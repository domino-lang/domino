// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    package::{Export, OracleSig},
    project::Project,
    theorem::{Claim, RandomnessType},
    writers::smt::contexts::EquivalenceContext,
};

use error::{Error, ExportSignatureMismatch, Result};

pub mod error;
mod smtrewrite;
mod verify_fn;

pub(crate) use verify_fn::EquivalenceSmtDriver;

// Equivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap
#[derive(Debug, Clone)]
pub struct Equivalence {
    // these two are game instance names
    pub(crate) left_name: String,
    pub(crate) right_name: String,
    pub(crate) invariants: Vec<(String, Vec<String>)>,
    pub(crate) trees: Vec<(String, Vec<Claim>)>,
    pub(crate) randomness: Vec<(String, RandomnessType)>,
}

impl Equivalence {
    pub fn new(
        left_name: String,
        right_name: String,
        mut invariants: Vec<(String, Vec<String>)>,
        mut trees: Vec<(String, Vec<Claim>)>,
        mut randomness: Vec<(String, RandomnessType)>,
    ) -> Self {
        trees.sort();
        invariants.sort();
        randomness.sort();

        Equivalence {
            left_name,
            right_name,
            invariants, // TODO INV
            trees,
            randomness,
        }
    }

    pub fn trees(&self) -> &[(String, Vec<Claim>)] {
        &self.trees
    }

    pub fn left_name(&self) -> &str {
        &self.left_name
    }

    pub fn right_name(&self) -> &str {
        &self.right_name
    }

    pub fn get_invariants(&self, offs: usize) -> Option<&[String]> {
        self.invariants
            .get(offs)
            .map(|(_name, invariants)| invariants.as_slice())
    }

    pub fn invariants_by_oracle_name(&self, oracle_name: &str) -> Vec<String> {
        self.invariants
            .iter()
            .find_map(|(oracle_name_, invariants)| {
                if oracle_name_.as_str() == oracle_name {
                    Some(invariants.clone())
                } else {
                    None
                }
            })
            .unwrap_or(vec![])
    }

    pub(crate) fn proof_tree_by_oracle_name(&self, oracle_name: &str) -> Vec<Claim> {
        self.trees
            .iter()
            .find(|(name, _tree)| name == oracle_name)
            .map(|(_oname, tree)| tree.clone())
            .unwrap_or_else(|| panic!("can't find proof tree for {oracle_name}"))
    }

    pub(crate) fn randomness_by_oracle_name(&self, oracle_name: &str) -> RandomnessType {
        self.randomness
            .iter()
            .find(|(name, _randomness)| name == oracle_name)
            .map(|(_oname, randomness)| randomness.clone())
            .unwrap_or_else(|| panic!("can't find randomness for {oracle_name}"))
    }
}

pub enum ClaimScope {
    InitialState,
    Oracle(String), // oracle name is stored
}

impl ClaimScope {
    pub fn name(&self) -> &str {
        match self {
            // the only equivalence wide claim we have at the moment
            ClaimScope::InitialState => "!INITIAL-STATE!",
            ClaimScope::Oracle(oracle_name) => oracle_name,
        }
    }
}

/// Checks that both game instances export the same oracles with the same signatures, and that the
/// equivalence declares a proof tree for exactly those oracles.
///
/// Oracles are identified by the name they are exported under, which is the alias if the export has
/// one, and the oracle name otherwise.
fn verify_exports_match(
    equivalence: &Equivalence,
    left_game_exports: &[Export],
    right_game_exports: &[Export],
) -> Result<()> {
    let left_game_inst_name = equivalence.left_name();
    let right_game_inst_name = equivalence.right_name();

    let left_exports: BTreeMap<&str, &OracleSig> = left_game_exports
        .iter()
        .map(|export| (export.name(), export.sig()))
        .collect();
    let right_exports: BTreeMap<&str, &OracleSig> = right_game_exports
        .iter()
        .map(|export| (export.name(), export.sig()))
        .collect();

    let only_left: Vec<String> = left_exports
        .keys()
        .filter(|name| !right_exports.contains_key(*name))
        .map(|name| (*name).to_string())
        .collect();
    let only_right: Vec<String> = right_exports
        .keys()
        .filter(|name| !left_exports.contains_key(*name))
        .map(|name| (*name).to_string())
        .collect();

    if !only_left.is_empty() || !only_right.is_empty() {
        return Err(Error::CompositionExportsMismatch {
            left_game_inst_name: left_game_inst_name.to_string(),
            right_game_inst_name: right_game_inst_name.to_string(),
            only_left,
            only_right,
        });
    }

    let mismatches: Vec<ExportSignatureMismatch> = left_exports
        .iter()
        .filter_map(|(name, left_sig)| {
            let right_sig = right_exports[name];
            if left_sig.types_match(right_sig) {
                return None;
            }

            Some(ExportSignatureMismatch {
                oracle_name: (*name).to_string(),
                left_sig: left_sig.to_oracle_type().to_string(),
                right_sig: right_sig.to_oracle_type().to_string(),
            })
        })
        .collect();

    if !mismatches.is_empty() {
        return Err(Error::CompositionExportSignatureMismatch {
            left_game_inst_name: left_game_inst_name.to_string(),
            right_game_inst_name: right_game_inst_name.to_string(),
            mismatches,
        });
    }

    let declared_oracles: BTreeSet<&str> = equivalence
        .trees()
        .iter()
        .map(|(oracle_name, _tree)| oracle_name.as_str())
        .collect();

    let missing_oracle_names: Vec<String> = left_exports
        .keys()
        .filter(|name| !declared_oracles.contains(*name))
        .map(|name| (*name).to_string())
        .collect();
    let unknown_oracle_names: Vec<String> = declared_oracles
        .iter()
        .filter(|name| !left_exports.contains_key(*name))
        .map(|name| (*name).to_string())
        .collect();

    if !missing_oracle_names.is_empty() || !unknown_oracle_names.is_empty() {
        return Err(Error::EquivalenceOraclesMismatch {
            left_game_inst_name: left_game_inst_name.to_string(),
            right_game_inst_name: right_game_inst_name.to_string(),
            missing_oracle_names,
            unknown_oracle_names,
        });
    }

    Ok(())
}

impl<'a> EquivalenceContext<'a> {
    fn verify_exports_match(&self) -> Result<()> {
        let equivalence = self.equivalence();

        let left_game_inst = self
            .theorem()
            .find_game_instance(equivalence.left_name())
            .unwrap();
        let right_game_inst = self
            .theorem()
            .find_game_instance(equivalence.right_name())
            .unwrap();

        verify_exports_match(
            equivalence,
            &left_game_inst.game().exports,
            &right_game_inst.game().exports,
        )
    }

    fn oracle_sequence(&self) -> Vec<&'a Export> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        log::debug!("oracle sequence: {:?}", game_inst.game().exports);

        game_inst.game().exports.iter().collect()
    }

    pub(crate) fn load_invariants(&mut self, project: &impl Project) -> Result<()> {
        for export in self.oracle_sequence() {
            let oracle_name = export.name();
            let mut out = Vec::new();
            //let mut linter = lint::Linter::new(self, oracle_name);

            for file_name in &self.equivalence().invariants_by_oracle_name(oracle_name) {
                log::info!("reading file {file_name}");
                let file_contents = project.read_input_file(file_name).map_err(|err| {
                    let file_name = file_name.clone();
                    error::new_invariant_file_read_error(oracle_name.to_string(), file_name, err)
                })?;
                log::info!("read file {file_name}");
                //linter.lint_file(file_name, &file_contents)?;
                out.append(&mut smtrewrite::rewrite(self, &file_contents)?);

                // log::info!("wrote contents of file {file_name}");

                // if comm.check_sat()? != SmtSolverResponse::Sat {
                //     return Err(Error::UnsatAfterInvariantRead {
                //         equivalence: self.equivalence.clone(),
                //         oracle_name: oracle_name.to_string(),
                //     });
                // }
            }
            self.append_invariants(oracle_name, out);
        }
        //linter.lint_finish()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Type;

    /// Builds an export of `oracle_name`, optionally exported under `alias`.
    fn export(oracle_name: &str, alias: Option<&str>, args: Vec<Type>, ty: Type) -> Export {
        let args = args
            .into_iter()
            .enumerate()
            .map(|(offs, ty)| (format!("arg{offs}"), ty))
            .collect();

        let sig = OracleSig {
            name: oracle_name.to_string(),
            args,
            ty,
        };

        Export::new(0, sig, alias.map(str::to_string))
    }

    /// Builds an oracle export named `oracle_name` with signature `(Integer) -> Integer`.
    fn simple_export(oracle_name: &str) -> Export {
        export(oracle_name, None, vec![Type::integer()], Type::integer())
    }

    /// Builds an equivalence of game instances `left` and `right` that declares a (empty) proof
    /// tree for each of `declared_oracle_names`.
    fn equivalence(declared_oracle_names: &[&str]) -> Equivalence {
        let trees = declared_oracle_names
            .iter()
            .map(|oracle_name| ((*oracle_name).to_string(), vec![]))
            .collect();

        Equivalence::new(
            "left".to_string(),
            "right".to_string(),
            vec![],
            trees,
            vec![],
        )
    }

    #[test]
    fn matching_exports_are_accepted() {
        let left = vec![simple_export("Eval"), simple_export("Get")];
        let right = vec![simple_export("Get"), simple_export("Eval")];

        verify_exports_match(&equivalence(&["Eval", "Get"]), &left, &right)
            .expect("exports match, so the check should pass");
    }

    #[test]
    fn exports_are_matched_by_alias() {
        // the left game exports Rand's `UsefulOracle` under the name `Eval`, which is the name the
        // right game exports directly.
        let left = vec![export(
            "UsefulOracle",
            Some("Eval"),
            vec![Type::integer()],
            Type::integer(),
        )];
        let right = vec![simple_export("Eval")];

        verify_exports_match(&equivalence(&["Eval"]), &left, &right)
            .expect("the alias matches the right export's name, so the check should pass");
    }

    #[test]
    fn export_matching_original_name_but_not_alias_is_rejected() {
        // the right game exports `UsefulOracle` under the alias `Eval`, so it does not export an
        // oracle named `UsefulOracle`, even though it has one.
        let left = vec![simple_export("UsefulOracle")];
        let right = vec![export(
            "UsefulOracle",
            Some("Eval"),
            vec![Type::integer()],
            Type::integer(),
        )];

        let err = verify_exports_match(&equivalence(&["UsefulOracle"]), &left, &right)
            .expect_err("the games export different names, so the check should fail");

        let Error::CompositionExportsMismatch {
            only_left,
            only_right,
            ..
        } = err
        else {
            panic!("expected a CompositionExportsMismatch, got {err}")
        };

        assert_eq!(only_left, vec!["UsefulOracle".to_string()]);
        assert_eq!(only_right, vec!["Eval".to_string()]);
    }

    #[test]
    fn differing_export_names_are_rejected() {
        let left = vec![simple_export("Eval"), simple_export("OnlyLeft")];
        let right = vec![simple_export("Eval"), simple_export("OnlyRight")];

        let err = verify_exports_match(
            &equivalence(&["Eval", "OnlyLeft", "OnlyRight"]),
            &left,
            &right,
        )
        .expect_err("the games export different names, so the check should fail");

        let Error::CompositionExportsMismatch {
            left_game_inst_name,
            right_game_inst_name,
            only_left,
            only_right,
        } = err
        else {
            panic!("expected a CompositionExportsMismatch, got {err}")
        };

        assert_eq!(left_game_inst_name, "left");
        assert_eq!(right_game_inst_name, "right");
        assert_eq!(only_left, vec!["OnlyLeft".to_string()]);
        assert_eq!(only_right, vec!["OnlyRight".to_string()]);
    }

    #[test]
    fn differing_argument_types_are_rejected() {
        let left = vec![export("Eval", None, vec![Type::integer()], Type::integer())];
        let right = vec![export("Eval", None, vec![Type::boolean()], Type::integer())];

        let err = verify_exports_match(&equivalence(&["Eval"]), &left, &right)
            .expect_err("the argument types differ, so the check should fail");

        let Error::CompositionExportSignatureMismatch { mismatches, .. } = err else {
            panic!("expected a CompositionExportSignatureMismatch, got {err}")
        };

        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].oracle_name, "Eval");
        assert_eq!(mismatches[0].left_sig, "oracle (Integer) -> Integer");
        assert_eq!(mismatches[0].right_sig, "oracle (Boolean) -> Integer");
    }

    #[test]
    fn differing_return_types_are_rejected() {
        let left = vec![export("Eval", None, vec![], Type::integer())];
        let right = vec![export("Eval", None, vec![], Type::boolean())];

        let err = verify_exports_match(&equivalence(&["Eval"]), &left, &right)
            .expect_err("the return types differ, so the check should fail");

        let Error::CompositionExportSignatureMismatch { mismatches, .. } = err else {
            panic!("expected a CompositionExportSignatureMismatch, got {err}")
        };

        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].oracle_name, "Eval");
        assert_eq!(mismatches[0].left_sig, "oracle () -> Integer");
        assert_eq!(mismatches[0].right_sig, "oracle () -> Boolean");
    }

    #[test]
    fn differing_argument_counts_are_rejected() {
        let left = vec![export(
            "Eval",
            None,
            vec![Type::integer(), Type::integer()],
            Type::integer(),
        )];
        let right = vec![simple_export("Eval")];

        let err = verify_exports_match(&equivalence(&["Eval"]), &left, &right)
            .expect_err("the argument counts differ, so the check should fail");

        assert!(
            matches!(err, Error::CompositionExportSignatureMismatch { .. }),
            "expected a CompositionExportSignatureMismatch, got {err}"
        );
    }

    #[test]
    fn signature_of_aliased_export_is_compared() {
        let left = vec![export(
            "UsefulOracle",
            Some("Eval"),
            vec![Type::integer()],
            Type::integer(),
        )];
        let right = vec![export("Eval", None, vec![Type::boolean()], Type::integer())];

        let err = verify_exports_match(&equivalence(&["Eval"]), &left, &right)
            .expect_err("the aliased export has a different signature, so the check should fail");

        let Error::CompositionExportSignatureMismatch { mismatches, .. } = err else {
            panic!("expected a CompositionExportSignatureMismatch, got {err}")
        };

        // the mismatch is reported under the name the oracle is exported as
        assert_eq!(mismatches[0].oracle_name, "Eval");
    }

    #[test]
    fn undeclared_and_unknown_equivalence_oracles_are_rejected() {
        let left = vec![simple_export("Eval"), simple_export("Get")];
        let right = vec![simple_export("Eval"), simple_export("Get")];

        // `Get` is exported but has no proof tree, and `NotExported` has a proof tree but is not
        // exported.
        let err = verify_exports_match(&equivalence(&["Eval", "NotExported"]), &left, &right)
            .expect_err("the declared oracles don't match the exports, so the check should fail");

        let Error::EquivalenceOraclesMismatch {
            missing_oracle_names,
            unknown_oracle_names,
            ..
        } = err
        else {
            panic!("expected an EquivalenceOraclesMismatch, got {err}")
        };

        assert_eq!(missing_oracle_names, vec!["Get".to_string()]);
        assert_eq!(unknown_oracle_names, vec!["NotExported".to_string()]);
    }

    #[test]
    fn equivalence_declaring_original_name_of_aliased_export_is_rejected() {
        let left = vec![export(
            "UsefulOracle",
            Some("Eval"),
            vec![Type::integer()],
            Type::integer(),
        )];
        let right = vec![simple_export("Eval")];

        let err = verify_exports_match(&equivalence(&["UsefulOracle"]), &left, &right)
            .expect_err("the equivalence declares the pre-alias name, so the check should fail");

        let Error::EquivalenceOraclesMismatch {
            missing_oracle_names,
            unknown_oracle_names,
            ..
        } = err
        else {
            panic!("expected an EquivalenceOraclesMismatch, got {err}")
        };

        assert_eq!(missing_oracle_names, vec!["Eval".to_string()]);
        assert_eq!(unknown_oracle_names, vec!["UsefulOracle".to_string()]);
    }
}
