// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

use crate::{
    package::{Export, OracleSig},
    project::Project,
    theorem::{Claim, RandomnessType},
    writers::smt::contexts::EquivalenceContext,
};

use error::Result;

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

pub mod error;
mod smtrewrite;
mod verify_fn;

pub use verify_fn::{verify, verify_parallel};

impl<'a> EquivalenceContext<'a> {
    fn verify_exports_match(&self) -> (Vec<OracleSig>, Vec<OracleSig>) {
        let left_game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().left_name())
            .unwrap();
        let right_game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().right_name())
            .unwrap();

        let left_exports: HashSet<_> = left_game_inst
            .game()
            .exports
            .iter()
            .map(|export| export.sig().clone())
            .collect();
        let right_exports: HashSet<_> = right_game_inst
            .game()
            .exports
            .iter()
            .map(|export| export.sig().clone())
            .collect();

        let only_left: Vec<_> = left_exports
            .iter()
            .filter(|sig| {
                right_exports
                    .iter()
                    .all(|right_sig| sig.name != right_sig.name || !sig.types_match(right_sig))
            })
            .cloned()
            .collect();
        let only_right: Vec<_> = right_exports
            .iter()
            .filter(|sig| {
                left_exports
                    .iter()
                    .all(|left_sig| sig.name != left_sig.name || !sig.types_match(left_sig))
            })
            .cloned()
            .collect();

        (only_left, only_right)
    }

    fn oracle_sequence(&self) -> Vec<&'a Export> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        log::debug!("oracle sequence: {:?}", game_inst.game().exports);

        game_inst.game().exports.iter().collect()
    }

    fn load_invariants(&mut self, project: &impl Project) -> Result<()> {
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
