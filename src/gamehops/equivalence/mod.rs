// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::iter::FromIterator;

use crate::identifier::theorem_ident::{TheoremConstIdentifier, TheoremIdentifier};
use crate::identifier::Identifier;
use crate::types::{CountSpec, TypeKind};
use crate::writers::smt::contexts::GameInstanceContext;
use crate::writers::smt::patterns::const_mapping::define_game_const_mapping_fun;
use crate::writers::smt::patterns::functions::const_mapping::define_pkg_const_mapping_fun;
use crate::writers::smt::patterns::oracle_args::OldNewOracleArgPattern as _;
use crate::writers::smt::patterns::{declare_datatype, FunctionPattern, GameStateDeclareInfo};
use crate::{
    package::{Export, OracleSig},
    theorem::{Claim, GameInstance, RandomnessType, Theorem},
    transforms::{
        samplify::SampleInfo, theorem_transforms::EquivalenceTransform, TheoremTransform,
    },
    types::Type,
    writers::smt::{
        contexts::{self, GenericOracleContext},
        exprs::{SmtAnd, SmtExpr, SmtIte},
        patterns::{self, DatastructurePattern},
        writer::CompositionSmtWriter,
    },
};

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

mod emit;
pub mod error;
mod lint;
mod smtrewrite;
mod verify_fn;

pub use verify_fn::{verify, verify_parallel};

#[derive(Clone, Copy)]
pub(crate) struct EquivalenceContext<'a> {
    equivalence: &'a Equivalence,
    theorem: &'a Theorem<'a>,
    auxs: &'a <EquivalenceTransform as TheoremTransform>::Aux,
}

// simple getters
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn theorem(&self) -> &'a Theorem<'a> {
        self.theorem
    }

    pub(crate) fn equivalence(&self) -> &'a Equivalence {
        self.equivalence
    }
}

// subcontexts
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn left_game_inst_ctx(self) -> contexts::GameInstanceContext<'a> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        contexts::GameInstanceContext::new(game_inst)
    }

    pub(crate) fn right_game_inst_ctx(self) -> contexts::GameInstanceContext<'a> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().right_name())
            .unwrap();

        contexts::GameInstanceContext::new(game_inst)
    }
}

impl<'a> EquivalenceContext<'a> {
    // fn split_oracle_sig_by_exported_name(
    //     &'a self,
    //     oracle_name: &str,
    // ) -> Option<&'a SplitOracleSig> {
    //     let gctx_left = self.left_game_inst_ctx();
    //
    //     gctx_left
    //         .game()
    //         .split_exports
    //         .iter()
    //         .find(|SplitExport(_, sig)| sig.name == oracle_name)
    //         .and_then(|SplitExport(inst_idx, _)| {
    //             gctx_left.game().pkgs[*inst_idx]
    //                 .pkg
    //                 .split_oracles
    //                 .iter()
    //                 .find(|odef| odef.sig.name == oracle_name)
    //                 .map(|odef| &odef.sig)
    //         })
    // }
    //
    // fn emit_split_claim_assert(
    //     &self,
    //     comm: &mut Communicator,
    //     oracle_name: &str,
    //     path: &SplitPath,
    //     claim: &Claim,
    // ) -> Result<()> {
    //     println!("name: {oracle_name}");
    //     println!("path: {path:?}");
    //
    //     let gctx_left = self.left_game_inst_ctx();
    //     let gctx_right = self.right_game_inst_ctx();
    //
    //     let game_inst_name_left = self.equivalence.left_name();
    //     let game_inst_name_right = self.equivalence.right_name();
    //
    //     let game_name_left = &gctx_left.game().name;
    //     let game_name_right = &gctx_right.game().name;
    //
    //     let game_params_left = &gctx_left.game_inst().consts;
    //     let game_params_right = &gctx_right.game_inst().consts;
    //
    //     let pkg_inst_ctx_left = gctx_left
    //         .pkg_inst_ctx_by_exported_split_oracle_name(oracle_name)
    //         .unwrap();
    //     let pkg_inst_ctx_right = gctx_right
    //         .pkg_inst_ctx_by_exported_split_oracle_name(oracle_name)
    //         .unwrap();
    //
    //     let pkg_inst_name_left = pkg_inst_ctx_left.pkg_inst_name();
    //     let pkg_inst_name_right = pkg_inst_ctx_right.pkg_inst_name();
    //
    //     let pkg_name_left = pkg_inst_ctx_left.pkg_name();
    //     let pkg_name_right = pkg_inst_ctx_right.pkg_name();
    //
    //     let pkg_params_left = &pkg_inst_ctx_left.pkg_inst().params;
    //     let pkg_params_right = &pkg_inst_ctx_right.pkg_inst().params;
    //
    //     let args: Vec<_> = self
    //         .split_oracle_sig_by_exported_name(oracle_name)
    //         .unwrap()
    //         .args
    //         .iter()
    //         .map(|(arg_name, arg_type)| patterns::OracleArgs {
    //             oracle_name,
    //             arg_name,
    //             arg_type,
    //         })
    //         .collect();
    //
    //     // find the package instance which is marked as exporting
    //     // the oracle of this name, both left and right.
    //     let left_partial_return_name = patterns::PartialReturnConst {
    //         game_name: game_name_left,
    //         game_params: game_params_left,
    //         pkg_name: pkg_name_left,
    //         pkg_params: pkg_params_left,
    //         game_inst_name: game_inst_name_left,
    //         pkg_inst_name: pkg_inst_name_left,
    //         oracle_name,
    //     }
    //     .name();
    //
    //     let right_partial_return_name = patterns::PartialReturnConst {
    //         game_name: game_name_right,
    //         game_params: game_params_right,
    //         game_inst_name: game_inst_name_right,
    //         pkg_name: pkg_name_right,
    //         pkg_params: pkg_params_right,
    //         pkg_inst_name: pkg_inst_name_right,
    //         oracle_name,
    //     }
    //     .name();
    //
    //     let state_left = gctx_left.oracle_arg_game_state_pattern();
    //     let state_right = gctx_right.oracle_arg_game_state_pattern();
    //
    //     let state_left_new_name =
    //         state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string());
    //     let state_left_old_name = state_left.old_global_const_name(game_inst_name_left);
    //
    //     let state_right_new_name =
    //         state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string());
    //     let state_right_old_name = state_right.old_global_const_name(game_inst_name_right);
    //
    //     let intermediate_state_left_new_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_left,
    //         pkg_inst_name: pkg_inst_name_left,
    //         pkg_name: pkg_name_left,
    //         pkg_params: pkg_params_left,
    //         oracle_name,
    //         variant: &format!("new-{oracle_name}"),
    //     }
    //     .name();
    //
    //     let intermediate_state_left_old_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_left,
    //         pkg_inst_name: pkg_inst_name_left,
    //         pkg_name: pkg_name_left,
    //         pkg_params: pkg_params_left,
    //         oracle_name,
    //         variant: "old",
    //     }
    //     .name();
    //
    //     let intermediate_state_right_new_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_right,
    //         pkg_inst_name: pkg_inst_name_right,
    //         pkg_name: pkg_name_right,
    //         pkg_params: pkg_params_right,
    //         oracle_name,
    //         variant: &format!("new-{oracle_name}"),
    //     }
    //     .name();
    //
    //     let intermediate_state_right_old_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_right,
    //         pkg_inst_name: pkg_inst_name_right,
    //         pkg_name: pkg_name_right,
    //         pkg_params: pkg_params_right,
    //         oracle_name,
    //         variant: "old",
    //     }
    //     .name();
    //
    //     let randomness_mapping = SmtForall {
    //         bindings: vec![
    //             ("randmap-sample-id-left".into(), Type::Integer.into()),
    //             ("randmap-sample-ctr-left".into(), Type::Integer.into()),
    //             ("randmap-sample-id-right".into(), Type::Integer.into()),
    //             ("randmap-sample-ctr-right".into(), Type::Integer.into()),
    //         ],
    //         body: (
    //             "=>",
    //             (
    //                 format!("randomness-mapping-{oracle_name}"),
    //                 (
    //                     format!("get-rand-ctr-{game_inst_name_left}"),
    //                     "randmap-sample-id-left",
    //                 ),
    //                 (
    //                     format!("get-rand-ctr-{game_inst_name_right}"),
    //                     "randmap-sample-id-right",
    //                 ),
    //                 "randmap-sample-id-left",
    //                 "randmap-sample-id-right",
    //                 "randmap-sample-ctr-left",
    //                 "randmap-sample-ctr-right",
    //             ),
    //             (
    //                 "rand-is-eq",
    //                 "randmap-sample-id-left",
    //                 "randmap-sample-id-right",
    //                 "randmap-sample-ctr-left",
    //                 "randmap-sample-ctr-right",
    //             ),
    //         ),
    //     };
    //
    //     // this helper builds an smt expression that calls the
    //     // function with the given name with the old states,
    //     // return values and the respective arguments.
    //     // We expect that function to return a boolean, which makes
    //     // it a relation.
    //     let build_lemma_call = |name: &str| {
    //         let mut tmp: Vec<SmtExpr> = vec![
    //             name.into(),
    //             state_left_old_name.clone().into(),
    //             state_right_old_name.clone().into(),
    //             intermediate_state_left_old_name.clone().into(),
    //             intermediate_state_right_old_name.clone().into(),
    //             left_partial_return_name.clone().into(),
    //             right_partial_return_name.clone().into(),
    //         ];
    //
    //         for arg in args {
    //             tmp.push(arg.name().into());
    //         }
    //
    //         SmtExpr::List(tmp)
    //     };
    //
    //     let build_relation_call = |name: &str| -> SmtExpr {
    //         (
    //             name,
    //             &state_left_new_name,
    //             &state_right_new_name,
    //             &intermediate_state_left_new_name,
    //             &intermediate_state_right_new_name,
    //         )
    //             .into()
    //     };
    //
    //     let build_invariant_old_call = |name: &str| -> SmtExpr {
    //         (
    //             name,
    //             &state_left_old_name,
    //             &state_right_old_name,
    //             &intermediate_state_left_old_name,
    //             &intermediate_state_right_old_name,
    //         )
    //             .into()
    //     };
    //
    //     let build_invariant_new_call = |name: &str| -> SmtExpr {
    //         (
    //             name,
    //             &state_left_new_name,
    //             &state_right_new_name,
    //             &intermediate_state_left_new_name,
    //             &intermediate_state_right_new_name,
    //         )
    //             .into()
    //     };
    //
    //     let dep_calls: Vec<_> = claim
    //         .dependencies()
    //         .iter()
    //         .map(|dep_name| {
    //             let claim_type = ClaimType::guess_from_name(dep_name);
    //             match claim_type {
    //                 ClaimType::Lemma => build_lemma_call.clone()(dep_name),
    //                 ClaimType::Relation => build_relation_call(dep_name),
    //                 ClaimType::Invariant => unreachable!(),
    //             }
    //         })
    //         .collect();
    //
    //     let postcond_call = match claim.ty {
    //         ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
    //         ClaimType::Relation => build_relation_call(&claim.name),
    //         ClaimType::Invariant => build_invariant_new_call(&claim.name),
    //     };
    //
    //     let mut dependencies_code: Vec<SmtExpr> = vec![
    //         randomness_mapping.into(),
    //         build_invariant_old_call("invariant"),
    //     ];
    //
    //     for dep in dep_calls {
    //         dependencies_code.push(dep)
    //     }
    //
    //     comm.write_smt(crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
    //         SmtAnd(dependencies_code),
    //         postcond_call,
    //     ))))?;
    //
    //     Ok(())
    // }

    fn oracle_sig_by_exported_name(&'a self, oracle_name: &str) -> Option<&'a OracleSig> {
        let gctx_left = self.left_game_inst_ctx();

        gctx_left
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .and_then(|export| {
                gctx_left.game().pkgs[export.to()]
                    .pkg
                    .oracles
                    .iter()
                    .find(|odef| odef.sig.name == export.sig().name)
                    .map(|odef| &odef.sig)
            })
    }

    fn types(&self) -> Vec<Type> {
        let (_, (types_left, _)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().left_name())
            .unwrap();
        let (_, (types_right, _)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().right_name())
            .unwrap();
        let types_theorem: HashSet<Type> = self
            .theorem()
            .consts
            .iter()
            .filter_map(|(name, ty)| match ty.kind() {
                TypeKind::Integer => {
                    let id = TheoremConstIdentifier {
                        theorem_name: self.theorem().name.clone(),
                        name: name.clone(),
                        ty: Type::integer(),
                        inst_info: None,
                    };

                    Some(Type::bits(CountSpec::Identifier(Box::new(
                        Identifier::TheoremIdentifier(TheoremIdentifier::Const(id)),
                    ))))
                }
                _ => None,
            })
            .collect();

        let mut types: Vec<_> = types_left
            .union(types_right)
            .cloned()
            .collect::<HashSet<_>>()
            .union(&types_theorem)
            .cloned()
            .collect();
        types.sort();
        types
    }

    fn sample_info_left(self) -> &'a SampleInfo {
        let (_, (_, sample_info)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().left_name())
            .unwrap();
        sample_info
    }

    fn sample_info_right(self) -> &'a SampleInfo {
        let (_, (_, sample_info)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().right_name())
            .unwrap();
        sample_info
    }

    // fn split_info_left(&self) -> &'a Vec<SplitInfoEntry> {
    //     let aux_resolver = SliceResolver(self.auxs);
    //     let (_, (_, _, split_info)) = aux_resolver
    //         .resolve_value(self.equivalence.left_name())
    //         .unwrap();
    //     split_info
    // }
    //
    // fn split_info_right(&self) -> &'a Vec<SplitInfoEntry> {
    //     let aux_resolver = SliceResolver(self.auxs);
    //     let (_, (_, _, split_info)) = aux_resolver
    //         .resolve_value(self.equivalence.right_name())
    //         .unwrap();
    //     split_info
    // }

    fn verify_exports_match(&self) -> (Vec<OracleSig>, Vec<OracleSig>) {
        let left_game_inst = self
            .theorem
            .find_game_instance(self.equivalence().left_name())
            .unwrap();
        let right_game_inst = self
            .theorem
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
            .theorem
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        log::debug!("oracle sequence: {:?}", game_inst.game().exports);

        game_inst.game().exports.iter().collect()
    }

    // fn split_oracle_sequence(&self) -> Vec<&'a SplitOracleSig> {
    //     let game_inst = SliceResolver(self.theorem.instances())
    //         .resolve_value(self.equivalence.left_name())
    //         .unwrap();
    //
    //     println!("oracle sequence: {:?}", game_inst.game().exports);
    //
    //     game_inst
    //         .game()
    //         .split_exports
    //         .iter()
    //         .map(|SplitExport(_, split_oracle_sig)| split_oracle_sig)
    //         .collect()
    // }

    /// Returns an iterator of all the package const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_const_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(|ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .flat_map(|gctx| gctx.pkg_inst_contexts())
            .map(|pctx| {
                let pattern = pctx.datastructure_pkg_consts_pattern();
                let spec = pattern.datastructure_spec(pctx.pkg());

                (pattern, spec)
            })
            .filter_map(move |(pattern, spec)| {
                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator of all the package state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_state_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(|ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .flat_map(|gctx| gctx.pkg_inst_contexts())
            .filter_map(move |pctx| {
                let pattern = pctx.pkg_state_pattern();
                let spec = pattern.datastructure_spec(pctx.pkg());

                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator of all the package state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_return_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(|ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .flat_map(|gctx| gctx.pkg_inst_contexts())
            .flat_map(|pctx| pctx.oracle_contexts())
            .filter_map(move |octx| {
                let pattern = octx.return_pattern();
                let spec = pattern.datastructure_spec(&octx.oracle_sig().ty);

                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator of all the game state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_game_state_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![
                    (ectx.left_game_inst_ctx(), self.sample_info_left()),
                    (ectx.right_game_inst_ctx(), self.sample_info_right()),
                ]
                .into_iter()
            })
            .filter_map(move |(gctx, sample_info)| {
                let declare_info = GameStateDeclareInfo {
                    game_inst: gctx.game_inst(),
                    sample_info,
                };

                let pattern = gctx.datastructure_game_state_pattern();
                let spec = pattern.datastructure_spec(&declare_info);

                if already_defined.insert(pattern.sort_name()) {
                    let datatype = declare_datatype(&pattern, &spec);
                    Some(datatype)
                } else {
                    None
                }
            })
    }

    /// Returns an iterator cntaining the theorem const datatype.
    pub(crate) fn smt_theorem_const_definition(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let pattern = self.datastructure_theorem_consts_pattern();
        let spec = pattern.datastructure_spec(self.theorem());

        Some(declare_datatype(&pattern, &spec)).into_iter()
    }

    /// Returns an iterator of all the game const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_game_const_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .filter_map(move |gctx| {
                let pattern = gctx.datastructure_game_consts_pattern();
                let spec = pattern.datastructure_spec(gctx.game());

                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator over the functions that map the constant values of the theorem to that of a
    /// game instance. Ranges over all game instances.
    pub(crate) fn smt_theorem_game_const_mapping_definitions(
        self,
    ) -> impl Iterator<Item = SmtExpr> + 'a {
        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![
                    ectx.left_game_inst_ctx().game_inst(),
                    ectx.right_game_inst_ctx().game_inst(),
                ]
                .into_iter()
            })
            .flat_map(move |game_inst| {
                define_game_const_mapping_fun(self.theorem(), game_inst.game(), game_inst.name())
                    .map(SmtExpr::from)
            })
    }

    /// Returns an iterator over the functions that map the constant values of a game to that of a
    /// package instance. Ranges over all package instances in all games.
    pub(crate) fn smt_game_pkg_const_mapping_definitions(
        self,
    ) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut seen_game_names: HashSet<&str> = Default::default();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .filter(move |gctx| seen_game_names.insert(gctx.game_name()))
            .flat_map(|gctx| {
                gctx.game().pkgs.iter().flat_map(move |pkg_inst| {
                    define_pkg_const_mapping_fun(gctx.game(), &pkg_inst.pkg, &pkg_inst.name)
                        .map(SmtExpr::from)
                })
            })
    }

    pub(crate) fn smt_oracle_function_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                let left_gctx = ectx.left_game_inst_ctx();
                let right_gctx = ectx.right_game_inst_ctx();

                vec![
                    (left_gctx, ectx.sample_info_left()),
                    (right_gctx, ectx.sample_info_right()),
                ]
                .into_iter()
            })
            .flat_map(|(gctx, sample_info)| {
                gctx.pkg_inst_contexts()
                    .map(move |pctx| (pctx, sample_info))
            })
            .flat_map(|(pctx, sample_info)| {
                pctx.oracle_contexts().map(move |octx| (octx, sample_info))
            })
            .filter_map(move |(octx, sample_info)| {
                let gctx = octx.game_inst_ctx();
                let pctx = octx.pkg_inst_ctx();
                let pattern = octx.oracle_pattern();

                let game_inst = gctx.game_inst();

                let writer = CompositionSmtWriter::new(game_inst, sample_info);

                if already_defined.insert(pattern.function_name()) {
                    let fundef =
                        writer.smt_define_nonsplit_oracle_fn(pctx.pkg_inst(), octx.oracle_def());
                    Some(fundef)
                } else {
                    None
                }
            })
    }

    pub fn smt_define_randctr_function(
        &self,
        game_inst: &GameInstance,
        sample_info: &SampleInfo,
    ) -> SmtExpr {
        let gctx = GameInstanceContext::new(game_inst);
        let game = game_inst.game();
        let game_inst_name = game_inst.name();
        let game_name = &game.name;
        let params = &game_inst.consts;

        let state_name = gctx
            .oracle_arg_game_state_pattern()
            .old_global_const_name(game_inst_name);

        let pattern = patterns::GameStatePattern { game_name, params };
        let info = patterns::GameStateDeclareInfo {
            game_inst,
            sample_info,
        };

        let spec = pattern.datastructure_spec(&info);
        let (_, selectors) = &spec.0[0];

        let mut body = SmtExpr::Atom("0".to_string());

        for selector in selectors {
            body = match selector {
                patterns::GameStateSelector::Randomness { sample_pos } => SmtIte {
                    cond: ("=", "sampleid", sample_pos.as_ref()),
                    then: (pattern.selector_name(selector), state_name.clone()),
                    els: body,
                }
                .into(),
                _ => body,
            };
        }

        (
            "define-fun",
            format!("get-rand-ctr-{game_inst_name}"),
            (("sampleid", "SampleId"),),
            "Int",
            body,
        )
            .into()
    }

    pub fn smt_define_randeq_function(&self) -> SmtExpr {
        let left_game_inst = self.left_game_inst_ctx().game_inst();
        let right_game_inst = self.right_game_inst_ctx().game_inst();

        let left_game_inst_name = &left_game_inst.name;
        let right_game_inst_name = &right_game_inst.name;

        /*
         *
         *
         * (= (randfn_left left-id left-ctr) (randfn-right right-id right-ctr)))
         *
         * if ( = left-id 3) (randfn-Int id ctr) else if ( )
         *
         *
         * if (or [cases left is type A and right is type A]) (= (fn left id ctr) fn right id ctr)
         *
         */

        fn type_use_theorem_ident(ty: Type) -> Type {
            match ty.into_kind() {
                TypeKind::Bits(mut count_spec) => {
                    if let CountSpec::Identifier(identifier) = &mut count_spec {
                        let theorem_ident = identifier.as_theorem_identifier();
                        assert!(
                            theorem_ident.is_some(),
                            "expected {identifier:?} to be completely resolved"
                        );
                        **identifier =
                            Identifier::TheoremIdentifier(theorem_ident.cloned().unwrap());
                    }
                    Type::bits(count_spec)
                }
                kind => Type::from_kind(kind),
            }
        }

        let left_positions = &self.sample_info_left().positions;
        let right_positions = &self.sample_info_right().positions;

        let left_types: BTreeSet<Type> = BTreeSet::from_iter(
            self.sample_info_left()
                .tys
                .iter()
                .cloned()
                .map(type_use_theorem_ident),
        );
        let right_types: BTreeSet<Type> = BTreeSet::from_iter(
            self.sample_info_right()
                .tys
                .iter()
                .cloned()
                .map(type_use_theorem_ident),
        );

        let types: Vec<&Type> = left_types.intersection(&right_types).collect();

        let mut left_positions_by_type: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut right_positions_by_type: BTreeMap<_, Vec<_>> = BTreeMap::new();

        for pos in left_positions {
            let pos_ty = pos.ty.clone();
            let pos_theorem_ty = type_use_theorem_ident(pos_ty);
            left_positions_by_type
                .entry(pos_theorem_ty)
                .or_default()
                .push(pos);
        }

        for pos in right_positions {
            let pos_ty = pos.ty.clone();
            let pos_theorem_ty = type_use_theorem_ident(pos_ty);
            right_positions_by_type
                .entry(pos_theorem_ty)
                .or_default()
                .push(pos);
        }

        let mut body: SmtExpr = true.into();

        for ty in types {
            let sort: SmtExpr = ty.into();

            let left_has_type = left_positions_by_type
                .get(ty)
                .expect("expected that left sample info has positions for type {ty:?}")
                .iter()
                .map(|sample_pos| ("=", *sample_pos, "sample-id-left").into());
            let mut left_or_case: Vec<SmtExpr> = vec!["or".into()];
            left_or_case.extend(left_has_type);

            let right_has_type = right_positions_by_type
                .get(ty)
                .expect("expected that right sample info has positions for type {ty:?}")
                .iter()
                .map(|sample_pos| ("=", *sample_pos, "sample-id-right").into());

            let mut right_or_case: Vec<SmtExpr> = vec!["or".into()];
            right_or_case.extend(right_has_type);

            body = SmtIte {
                cond: SmtAnd(vec![
                    SmtExpr::List(left_or_case),
                    SmtExpr::List(right_or_case),
                ]),
                then: (
                    "=",
                    (
                        format!("__sample-rand-{left_game_inst_name}-{sort}"),
                        "sample-id-left",
                        "sample-ctr-left",
                    ),
                    (
                        format!("__sample-rand-{right_game_inst_name}-{sort}"),
                        "sample-id-right",
                        "sample-ctr-right",
                    ),
                ),
                els: body,
            }
            .into()
        }

        (
            "define-fun",
            "rand-is-eq",
            (
                ("sample-id-left", "SampleId"),
                ("sample-id-right", "SampleId"),
                ("sample-ctr-left", Type::integer()),
                ("sample-ctr-right", Type::integer()),
            ),
            "Bool",
            body,
        )
            .into()
    }
}

// ResolvedEquivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap
