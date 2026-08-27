// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{HashMap, HashSet};

mod emit;

use crate::{
    gamehops::equivalence::Equivalence,
    identifier::{
        theorem_ident::{TheoremConstIdentifier, TheoremIdentifier},
        Identifier,
    },
    package::OracleSig,
    theorem::Theorem,
    transforms::{
        samplify::SampleInfo, theorem_transforms::EquivalenceTransform, TheoremTransform,
    },
    types::{CountSpec, Type, TypeKind},
    writers::smt::{
        contexts,
        exprs::SmtExpr,
        patterns::{
            relation::Relation, relations::equal_aborts, theorem_consts::TheoremConstsPattern,
            GameStatePattern,
        },
    },
};

use super::{GameInstanceContext, GenericOracleContext, OracleContext};

#[derive(Clone)]
pub struct EquivalenceContext<'a> {
    equivalence: &'a Equivalence,
    theorem: &'a Theorem<'a>,
    auxs: &'a <EquivalenceTransform as TheoremTransform>::Aux,
    invariants: HashMap<String, Vec<SmtExpr>>,
}

// simple getters
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn new(
        equivalence: &'a Equivalence,
        theorem: &'a Theorem<'a>,
        auxs: &'a <EquivalenceTransform as TheoremTransform>::Aux,
    ) -> Self {
        Self {
            equivalence,
            theorem,
            auxs,
            invariants: HashMap::new(),
        }
    }

    pub(crate) fn theorem(&self) -> &'a Theorem<'a> {
        self.theorem
    }

    pub(crate) fn equivalence(&self) -> &'a Equivalence {
        self.equivalence
    }

    pub(crate) fn append_invariants(
        &mut self,
        oracle_name: &str,
        mut new_invariants: Vec<SmtExpr>,
    ) {
        if let Some(current) = self.invariants.get_mut(oracle_name) {
            current.append(&mut new_invariants);
        } else {
            self.invariants
                .insert(oracle_name.to_string(), new_invariants);
        }
    }
}

// subcontexts
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn left_game_inst_ctx(&self) -> contexts::GameInstanceContext<'a> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        contexts::GameInstanceContext::new(game_inst)
    }

    pub(crate) fn right_game_inst_ctx(&self) -> contexts::GameInstanceContext<'a> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().right_name())
            .unwrap();

        contexts::GameInstanceContext::new(game_inst)
    }
}

// patterns
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn relation_pattern(
        &'a self,
        relation_name: &'a str,
        oracle_name: &'a str,
    ) -> Relation<'a> {
        let left_gctx: GameInstanceContext<'a> = self.left_game_inst_ctx();
        let right_gctx: GameInstanceContext<'a> = self.right_game_inst_ctx();

        let state_datatype_left: GameStatePattern<'a> =
            left_gctx.datastructure_game_state_pattern();
        let state_datatype_right: GameStatePattern<'a> =
            right_gctx.datastructure_game_state_pattern();

        let left_octx: OracleContext<'a> =
            left_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let right_octx = right_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();

        let return_datatype_left = left_octx.return_pattern();
        let return_datatype_right = right_octx.return_pattern();

        let args: &'a [_] = left_octx.oracle_args();
        let return_type = left_octx.oracle_return_type();

        Relation {
            game_inst_name_left: left_gctx.game_inst_name(),
            game_inst_name_right: right_gctx.game_inst_name(),
            relation_name,
            oracle_name,
            state_datatype_left,
            state_datatype_right,
            return_datatype_left,
            return_datatype_right,
            args,
            return_type,
        }
    }

    pub(crate) fn relation_definition_equal_aborts(
        &self,
        oracle_name: &str,
    ) -> equal_aborts::RelationFunction {
        self.relation_pattern("equal-aborts", oracle_name)
            .build_equal_aborts()
    }

    pub(crate) fn relation_definition_left_no_abort(
        &self,
        oracle_name: &str,
    ) -> impl Into<SmtExpr> {
        self.relation_pattern("left-no-abort", oracle_name)
            .build_left_no_abort()
    }

    pub(crate) fn relation_definition_right_no_abort(
        &self,
        oracle_name: &str,
    ) -> impl Into<SmtExpr> {
        self.relation_pattern("right-no-abort", oracle_name)
            .build_right_no_abort()
    }

    pub(crate) fn relation_definition_no_abort(&self, oracle_name: &str) -> impl Into<SmtExpr> {
        self.relation_pattern("no-abort", oracle_name)
            .build_no_abort()
    }

    pub(crate) fn relation_definition_same_output(&self, oracle_name: &str) -> impl Into<SmtExpr> {
        self.relation_pattern("same-output", oracle_name)
            .build_same_output()
    }

    pub(crate) fn datastructure_theorem_consts_pattern(&'a self) -> TheoremConstsPattern<'a> {
        let theorem_name = &self.theorem().name;

        TheoremConstsPattern { theorem_name }
    }
}

impl<'a> EquivalenceContext<'a> {
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

    pub(crate) fn sample_info_left(&self) -> &'a SampleInfo {
        let (_, (_, sample_info)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().left_name())
            .unwrap();
        sample_info
    }

    pub(crate) fn sample_info_right(&self) -> &'a SampleInfo {
        let (_, (_, sample_info)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().right_name())
            .unwrap();
        sample_info
    }

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
}
