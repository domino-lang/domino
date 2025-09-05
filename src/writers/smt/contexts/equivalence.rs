use crate::{
    gamehops::equivalence::EquivalenceContext,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            relation::Relation, relations::equal_aborts, theorem_consts::TheoremConstsPattern,
            GameStatePattern,
        },
    },
};

use super::{GameInstanceContext, GenericOracleContext, OracleContext};

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

    pub(crate) fn datastructure_theorem_consts_pattern(self) -> TheoremConstsPattern<'a> {
        let theorem_name = &self.theorem().name;

        TheoremConstsPattern { theorem_name }
    }
}
