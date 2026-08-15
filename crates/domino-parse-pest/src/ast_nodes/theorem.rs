use domino_ast::ast_nodes::{
    identifier::{
        AssumptionIdentifier, GameInstanceIdentifier, LemmaIdentifier, OracleCompositionIdentifier,
        PackageInstanceIdentifier, TheoremIdentifier,
    },
    theorem::*,
    Trivia,
};

use crate::{
    ast_nodes::{common, expressions, instances},
    ListItem, Parsable, Rule,
};

expressions::impl_expr!(PureTheoremExpressionKind);

impl ListItem for InstanceConstAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_const_assignment_list;
}

impl ListItem for InstanceTypeAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_type_assignment_list;
}

impl ListItem for InstanceItem {
    const LIST_RULE: Rule = Rule::inst_list;
}

// paths for smt files

impl ListItem for Path {
    const LIST_RULE: Rule = Rule::path_list;
}

impl ListItem for SmtIdentifier {
    const LIST_RULE: Rule = Rule::smt_identifier_list;
}

impl ListItem for LemmaItem {
    const LIST_RULE: Rule = Rule::lemma_items;
}

impl ListItem for EquivalenceOracleItem {
    const LIST_RULE: Rule = Rule::eqv_oracle_block_list;
}

impl ListItem for EquivalenceOracleBlock {
    const LIST_RULE: Rule = Rule::eqv_oracle_blocks;
}

impl ListItem for AssumptionsItem {
    const LIST_RULE: Rule = Rule::assumptions_items;
}

impl ListItem for ReductionMapItem {
    const LIST_RULE: Rule = Rule::red_map_items;
}

impl ListItem for ReductionItem {
    const LIST_RULE: Rule = Rule::red_items;
}

impl ListItem for GameHopItem {
    const LIST_RULE: Rule = Rule::gamehop_items;
}

impl ListItem for TheoremItem {
    const LIST_RULE: Rule = Rule::theorem_item_list;
}

impl Parsable for InstanceConstAssignmentItem {
    const RULE: Rule = Rule::inst_const_assignment_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        instances::parse_instance_const_assignment_item(file_id, state, pair)
    }
}

impl Parsable for InstanceConstBlock {
    const RULE: Rule = Rule::inst_const_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_consts = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let list_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let list = InstanceConstAssignmentList::parse_ref(file_id, state, list_pair);

        Self { trivia, list }
    }
}

impl Parsable for InstanceTypeAssignmentItem {
    const RULE: Rule = Rule::inst_type_assignment_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        instances::parse_instance_type_assignment_item(file_id, state, pair)
    }
}

impl Parsable for InstanceTypeBlock {
    const RULE: Rule = Rule::inst_type_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_consts = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let list_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let list = InstanceTypeAssignmentList::parse_ref(file_id, state, list_pair);

        Self { trivia, list }
    }
}
impl Parsable for InstanceItem {
    const RULE: Rule = Rule::inst_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::inst_const_block => {
                InstanceItem::InstanceConst(InstanceConstBlock::parse_ref(file_id, state, inner))
            }
            Rule::inst_type_block => {
                InstanceItem::InstanceType(InstanceTypeBlock::parse_ref(file_id, state, inner))
            }
            _ => unreachable!(),
        }
    }
}

impl Parsable for InstanceBlock {
    const RULE: Rule = Rule::inst_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        instances::parse_instance_block(file_id, state, pair)
    }
}

impl Parsable for Path {
    const RULE: Rule = Rule::path;

    fn parse_inner(
        _file_id: domino_ast::source::FileId,
        _state: &mut crate::State,
        _pair: crate::Pair,
    ) -> Self {
        Path
    }
}

impl Parsable for InvariantSpec {
    const RULE: Rule = Rule::invariant_spec;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_open_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let paths = PathList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            pre_colon_trivia,
            pre_open_trivia,
            paths,
        }
    }
}

impl Parsable for SmtIdentifier {
    const RULE: Rule = Rule::smt_identifier;

    fn parse_inner(
        _file_id: domino_ast::source::FileId,
        _state: &mut crate::State,
        _pair: crate::Pair,
    ) -> Self {
        SmtIdentifier
    }
}

impl Parsable for LemmaItem {
    const RULE: Rule = Rule::lemma_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let name = LemmaIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_open_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let dependencies = SmtIdentifierList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            pre_colon_trivia,
            pre_open_trivia,
            dependencies,
        }
    }
}

impl Parsable for LemmaBlock {
    const RULE: Rule = Rule::lemmas_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = LemmaItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for EquivalenceOracleItem {
    const RULE: Rule = Rule::eqv_oracle_block_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::invariant_spec => {
                Self::InvariantSpec(InvariantSpec::parse_ref(file_id, state, inner))
            }
            Rule::lemmas_block => Self::LemmaBlock(LemmaBlock::parse_ref(file_id, state, inner)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for EquivalenceOracleBlock {
    const RULE: Rule = Rule::eqv_oracle_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let name = OracleCompositionIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = EquivalenceOracleItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            pre_colon_trivia,
            pre_brace_trivia,
            items,
        }
    }
}

impl Parsable for Equivalence {
    const RULE: Rule = Rule::equivalence;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let kw_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let left_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let left_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let right_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let blocks = EquivalenceOracleBlockList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            kw_trivia,
            left_name,
            left_trivia,
            right_name,
            right_trivia,
            blocks,
        }
    }
}

impl Parsable for Bound {
    const RULE: Rule = Rule::bound;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let lhs = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_tilde_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let post_tilde_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let rhs = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            lhs,
            pre_tilde_trivia,
            post_tilde_trivia,
            rhs,
        }
    }
}

impl Parsable for AssumptionsItem {
    const RULE: Rule = Rule::assumptions_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let name = AssumptionIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let bound = Bound::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            pre_colon_trivia,
            pre_brace_trivia,
            bound,
        }
    }
}

impl Parsable for AssumptionsBlock {
    const RULE: Rule = Rule::assumptions_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = AssumptionsItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for Conjecture {
    const RULE: Rule = Rule::conjecture;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let left_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let left_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let right_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            left_trivia,
            left_name,
            right_trivia,
            right_name,
        }
    }
}

impl Parsable for ReductionAssumptionLine {
    const RULE: Rule = Rule::red_assumption_line;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_assumption = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let name = AssumptionIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, name }
    }
}

impl Parsable for ReductionMapItem {
    const RULE: Rule = Rule::red_map_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let left_name = PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_name =
            PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            left_name,
            colon_trivia,
            right_trivia,
            right_name,
        }
    }
}

impl Parsable for ReductionMap {
    const RULE: Rule = Rule::red_map;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw = inner.next().unwrap();

        Self {
            assumption_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            assumption_name: GameInstanceIdentifier::parse_ref(
                file_id,
                state,
                inner.next().unwrap(),
            ),
            construction_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            construction_name: GameInstanceIdentifier::parse_ref(
                file_id,
                state,
                inner.next().unwrap(),
            ),
            items_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            items: ReductionMapItemList::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for ReductionItem {
    const RULE: Rule = Rule::red_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::red_assumption_line => {
                Self::AssumptionLine(ReductionAssumptionLine::parse_ref(file_id, state, inner))
            }
            Rule::red_map => Self::Map(ReductionMap::parse_ref(file_id, state, inner)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for Reduction {
    const RULE: Rule = Rule::reduction;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw = inner.next().unwrap();

        Self {
            left_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            left_name: GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap()),
            right_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            right_name: GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap()),
            items_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            items: ReductionItemList::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for GameHopItem {
    const RULE: Rule = Rule::gamehop_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::reduction => Self::Reduction(Reduction::parse_ref(file_id, state, inner)),
            Rule::equivalence => Self::Equivalence(Equivalence::parse_ref(file_id, state, inner)),
            Rule::conjecture => Self::Conjecture(Conjecture::parse_ref(file_id, state, inner)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for GameHops {
    const RULE: Rule = Rule::gamehops;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw = inner.next().unwrap();

        Self {
            trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            items: GameHopItemList::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for TheoremConstDecl {
    const RULE: Rule = Rule::expr_ident_decl;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        common::parse_value_decl(file_id, state, pair)
    }
}

impl Parsable for TheoremConstParamBlock {
    const RULE: Rule = Rule::consts_param_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = TheoremConstDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for TheoremItem {
    const RULE: Rule = Rule::theorem_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::consts_param_block => {
                Self::ConstParams(TheoremConstParamBlock::parse_ref(file_id, state, inner))
            }
            Rule::inst_block => Self::GameInstance(InstanceBlock::parse_ref(file_id, state, inner)),
            Rule::assumptions_block => {
                Self::Assumptions(AssumptionsBlock::parse_ref(file_id, state, inner))
            }
            Rule::gamehops => Self::GameHops(GameHops::parse_ref(file_id, state, inner)),
            Rule::proposition_block => todo!(),
            _ => unreachable!(),
        }
    }
}

impl Parsable for Theorem {
    const RULE: Rule = Rule::theorem;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _kw_pair = inner.next().unwrap();
        let name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let name = TheoremIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = TheoremItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name_trivia,
            name,
            brace_trivia,
            items,
        }
    }
}

#[cfg(test)]
mod static_checks {
    use super::*;

    fn impls_parsable<T: Parsable>() {}

    #[test]
    fn impl_parsable() {
        impls_parsable::<TheoremItem>();
        impls_parsable::<TheoremConstParamBlock>();
    }
}
