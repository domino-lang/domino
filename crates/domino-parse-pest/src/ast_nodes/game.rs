use domino_ast::ast_nodes::{
    game::*,
    identifier::{
        GameTypeIdentifier, Identifier, OracleCompositionIdentifier, PackageInstanceIdentifier,
    },
    list::{Colon, Comma, List},
    Trivia,
};

use crate::{
    ast_nodes::{common, expressions, instances},
    ListItem, Parsable, Rule,
};

expressions::impl_expr!(PureGameExpressionKind);

impl ListItem for InstanceConstAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_const_assignment_list;
}

impl ListItem for InstanceTypeAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_type_assignment_list;
}

impl ListItem for InstanceItem {
    const LIST_RULE: Rule = Rule::inst_list;
}

impl ListItem for ComposeOracleAssignmentItem {
    const LIST_RULE: Rule = Rule::cmps_oracle_assignment_list;
}

impl ListItem for ComposePackageInstanceItem {
    const LIST_RULE: Rule = Rule::cmps_pkg_assign_list;
}

impl ListItem for GameItem {
    const LIST_RULE: Rule = Rule::game_item_list;
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

impl Parsable for ComposeOracleAssignmentItem {
    const RULE: Rule = Rule::cmps_oracle_assignment_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let oracle_name =
            OracleCompositionIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let _colon = Colon::parse(file_id, state, inner.next().unwrap());
        let pkg_inst_name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pkg_inst_name =
            PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            oracle_name,
            pkg_inst_name,
            colon_trivia,
            pkg_inst_name_trivia,
        }
    }
}

impl Parsable for ComposePackageInstanceItem {
    const RULE: Rule = Rule::cmps_pkg_assign_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let pkg_inst_name =
            PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let _colon = Colon::parse(file_id, state, inner.next().unwrap());
        let items_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());

        let items = ComposeOracleAssignmentList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            pkg_inst_name,
            items,
            colon_trivia,
            items_trivia,
        }
    }
}

impl Parsable for ComposeBlock {
    const RULE: Rule = Rule::compose_block;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_compose = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = ComposePackageInstanceList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for GameTypeParamBlock {
    const RULE: Rule = Rule::types_param_block;

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
        let decls = List::<GameTypeIdentifier, Comma>::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for GameConstDecl {
    const RULE: Rule = Rule::expr_ident_decl;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        common::parse_value_decl(file_id, state, pair)
    }
}

impl Parsable for GameConstParamBlock {
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
        let decls = GameConstDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for GameItem {
    const RULE: Rule = Rule::game_item;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::compose_block => Self::Compose(ComposeBlock::parse_ref(file_id, state, inner)),
            Rule::inst_block => Self::Instance(InstanceBlock::parse_ref(file_id, state, inner)),
            Rule::types_param_block => {
                Self::TypeParams(GameTypeParamBlock::parse_ref(file_id, state, inner))
            }
            Rule::consts_param_block => {
                Self::ConstParams(GameConstParamBlock::parse_ref(file_id, state, inner))
            }
            _other => unreachable!(),
        }
    }
}

impl Parsable for Game {
    const RULE: Rule = Rule::game;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let _kw_game = inner.next().unwrap();
        let name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
        let brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = GameItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            items,
            name_trivia,
            brace_trivia,
        }
    }
}

#[cfg(debug_assertions)]
#[allow(dead_code)]
mod static_checks {
    use super::*;
    use domino_ast::ast_nodes::{InArena, NodeType};

    fn impls_parsable<Node: Parsable>() {}
    fn impls_nodetype<Node: NodeType>() {}
    fn impls_arenanode<Node: InArena>() {}

    fn types_impl_parsable() {
        impls_parsable::<Colon>();
        impls_parsable::<InstanceConstAssignmentItem>();
        impls_parsable::<InstanceConstAssignmentList>();
        impls_parsable::<InstanceConstBlock>();
        impls_parsable::<InstanceTypeAssignmentItem>();
        impls_parsable::<InstanceTypeAssignmentList>();
        impls_parsable::<InstanceTypeBlock>();
        impls_parsable::<InstanceItem>();
        impls_parsable::<InstanceItemList>();
        impls_parsable::<InstanceBlock>();

        impls_parsable::<ComposeOracleAssignmentItem>();
        impls_parsable::<ComposeOracleAssignmentList>();
        impls_parsable::<ComposePackageInstanceItem>();
        impls_parsable::<ComposePackageInstanceList>();
        impls_parsable::<ComposeBlock>();
        impls_parsable::<GameItem>();
        impls_parsable::<GameItemList>();
        impls_parsable::<Game>();
    }
}
