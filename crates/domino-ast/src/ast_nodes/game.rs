use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{
            GameConstValueIdentifierKind, GameIdentifier, GameTypeIdentifierKind, Identifier,
            OracleIdentifier, PackageConstValueIdentifierKind, PackageInstanceIdentifier,
            PackageInstanceIdentifierKind, PackageTypeIdentifierKind,
        },
        instances,
        list::{Colon, Comma, List, ListNoDelim},
        pure_expressions::PureExpression,
        types::Type,
        ListItem, Padded, PaddedRef, Parsable, Trivia,
    },
    Rule,
};

pub type InstanceConstAssignmentItem = instances::InstanceConstAssignmentItem<
    PackageConstValueIdentifierKind,
    GameConstValueIdentifierKind,
>;

impl ListItem for InstanceConstAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_const_assignment_list;
}

pub type InstanceConstAssignmentList = List<InstanceConstAssignmentItem, Comma>;
pub type InstanceConstBlock =
    instances::InstanceConstBlock<PackageConstValueIdentifierKind, GameConstValueIdentifierKind>;
pub type InstanceTypeAssignmentItem =
    instances::InstanceTypeAssignmentItem<PackageTypeIdentifierKind, GameTypeIdentifierKind>;

impl ListItem for InstanceTypeAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_type_assignment_list;
}

pub type InstanceTypeAssignmentList =
    instances::InstanceTypeAssignmentList<PackageTypeIdentifierKind, GameTypeIdentifierKind>;
pub type InstanceTypeBlock =
    instances::InstanceTypeBlock<PackageTypeIdentifierKind, GameTypeIdentifierKind>;
pub type InstanceItem = instances::InstanceItem<PackageInstanceIdentifierKind>;

impl ListItem for InstanceItem {
    const LIST_RULE: Rule = Rule::inst_list;
}

pub type InstanceItemList = instances::InstanceItemList<PackageInstanceIdentifierKind>;
pub type InstanceBlock = instances::InstanceBlock<PackageInstanceIdentifierKind>;

#[derive(Debug, Clone, Copy)]
pub struct ComposeOracleAssignmentItem {
    pub oracle_name: Ref<OracleIdentifier>,
    pub padded_colon: Padded<Colon>,
    pub pkg_inst_name: Ref<PackageInstanceIdentifier>,
}

impl ListItem for ComposeOracleAssignmentItem {
    const LIST_RULE: Rule = Rule::cmps_oracle_assignment_list;
}

pub type ComposeOracleAssignmentList = List<ComposeOracleAssignmentItem, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct ComposePackageInstanceItem {
    pub pkg_inst_name: Ref<PackageInstanceIdentifier>,
    pub padded_colon: Padded<Colon>,
    pub items: Ref<ComposeOracleAssignmentList>,
}

impl ListItem for ComposePackageInstanceItem {
    const LIST_RULE: Rule = Rule::cmps_pkg_assign_list;
}

pub type ComposePackageInstanceList = List<ComposePackageInstanceItem, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct ComposeBlock {
    pub trivia: Ref<Trivia>,
    pub items: Ref<ComposePackageInstanceList>,
}

#[derive(Debug, Clone, Copy)]
pub enum GameItem {
    Instance(Ref<InstanceBlock>),
    Compose(Ref<ComposeBlock>),
}

impl ListItem for GameItem {
    const LIST_RULE: Rule = Rule::game_item_list;
}

pub type GameItemList = ListNoDelim<GameItem>;

#[derive(Debug, Clone, Copy)]
pub struct Game {
    pub name: PaddedRef<GameIdentifier>,
    pub items: Ref<GameItemList>,
}

impl Parsable for Colon {
    fn parse(
        _file_id: crate::source::FileId,
        _state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::colon);

        Self
    }
}

impl Parsable for InstanceConstAssignmentItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_const_assignment_item);

        let mut inner = pair.into_inner();
        let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
        let colon = Padded::parse(file_id, state, inner.next().unwrap());
        let expr = PureExpression::<GameConstValueIdentifierKind>::parse_ref(
            file_id,
            state,
            inner.next().unwrap(),
        );

        Self { ident, colon, expr }
    }
}

impl Parsable for InstanceConstBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_const_block);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_type_assignment_item);

        let mut inner = pair.into_inner();
        let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
        let colon = Padded::parse(file_id, state, inner.next().unwrap());
        let ty = Type::parse_ref(file_id, state, inner.next().unwrap());

        Self { ident, colon, ty }
    }
}

impl Parsable for InstanceTypeBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_type_block);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_item);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_block);

        let mut inner = pair.into_inner();
        let _kw_instance = inner.next().unwrap();
        let name = PaddedRef::parse(file_id, state, inner.next().unwrap());
        let items = InstanceItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self { name, items }
    }
}

impl Parsable for ComposeOracleAssignmentItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::cmps_oracle_assignment_item);

        let mut inner = pair.into_inner();
        let oracle_name = OracleIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let padded_colon = Padded::<Colon>::parse(file_id, state, inner.next().unwrap());
        let pkg_inst_name =
            PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            oracle_name,
            padded_colon,
            pkg_inst_name,
        }
    }
}

impl Parsable for ComposePackageInstanceItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::cmps_pkg_assign_item);

        let mut inner = pair.into_inner();

        let pkg_inst_name =
            PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let padded_colon = Padded::<Colon>::parse(file_id, state, inner.next().unwrap());

        let items = ComposeOracleAssignmentList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            pkg_inst_name,
            padded_colon,
            items,
        }
    }
}

impl Parsable for ComposeBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::compose_block);

        let mut inner = pair.into_inner();

        let _kw_compose = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = ComposePackageInstanceList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for GameItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::game_item);

        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::compose_block => Self::Compose(ComposeBlock::parse_ref(file_id, state, inner)),
            Rule::inst_block => Self::Instance(InstanceBlock::parse_ref(file_id, state, inner)),
            Rule::types_param_block => todo!(),
            Rule::consts_param_block => todo!(),
            _other => unreachable!(),
        }
    }
}

impl Parsable for Game {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::game);

        let mut inner = pair.into_inner();

        let _kw_game = inner.next().unwrap();
        let name = PaddedRef::parse(file_id, state, inner.next().unwrap());
        let items = GameItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self { name, items }
    }
}

#[cfg(debug_assertions)]
#[allow(dead_code)]
mod static_checks {
    use super::*;
    use crate::ast_nodes::{InArena, NodeType};

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
