use crate::{
    arena::Ref,
    ast_nodes::{
        common,
        identifier::{
            GameConstValueIdentifierKind, GameIdentifier, GameTypeIdentifier,
            GameTypeIdentifierKind, Identifier, OracleIdentifier, PackageConstValueIdentifierKind,
            PackageInstanceIdentifier, PackageInstanceIdentifierKind, PackageTypeIdentifierKind,
        },
        instances,
        list::{Colon, Comma, List, ListNoDelim},
        params, ListItem, Parsable, Trivia,
    },
    Rule,
};

pub type GameTypeDeclList = common::TypeDeclList<GameTypeIdentifierKind>;
pub type GameTypeParamBlock = params::TypeParamBlock<GameTypeIdentifierKind>;

pub type GameConstDecl = common::ValueDecl<GameConstValueIdentifierKind>;
pub type GameConstDeclList = common::ConstDeclList<GameConstValueIdentifierKind>;
pub type GameConstParamBlock = params::ConstParamBlock<GameConstValueIdentifierKind>;

pub type InstanceConstAssignmentItem = instances::InstanceConstAssignmentItem<
    PackageConstValueIdentifierKind,
    GameConstValueIdentifierKind,
>;

impl ListItem for InstanceConstAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_const_assignment_list;
}

pub type InstanceConstAssignmentList = instances::InstanceConstAssignmentList<
    PackageConstValueIdentifierKind,
    GameConstValueIdentifierKind,
>;
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
    pub colon_trivia: Ref<Trivia>,
    pub pkg_inst_name_trivia: Ref<Trivia>,
    pub pkg_inst_name: Ref<PackageInstanceIdentifier>,
}

impl ListItem for ComposeOracleAssignmentItem {
    const LIST_RULE: Rule = Rule::cmps_oracle_assignment_list;
}

pub type ComposeOracleAssignmentList = List<ComposeOracleAssignmentItem, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct ComposePackageInstanceItem {
    pub pkg_inst_name: Ref<PackageInstanceIdentifier>,
    pub colon_trivia: Ref<Trivia>,
    pub items_trivia: Ref<Trivia>,
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
    TypeParams(Ref<GameTypeParamBlock>),
    ConstParams(Ref<GameConstParamBlock>),
    Instance(Ref<InstanceBlock>),
    Compose(Ref<ComposeBlock>),
}

impl ListItem for GameItem {
    const LIST_RULE: Rule = Rule::game_item_list;
}

pub type GameItemList = ListNoDelim<GameItem>;

#[derive(Debug, Clone, Copy)]
pub struct Game {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<GameIdentifier>,
    pub brace_trivia: Ref<Trivia>,
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
        super::instances::parse_instance_const_assignment_item(file_id, state, pair)
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
        instances::parse_instance_type_assignment_item(file_id, state, pair)
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
        super::instances::parse_instance_block(file_id, state, pair)
    }
}

impl Parsable for ComposeOracleAssignmentItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::cmps_oracle_assignment_item);

        let mut inner = pair.into_inner();
        let oracle_name = OracleIdentifier::parse_ref(file_id, state, inner.next().unwrap());
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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::cmps_pkg_assign_item);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::compose_block);

        let mut inner = pair.into_inner();

        let _kw_compose = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = ComposePackageInstanceList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for GameTypeParamBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::types_param_block);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        common::parse_value_decl(file_id, state, pair)
    }
}

impl Parsable for GameConstParamBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::consts_param_block);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::game_item);

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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::game);

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
