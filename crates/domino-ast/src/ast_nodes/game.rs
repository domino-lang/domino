use crate::{
    arena::Ref,
    ast_nodes::{
        common, expressions,
        identifier::{
            GameConstValueIdentifierKind, GameIdentifier, GameTypeIdentifierKind,
            OracleCompositionIdentifier, PackageConstValueIdentifierKind,
            PackageInstanceIdentifier, PackageInstanceIdentifierKind, PackageTypeIdentifierKind,
        },
        instances,
        list::{Comma, List, ListNoDelim},
        params, types, Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct PureGameExpressionKind;

impl expressions::ExpressionKind for PureGameExpressionKind {
    type TypeKind = types::GameTypeKind;
    type ValueIdentifierKind = GameConstValueIdentifierKind;
}

pub type Expression = expressions::Expression<PureGameExpressionKind>;
pub type BinOpExpression = expressions::BinOpExpression<PureGameExpressionKind>;
pub type UnOpExpression = expressions::UnOpExpression<PureGameExpressionKind>;
pub type TableIndexExpression = expressions::TableIndexExpression<PureGameExpressionKind>;
pub type ParenExpression = expressions::ParenExpression<PureGameExpressionKind>;
pub type CallExpression = expressions::CallExpression<PureGameExpressionKind>;
pub type TupleExpression = expressions::TupleExpression<PureGameExpressionKind>;
pub type ExprList = expressions::ExprList<PureGameExpressionKind>;

pub type SampleExpression = expressions::SampleExpression<PureGameExpressionKind>;
pub type OracleInvocationExpression =
    expressions::OracleInvocationExpression<PureGameExpressionKind>;

pub type GameTypeDeclList = common::TypeDeclList<GameTypeIdentifierKind>;
pub type GameTypeParamBlock = params::TypeParamBlock<GameTypeIdentifierKind>;

pub type GameConstDecl = common::ValueDecl<PureGameExpressionKind>;
pub type GameConstDeclList = common::ConstDeclList<PureGameExpressionKind>;
pub type GameConstParamBlock = params::ConstParamBlock<PureGameExpressionKind>;

pub type InstanceConstAssignmentItem =
    instances::InstanceConstAssignmentItem<PackageConstValueIdentifierKind, PureGameExpressionKind>;

pub type InstanceConstAssignmentList =
    instances::InstanceConstAssignmentList<PackageConstValueIdentifierKind, PureGameExpressionKind>;
pub type InstanceConstBlock =
    instances::InstanceConstBlock<PackageConstValueIdentifierKind, PureGameExpressionKind>;
pub type InstanceTypeAssignmentItem =
    instances::InstanceTypeAssignmentItem<PackageTypeIdentifierKind, types::GameTypeKind>;

pub type InstanceTypeAssignmentList =
    instances::InstanceTypeAssignmentList<PackageTypeIdentifierKind, types::GameTypeKind>;
pub type InstanceTypeBlock =
    instances::InstanceTypeBlock<PackageTypeIdentifierKind, types::GameTypeKind>;
pub type InstanceItem = instances::InstanceItem<PackageInstanceIdentifierKind>;

pub type InstanceItemList = instances::InstanceItemList<PackageInstanceIdentifierKind>;
pub type InstanceBlock = instances::InstanceBlock<PackageInstanceIdentifierKind>;

#[derive(Debug, Clone, Copy)]
pub struct ComposeOracleAssignmentItem {
    pub oracle_name: Ref<OracleCompositionIdentifier>,
    pub colon_trivia: Ref<Trivia>,
    pub pkg_inst_name_trivia: Ref<Trivia>,
    pub pkg_inst_name: Ref<PackageInstanceIdentifier>,
}

pub type ComposeOracleAssignmentList = List<ComposeOracleAssignmentItem, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct ComposePackageInstanceItem {
    pub pkg_inst_name: Ref<PackageInstanceIdentifier>,
    pub colon_trivia: Ref<Trivia>,
    pub items_trivia: Ref<Trivia>,
    pub items: Ref<ComposeOracleAssignmentList>,
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

pub type GameItemList = ListNoDelim<GameItem>;

#[derive(Debug, Clone, Copy)]
pub struct Game {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<GameIdentifier>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<GameItemList>,
}
