use crate::{
    arena::Ref,
    ast_nodes::{
        common, expressions,
        identifier::{
            AssumptionIdentifier, GameConstValueIdentifierKind, GameInstanceIdentifier,
            GameInstanceIdentifierKind, GameTypeIdentifierKind, LemmaIdentifier,
            OracleCompositionIdentifier, PackageInstanceIdentifier,
            TheoremConstValueIdentifierKind, TheoremIdentifier,
        },
        instances,
        list::{Comma, List, ListNoDelim},
        params, types, Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct PureTheoremExpressionKind;

impl expressions::ExpressionKind for PureTheoremExpressionKind {
    type TypeKind = types::TheoremTypeKind;
    type ValueIdentifierKind = TheoremConstValueIdentifierKind;
}

pub type Expression = expressions::Expression<PureTheoremExpressionKind>;
pub type BinOpExpression = expressions::BinOpExpression<PureTheoremExpressionKind>;
pub type UnOpExpression = expressions::UnOpExpression<PureTheoremExpressionKind>;
pub type TableIndexExpression = expressions::TableIndexExpression<PureTheoremExpressionKind>;
pub type ParenExpression = expressions::ParenExpression<PureTheoremExpressionKind>;
pub type CallExpression = expressions::CallExpression<PureTheoremExpressionKind>;
pub type TupleExpression = expressions::TupleExpression<PureTheoremExpressionKind>;
pub type ExprList = expressions::ExprList<PureTheoremExpressionKind>;

pub type SampleExpression = expressions::SampleExpression<PureTheoremExpressionKind>;
pub type OracleInvocationExpression =
    expressions::OracleInvocationExpression<PureTheoremExpressionKind>;

pub type TheoremConstDecl = common::ValueDecl<PureTheoremExpressionKind>;
pub type TheoremConstDeclList = common::ConstDeclList<PureTheoremExpressionKind>;
pub type TheoremConstParamBlock = params::ConstParamBlock<PureTheoremExpressionKind>;

pub type InstanceConstAssignmentItem =
    instances::InstanceConstAssignmentItem<GameConstValueIdentifierKind, PureTheoremExpressionKind>;

pub type InstanceConstAssignmentList =
    instances::InstanceConstAssignmentList<GameConstValueIdentifierKind, PureTheoremExpressionKind>;
pub type InstanceConstBlock =
    instances::InstanceConstBlock<GameConstValueIdentifierKind, PureTheoremExpressionKind>;
pub type InstanceTypeAssignmentItem =
    instances::InstanceTypeAssignmentItem<GameTypeIdentifierKind, types::TheoremTypeKind>;

pub type InstanceTypeAssignmentList =
    instances::InstanceTypeAssignmentList<GameTypeIdentifierKind, types::TheoremTypeKind>;
pub type InstanceTypeBlock =
    instances::InstanceTypeBlock<GameTypeIdentifierKind, types::TheoremTypeKind>;
pub type InstanceItem = instances::InstanceItem<GameInstanceIdentifierKind>;

pub type InstanceItemList = instances::InstanceItemList<GameInstanceIdentifierKind>;
pub type InstanceBlock = instances::InstanceBlock<GameInstanceIdentifierKind>;

// hybrid instances

// #[derive(Debug, Copy, Clone)]
// pub struct HybridInstanceBlockOne {
//     pub pre_instance_trivia: Ref<Trivia>,
//     pub left_trivia: Ref<Trivia>,
//     pub left: Ref<GameIdentifier>,
//     pub right_trivia: Ref<Trivia>,
//     pub right: Ref<GameIdentifier>,
//     pub bit_trivia: Ref<Trivia>,
//     pub bit: Ref<GameIdentifier>,
//     pub eq_trivia: Ref<Trivia>,
//     pub game_trivia: Ref<Trivia>,
//     pub inst_items: Ref<InstanceItemList>,
// }
//
// #[derive(Debug, Copy, Clone)]
// pub struct HybridInstanceBlockTwo {
//     pub pre_instance_trivia: Ref<Trivia>,
//     pub left_trivia: Ref<Trivia>,
//     pub right_trivia: Ref<Trivia>,
//     pub eq_trivia: Ref<Trivia>,
//     pub outer_brace_trivia: Ref<Trivia>,
//     pub left_game_trivia: Ref<Trivia>,
//     pub left_brace_trivia: Ref<Trivia>,
//     pub letft_inst_items: Ref<InstanceItemList>,
//     pub right_game_trivia: Ref<Trivia>,
//     pub right_brace_trivia: Ref<Trivia>,
//     pub right_inst_items: Ref<InstanceItemList>,
// }
//
// #[derive(Debug, Copy, Clone)]
// pub enum HybridInstanceBlock {
//     One(Ref<HybridInstanceBlockOne>),
//     Two(Ref<HybridInstanceBlockTwo>),
// }

// paths for smt files

#[derive(Debug, Copy, Clone)]
pub struct Path;

pub type PathList = ListNoDelim<Path>;

#[derive(Debug, Copy, Clone)]
pub struct InvariantSpec {
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_open_trivia: Ref<Trivia>,
    pub paths: Ref<PathList>,
}

#[derive(Debug, Copy, Clone)]
pub struct SmtIdentifier;

pub type SmtIdentifierList = List<SmtIdentifier, Comma>;

#[derive(Debug, Copy, Clone)]
pub struct LemmaItem {
    pub name: Ref<LemmaIdentifier>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_open_trivia: Ref<Trivia>,
    pub dependencies: Ref<SmtIdentifierList>,
}

pub type LemmaItemList = ListNoDelim<LemmaItem>;

#[derive(Debug, Copy, Clone)]
pub struct LemmaBlock {
    pub trivia: Ref<Trivia>,
    pub items: Ref<LemmaItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum EquivalenceOracleItem {
    InvariantSpec(Ref<InvariantSpec>),
    LemmaBlock(Ref<LemmaBlock>),
}

pub type EquivalenceOracleItemList = ListNoDelim<EquivalenceOracleItem>;

#[derive(Debug, Copy, Clone)]
pub struct EquivalenceOracleBlock {
    pub name: Ref<OracleCompositionIdentifier>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_brace_trivia: Ref<Trivia>,
    pub items: Ref<EquivalenceOracleItemList>,
}

pub type EquivalenceOracleBlockList = ListNoDelim<EquivalenceOracleBlock>;

#[derive(Debug, Copy, Clone)]
pub struct Equivalence {
    pub kw_trivia: Ref<Trivia>,
    pub left_name: Ref<GameInstanceIdentifier>,
    pub left_trivia: Ref<Trivia>,
    pub right_name: Ref<GameInstanceIdentifier>,
    pub right_trivia: Ref<Trivia>,
    pub blocks: Ref<EquivalenceOracleBlockList>,
}

#[derive(Debug, Copy, Clone)]
pub struct Bound {
    pub lhs: Ref<GameInstanceIdentifier>,
    pub pre_tilde_trivia: Ref<Trivia>,
    pub post_tilde_trivia: Ref<Trivia>,
    pub rhs: Ref<GameInstanceIdentifier>,
}

#[derive(Debug, Copy, Clone)]
pub struct AssumptionsItem {
    pub name: Ref<AssumptionIdentifier>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_brace_trivia: Ref<Trivia>,
    pub bound: Ref<Bound>,
}

pub type AssumptionsItemList = ListNoDelim<AssumptionsItem>;

#[derive(Debug, Copy, Clone)]
pub struct AssumptionsBlock {
    pub trivia: Ref<Trivia>,
    pub items: Ref<AssumptionsItemList>,
}

#[derive(Debug, Copy, Clone)]
pub struct Conjecture {
    pub left_trivia: Ref<Trivia>,
    pub left_name: Ref<GameInstanceIdentifier>,
    pub right_trivia: Ref<Trivia>,
    pub right_name: Ref<GameInstanceIdentifier>,
}

#[derive(Debug, Copy, Clone)]
pub struct ReductionAssumptionLine {
    pub trivia: Ref<Trivia>,
    pub name: Ref<AssumptionIdentifier>,
}

#[derive(Debug, Copy, Clone)]
pub struct ReductionMapItem {
    pub left_name: Ref<PackageInstanceIdentifier>,
    pub colon_trivia: Ref<Trivia>,
    pub right_trivia: Ref<Trivia>,
    pub right_name: Ref<PackageInstanceIdentifier>,
}

pub type ReductionMapItemList = ListNoDelim<ReductionMapItem>;

#[derive(Debug, Copy, Clone)]
pub struct ReductionMap {
    pub assumption_trivia: Ref<Trivia>,
    pub assumption_name: Ref<GameInstanceIdentifier>,
    pub construction_trivia: Ref<Trivia>,
    pub construction_name: Ref<GameInstanceIdentifier>,
    pub items_trivia: Ref<Trivia>,
    pub items: Ref<ReductionMapItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum ReductionItem {
    AssumptionLine(Ref<ReductionAssumptionLine>),
    Map(Ref<ReductionMap>),
}

pub type ReductionItemList = ListNoDelim<ReductionItem>;

#[derive(Debug, Copy, Clone)]
pub struct Reduction {
    pub left_trivia: Ref<Trivia>,
    pub left_name: Ref<GameInstanceIdentifier>,
    pub right_trivia: Ref<Trivia>,
    pub right_name: Ref<GameInstanceIdentifier>,
    pub items_trivia: Ref<Trivia>,
    pub items: Ref<ReductionItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum GameHopItem {
    Reduction(Ref<Reduction>),
    Equivalence(Ref<Equivalence>),
    Conjecture(Ref<Conjecture>),
}

pub type GameHopItemList = ListNoDelim<GameHopItem>;

#[derive(Debug, Copy, Clone)]
pub struct GameHops {
    pub trivia: Ref<Trivia>,
    pub items: Ref<GameHopItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum TheoremItem {
    ConstParams(Ref<TheoremConstParamBlock>),
    GameInstance(Ref<InstanceBlock>),
    Assumptions(Ref<AssumptionsBlock>),
    GameHops(Ref<GameHops>),
    // TODO: Propositions
}

pub type TheoremItemList = ListNoDelim<TheoremItem>;

#[derive(Debug, Copy, Clone)]
pub struct Theorem {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<TheoremIdentifier>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<TheoremItemList>,
}
