pub mod common;
pub mod game;
pub mod identifier;
pub mod instances;
pub mod list;
pub mod oracle_expressions;
pub mod oracles;
pub mod package;
pub mod params;
pub mod pure_expressions;
pub mod statements;
pub mod theorem;
pub mod types;

use crate::{
    arena::{Ref, Slice},
    ast_nodes::identifier::{
        GameTypeArgumentIdentifierKind, GameTypeIdentifierKind, PackageTypeArgumentIdentifierKind,
        PackageTypeIdentifierKind, TheoremTypeArgumentIdentifierKind, TheoremTypeIdentifierKind,
    },
    source::{FileId, SourceLocation},
    Arenas, Rule, State,
};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct NodeTypeId(pub u8);

pub trait ListItem {
    const LIST_RULE: Rule;
}

pub trait NodeType {
    const NODE_TYPE: NodeTypeEnum;
}

pub trait InArena: Sized {
    fn arena(arenas: &Arenas) -> &crate::arena::Arena<Self>;
    fn arena_mut(arenas: &mut Arenas) -> &mut crate::arena::Arena<Self>;
}

pub trait Indexable: Sized {
    #[allow(unused_variables)]
    fn index(reference: Ref<Self>, state: &mut State) {}
}

pub trait Parsable: NodeType + InArena + Indexable {
    const RULE: Rule;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self;

    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Self::RULE);

        Self::parse_inner(file_id, state, pair)
    }

    fn parse_ref(file_id: FileId, state: &mut State, pair: crate::Pair) -> Ref<Self> {
        // NOTE: We need to trim trailing whitespace from the span here.
        let loc = trimmed_loc(file_id, &pair);

        let node = Self::parse(file_id, state, pair);

        Ref::<Self>::from_parsed(state, loc, node)
    }
}

pub trait ParsableArenaNode: Parsable + InArena + Indexable {}

/// This predicate checks that the char is neither tab nor space, i.e. the characters we defined as
/// WHITESPACE in our grammar.
fn is_neither_tab_nor_space(c: char) -> bool {
    !matches!(c, ' ' | '\t')
}

/// A helper for trimming trailing whitespace
pub fn trimmed_loc(file_id: FileId, pair: &crate::Pair) -> SourceLocation {
    let span = pair.as_span();
    let text = pair.as_str();

    // TODO: This function probable doesn't handle multibyte characters very well

    // (requires)
    // if the span is not empty, it doesn't only consist of Rule::WHITESPACE.
    // This should be guaranteed by pest.
    debug_assert!(
        text.is_empty() || text.contains(is_neither_tab_nor_space),
        "expected pest to guearantee that if span is not empty, it doesn't only consist of Rule::WHITESPACE: {text}"
    );

    // index logic below requires non-empty spans, so we need to handle that case first
    if text.is_empty() {
        return SourceLocation {
            file_id,
            start: span.start() as u32,
            end: span.end() as u32,
        };
    }

    // find the length, i.e. first trailing whitespace char.
    // rfind finds the last non-whitespace char, then we add 1.
    //
    // example:
    // "foo "
    //    ^     rfind returns Some(2)
    //     ^    len = 3
    //
    // The unwrap follows from our debug_assert above.
    let len = 1 + text.rfind(is_neither_tab_nor_space).unwrap();
    let end = len + span.start();

    // (ensures)
    // we don't grow the span accidentally
    debug_assert!(end <= span.end());

    SourceLocation {
        file_id,
        start: span.start() as u32,
        end: end as u32,
    }
}

impl<T: NodeType + InArena + Indexable> Ref<T> {
    pub fn from_parsed(state: &mut State, loc: SourceLocation, node: T) -> Self {
        let arena = T::arena_mut(&mut state.arenas);
        let id = arena.alloc(node);

        state.tables.locations.insert(id.global_ref_id(), loc);
        T::index(id, state);

        id
    }
}

impl<T: Parsable> Slice<T> {
    pub fn from_iter<'src>(
        file_id: FileId,
        state: &mut State,
        iter: impl IntoIterator<Item = crate::Pair<'src>>,
    ) -> Self {
        let parsed: Vec<(T, _)> = iter
            .into_iter()
            .map(|pair: crate::Pair| {
                let loc = SourceLocation::from_file_and_pair(file_id, &pair);
                let node = T::parse(file_id, state, pair);
                (node, loc)
            })
            .collect();

        Self::from_parsed(state, parsed)
    }

    pub fn from_parsed(
        state: &mut State,
        parsed: impl IntoIterator<Item = (T, SourceLocation)>,
    ) -> Self {
        let mut allocator = T::arena_mut(&mut state.arenas).slice_allocator();
        let allocated: Vec<(Ref<T>, _)> = parsed
            .into_iter()
            .map(|(node, loc)| {
                let id = allocator.push(node);
                (id, loc)
            })
            .collect();

        let slice = allocator.finish();

        for (id, loc) in allocated {
            state.tables.locations.insert(id.global_ref_id(), loc);
            T::index(id, state);
        }

        slice
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Trivium {
    BlockComment,
    LineComment,
    NewLine,
}

#[derive(Debug, Clone, Copy)]
pub struct Trivia {
    pub trivia: Slice<Trivium>,
}

impl Parsable for Trivium {
    const RULE: Rule = Rule::trivium;

    fn parse_inner(_file_id: FileId, _state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::trivium);

        match pair.into_inner().next().unwrap().as_rule() {
            Rule::newline => Trivium::NewLine,
            Rule::block_comment => Trivium::BlockComment,
            Rule::line_comment => Trivium::LineComment,
            _ => unreachable!(),
        }
    }
}

impl Parsable for Trivia {
    const RULE: Rule = Rule::gap;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::gap);

        let mut trivia = vec![];
        trivia.extend(
            pair.into_inner()
                .map(|trivium_pair| Trivium::parse(file_id, state, trivium_pair)),
        );

        let mut allocator = state.arenas.trivium.slice_allocator();
        allocator.extend(trivia);

        Self {
            trivia: allocator.finish(),
        }
    }
}

macro_rules! define_node_type_enum {
    ($($variant_name:ident : $node_type:ty),* $(,)?) => {
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
        pub enum NodeTypeEnum {
            $($variant_name),*
        }

        $(
            impl NodeType for $node_type {
                const NODE_TYPE: NodeTypeEnum = NodeTypeEnum::$variant_name;
            }

        impl crate::ast_nodes::NodeTypeIdIsUnique<{NodeTypeEnum::$variant_name as u8}>
            for crate::ast_nodes::NodeTypeUniquenessGuard
        {
            type Node = $node_type;
        }
        )*
    }
}

pub fn parse_ref<T: Parsable>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
    f: fn(crate::source::FileId, &mut crate::State, crate::Pair) -> T,
) -> Ref<T> {
    // NOTE: We need to trim trailing whitespace from the span here.
    let loc = trimmed_loc(file_id, &pair);
    let node = f(file_id, state, pair);
    Ref::<T>::from_parsed(state, loc, node)
}

define_node_type_enum! {
    Trivium: Trivium,
    Trivia: Trivia,

    // Delimiters

    Comma: list::Comma,
    Semicolon: list::Semicolon,

    // Types
    //
    // ## In Packages

    Type: types::Type<identifier::PackageTypeIdentifierKind>,
    TupleType: types::TupleType<identifier::PackageTypeIdentifierKind>,
    ArgumentedType: types::ArgumentedType<identifier::PackageTypeArgumentIdentifierKind>,
    TypeArgument: types::TypeArgument<PackageTypeArgumentIdentifierKind>,
    TypeArgList: types::TypeArgList<PackageTypeArgumentIdentifierKind>,
    TypeList: types::TypeList<PackageTypeIdentifierKind>,

    // ## In Games

    GameType: types::Type<identifier::GameTypeIdentifierKind>,
    GameTupleType: types::TupleType<identifier::GameTypeIdentifierKind>,
    GameArgumentedType: types::ArgumentedType<identifier::GameTypeArgumentIdentifierKind>,
    PaddedGameTypeArgument: types::TypeArgument<GameTypeArgumentIdentifierKind>,
    GameTypeArgList: types::TypeArgList<GameTypeArgumentIdentifierKind>,
    GameTypeList: types::TypeList<GameTypeIdentifierKind>,

    // ## In Theorems

    TheoremType: types::Type<identifier::TheoremTypeIdentifierKind>,
    TheoremTupleType: types::TupleType<identifier::TheoremTypeIdentifierKind>,
    TheoremArgumentedType: types::ArgumentedType<identifier::TheoremTypeArgumentIdentifierKind>,
    PaddedTheoremTypeArgument: types::TypeArgument<TheoremTypeArgumentIdentifierKind>,
    TheoremTypeArgList: types::TypeArgList<TheoremTypeArgumentIdentifierKind>,
    TheoremTypeList: types::TypeList<TheoremTypeIdentifierKind>,

    // Pure Expressions

    PurePackageConstValueExpression: pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueTableIndexExpression: pure_expressions::TableIndexExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueTupleExpression: pure_expressions::TupleExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueParenExpression: pure_expressions::ParenExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueBinOpExpression: pure_expressions::BinOpExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueUnOpExpression: pure_expressions::UnOpExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueCallExpression: pure_expressions::CallExpression<identifier::PackageConstValueIdentifierKind>,

    PureGameConstValueExpression: pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueTableIndexExpression: pure_expressions::TableIndexExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueTupleExpression: pure_expressions::TupleExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueParenExpression: pure_expressions::ParenExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueBinOpExpression: pure_expressions::BinOpExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueUnOpExpression: pure_expressions::UnOpExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueCallExpression: pure_expressions::CallExpression<identifier::GameConstValueIdentifierKind>,

    PureTheoremConstValueExpression: pure_expressions::PureExpression<identifier::TheoremConstValueIdentifierKind>,
    PureTheoremConstValueTableIndexExpression: pure_expressions::TableIndexExpression<identifier::TheoremConstValueIdentifierKind>,
    PureTheoremConstValueTupleExpression: pure_expressions::TupleExpression<identifier::TheoremConstValueIdentifierKind>,
    PureTheoremConstValueParenExpression: pure_expressions::ParenExpression<identifier::TheoremConstValueIdentifierKind>,
    PureTheoremConstValueBinOpExpression: pure_expressions::BinOpExpression<identifier::TheoremConstValueIdentifierKind>,
    PureTheoremConstValueUnOpExpression: pure_expressions::UnOpExpression<identifier::TheoremConstValueIdentifierKind>,
    PureTheoremConstValueCallExpression: pure_expressions::CallExpression<identifier::TheoremConstValueIdentifierKind>,

    PureConstPackageExpressionList: pure_expressions::PureConstPackageExpressionList,
    PureConstGameExpressionList: pure_expressions::PureConstGameExpressionList,
    PureConstTheoremExpressionList: pure_expressions::PureConstTheoremExpressionList,
    Statement: statements::Statement,
    AssignStatement: statements::AssignStatement,
    IfThenElseStatement: statements::IfThenElseStatement,
    ReturnStatement: statements::ReturnStatement,
    ExpressionStatement: statements::ExpressionStatement,
    StatementList: statements::StatementList,
    Pattern: statements::Pattern,
    TablePattern: statements::TablePattern,
    TuplePattern: statements::TuplePattern,
    PatternList: statements::PatternList,

    OracleSignature: oracles::OracleSignature,
    OracleValueDeclList: oracles::OracleValueDeclList,
    OracleValueArgDecl: oracles::OracleValueArgDecl,
    OracleDefinition: oracles::OracleDefinition,

    OracleExpression: oracle_expressions::OracleExpression,
    OracleInvocationExpression: oracle_expressions::OracleInvocationExpression,
    ExprList: oracle_expressions::ExprList,
    TableIndexExpression: oracle_expressions::TableIndexExpression,
    SampleExpression: oracle_expressions::SampleExpression<PackageTypeIdentifierKind>,
    ParenExpression: oracle_expressions::ParenExpression,
    CallExpression: oracle_expressions::CallExpression,
    TupleExpression: oracle_expressions::TupleExpression,
    BinOpExpression: oracle_expressions::BinOpExpression,
    UnOpExpression: oracle_expressions::UnOpExpression,

    OracleDeclList: package::OracleDeclList,
    ImportOraclesBlock: package::ImportOraclesBlock,
    StateBlock: package::StateBlock,

    PackageConstDecl: package::PackageConstDecl,
    PackageConstDeclList: package::PackageConstDeclList,
    PackageConstParamBlock: package::PackageConstParamBlock,

    PackageTypeDeclList:package::PackageTypeDeclList,
    PackageTypeParamBlock: package::PackageTypeParamBlock,
    PackageItem: package::PackageItem,
    Package: package::Package,
    PackageItemList: package::PackageItemList,

    Colon: list::Colon,

    PackageTypeIdentifier: identifier::PackageTypeIdentifier,
    GameTypeIdentifier: identifier::GameTypeIdentifier,
    TheoremTypeIdentifier: identifier::TheoremTypeIdentifier,

    PackageTypeArgumentIdentifier: identifier::PackageTypeArgumentIdentifier,
    GameTypeArgumentIdentifier: identifier::GameTypeArgumentIdentifier,
    TheoremTypeArgumentIdentifier: identifier::TheoremTypeArgumentIdentifier,

    OracleIdentifier: identifier::OracleIdentifier,
    PackageIdentifier: identifier::PackageIdentifier,
    GameIdentifier: identifier::GameIdentifier,
    PackageInstanceIdentifier: identifier::PackageInstanceIdentifier,
    GameInstanceIdentifier: identifier::GameInstanceIdentifier,
    AssumptionIdentifier: identifier::AssumptionIdentifier,

    OracleValueIdentifier: identifier::OracleValueIdentifier,
    PackageConstValueIdentifier: identifier::PackageConstValueIdentifier,
    GameConstValueIdentifier: identifier::GameConstValueIdentifier,
    TheoremConstValueIdentifier: identifier::TheoremConstValueIdentifier,

    LemmaIdentifier: identifier::LemmaIdentifier,
    TheoremIdentifier: identifier::TheoremIdentifier,

    GameInstanceConstAssignmentItem: game::InstanceConstAssignmentItem,
    GameInstanceConstAssignmentList: game::InstanceConstAssignmentList,
    GameInstanceConstBlock: game::InstanceConstBlock,

    GameInstanceTypeAssignmentItem: game::InstanceTypeAssignmentItem,
    GameInstanceTypeAssignmentList: game::InstanceTypeAssignmentList,
    GameInstanceTypeBlock: game::InstanceTypeBlock,

    GameInstanceItem: game::InstanceItem,
    GameInstanceItemList: game::InstanceItemList,

    GameInstanceBlock: game::InstanceBlock,

    ComposeOracleAssignmentItem: game::ComposeOracleAssignmentItem,
    ComposeOracleAssignmentList: game::ComposeOracleAssignmentList,

    ComposePackageInstanceItem: game::ComposePackageInstanceItem,
    ComposePackageInstanceList: game::ComposePackageInstanceList,

    ComposeBlock: game::ComposeBlock,

    GameConstDecl: game::GameConstDecl,
    GameConstDeclList: game::GameConstDeclList,
    GameConstParamBlock: game::GameConstParamBlock,

    GameTypeDeclList:game::GameTypeDeclList,
    GameTypeParamBlock: game::GameTypeParamBlock,

    GameItem: game::GameItem,
    GameItemList: game::GameItemList,
    Game: game::Game,

    // theorems

    //// instances

    TheoremInstanceConstAssignmentItem: theorem::InstanceConstAssignmentItem,
    TheoremInstanceConstAssignmentList: theorem::InstanceConstAssignmentList,
    TheoremInstanceConstBlock: theorem::InstanceConstBlock,

    TheoremInstanceTypeAssignmentItem: theorem::InstanceTypeAssignmentItem,
    TheoremInstanceTypeAssignmentList: theorem::InstanceTypeAssignmentList,
    TheoremInstanceTypeBlock: theorem::InstanceTypeBlock,

    TheoremInstanceItem: theorem::InstanceItem,
    TheoremInstanceItemList: theorem::InstanceItemList,

    TheoremInstanceBlock: theorem::InstanceBlock,

    //// hybrid instances

    // HybridInstanceBlockOne: theorem::HybridInstanceBlockOne,
    // HybridInstanceBlockTwo: theorem::HybridInstanceBlockTwo,
    // HybridInstanceBlock: theorem::HybridInstanceBlock,

    TheoremConstDecl: theorem::TheoremConstDecl,
    TheoremConstDeclList: theorem::TheoremConstDeclList,
    TheoremConstParamBlock: theorem::TheoremConstParamBlock,

    Path: theorem::Path,
    PathList: theorem::PathList,
    InvariantSpec: theorem::InvariantSpec,

    SmtIdentifier: theorem::SmtIdentifier,
    SmtIdentifierList: theorem::SmtIdentifierList,
    LemmaItem: theorem::LemmaItem,
    LemmaItemList: theorem::LemmaItemList,
    LemmaBlock: theorem::LemmaBlock,
    EquivalenceOracleItem: theorem::EquivalenceOracleItem,
    EquivalenceOracleItemList: theorem::EquivalenceOracleItemList,
    EquivalenceOracleBlock: theorem::EquivalenceOracleBlock,
    EquivalenceOracleBlockList: theorem::EquivalenceOracleBlockList,
    Equivalence: theorem::Equivalence,

    Bound: theorem::Bound,
    AssumptionsItem: theorem::AssumptionsItem,
    AssumptionsItemList: theorem::AssumptionsItemList,
    AssumptionsBlock: theorem::AssumptionsBlock,

    Conjecture: theorem::Conjecture,

    ReductionAssumptionLine: theorem::ReductionAssumptionLine,
    ReductionMapItem: theorem::ReductionMapItem,
    ReductionMapItemList: theorem::ReductionMapItemList,
    ReductionMap: theorem::ReductionMap,
    ReductionItem: theorem::ReductionItem,
    ReductionItemList: theorem::ReductionItemList,
    Reduction: theorem::Reduction,

    GameHopItem: theorem::GameHopItem,
    GameHopItemList: theorem::GameHopItemList,
    GameHops: theorem::GameHops,

    TheoremItem: theorem::TheoremItem,
    TheoremItemList: theorem::TheoremItemList,
    Theorem: theorem::Theorem,

}

macro_rules! impl_noop_index {
    ($($node_type:ty),* $(,)?) => {
        $(
            impl Indexable for $node_type {}
        )*

    };
}

impl_noop_index! {
    Trivium,
    Trivia,

    // pure expressions

    //// package const
    pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::TableIndexExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::TupleExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::ParenExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::BinOpExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::UnOpExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::CallExpression<identifier::PackageConstValueIdentifierKind>,

    //// game const
    pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::TableIndexExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::TupleExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::ParenExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::BinOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::UnOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::CallExpression<identifier::GameConstValueIdentifierKind>,

    //// theorem const
    pure_expressions::PureExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions::TableIndexExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions::TupleExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions::ParenExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions::BinOpExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions::UnOpExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions::CallExpression<identifier::TheoremConstValueIdentifierKind>,

    // types
    //// in packages
    types::Type<PackageTypeIdentifierKind>,
    types::TupleType<PackageTypeIdentifierKind>,
    types::ArgumentedType<PackageTypeArgumentIdentifierKind>,
    types::TypeArgument<PackageTypeArgumentIdentifierKind>,

    //// in games
    types::Type<GameTypeIdentifierKind>,
    types::TupleType<GameTypeIdentifierKind>,
    types::ArgumentedType<GameTypeArgumentIdentifierKind>,
    types::TypeArgument<GameTypeArgumentIdentifierKind>,

    //// in theorems
    types::Type<TheoremTypeIdentifierKind>,
    types::TupleType<TheoremTypeIdentifierKind>,
    types::ArgumentedType<TheoremTypeArgumentIdentifierKind>,
    types::TypeArgument<TheoremTypeArgumentIdentifierKind>,

    // oracle expressions
    oracle_expressions::OracleExpression,
    oracle_expressions::OracleInvocationExpression,
    oracle_expressions::SampleExpression<PackageTypeIdentifierKind>,
    oracle_expressions::TableIndexExpression,
    oracle_expressions::TupleExpression,
    oracle_expressions::ParenExpression,
    oracle_expressions::BinOpExpression,
    oracle_expressions::UnOpExpression,
    oracle_expressions::CallExpression,

    // statemnts
    statements::Statement,
    statements::AssignStatement,
    statements::IfThenElseStatement,
    statements::ReturnStatement,
    statements::ExpressionStatement,
    statements::Pattern,
    statements::TablePattern,
    statements::TuplePattern,

    // oracles
    oracles::OracleSignature,
    oracles::OracleValueArgDecl,
    oracles::OracleDefinition,

    // packages
    package::PackageConstDecl,
    package::PackageConstParamBlock,

    package::ImportOraclesBlock,
    package::StateBlock,
    //package::PackageTypeIdentifierList,
    package::PackageTypeParamBlock,
    package::PackageItem,
    package::Package,
    // games
    game::InstanceConstAssignmentItem,
    game::InstanceConstBlock,
    game::InstanceTypeAssignmentItem,
    game::InstanceTypeBlock,
    game::InstanceItem,
    game::InstanceBlock,
    game::ComposeOracleAssignmentItem,
    game::ComposePackageInstanceItem,
    game::ComposeBlock,
    game::GameConstDecl,
    game::GameConstParamBlock,

    game::GameTypeParamBlock,

    game::GameItem,
    game::Game,

    // theorems
    //// instances
    theorem::InstanceConstAssignmentItem,
    theorem::InstanceConstBlock,

    theorem::InstanceTypeAssignmentItem,
    theorem::InstanceTypeBlock,

    theorem::InstanceItem,

    theorem::InstanceBlock,

    //// hybrid instances
    // theorem::HybridInstanceBlockOne,
    // theorem::HybridInstanceBlockTwo,
    // theorem::HybridInstanceBlock,

    theorem::TheoremConstDecl,
    theorem::TheoremConstParamBlock,

    theorem::Path,
    theorem::InvariantSpec,

    theorem::SmtIdentifier,
    theorem::LemmaItem,
    theorem::LemmaBlock,
    theorem::EquivalenceOracleItem,
    theorem::EquivalenceOracleBlock,
    theorem::Equivalence,

    theorem::Bound,
    theorem::AssumptionsItem,
    theorem::AssumptionsBlock,

    theorem::Conjecture,

    theorem::ReductionAssumptionLine,
    theorem::ReductionMapItem,
    theorem::ReductionMap,
    theorem::ReductionItem,
    theorem::Reduction,

    theorem::GameHopItem,
    theorem::GameHops,

    theorem::TheoremItem,
    theorem::Theorem,

    // lists
    list::Colon,
    list::Comma,
    list::Semicolon,
}

// Trick for ensuring we don't reuse node type ids

/// We implement this trait for [`NodeTypeUniquenessGuard`] for every node we run the impl macro
/// with. Implementing it twice will trigger a compiler error.
#[allow(dead_code)]
trait NodeTypeIdIsUnique<const NODE_TYPE_ID: u8> {
    type Node;
}
#[allow(dead_code)]
struct NodeTypeUniquenessGuard;
