pub mod common;
pub mod expressions;
pub mod game;
pub mod identifier;
pub mod instances;
pub mod list;
pub mod oracles;
pub mod package;
pub mod params;
pub mod statements;
pub mod theorem;
pub mod types;

use crate::{
    arena::{Ref, Slice},
    source::{FileId, SourceLocation},
    Arenas, Rule, State,
};

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
    !is_tab_or_space(c)
}

/// This predicate checks that the char is either tab or space, i.e. the characters we defined as
/// WHITESPACE in our grammar.
fn is_tab_or_space(c: char) -> bool {
    matches!(c, ' ' | '\t')
}

/// A helper for trimming trailing whitespace
pub fn trimmed_loc(file_id: FileId, pair: &crate::Pair) -> SourceLocation {
    let span = pair.as_span();
    let text = pair.as_str();

    // (requires)
    // if the span is not empty, it doesn't only consist of Rule::WHITESPACE.
    // This should be guaranteed by pest.
    debug_assert!(
        text.is_empty() || text.contains(is_neither_tab_nor_space),
        "expected pest to guarantee that if span is not empty, it doesn't only consist of Rule::WHITESPACE: {text}"
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
    let len = text.trim_end_matches(is_tab_or_space).len();
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

    /*
    Type: types::Type<identifier::PackageTypeIdentifierKind>,
    TupleType: types::TupleType<identifier::PackageTypeIdentifierKind>,
    FnType: types::FnType<PackageTypeIdentifierKind>,
    ArgumentedType: types::ArgumentedType<identifier::PackageTypeArgumentIdentifierKind>,
    TypeArgument: types::TypeArgument<PackageTypeArgumentIdentifierKind>,
    TypeArgList: types::TypeArgList<PackageTypeArgumentIdentifierKind>,
*/

    Type2: types::Type<types::PackageTypeKind>,
    TupleType2:types::TupleType<types::PackageTypeKind>,
    FnType2:types::FnType<types::PackageTypeKind>,
    ApplicationType: types::ArgumentedType<types::PackageTypeKind>,
    TypeArg2:types::TypeArgument<types::PackageTypeKind>,
    TypeArgList: types::TypeArgList<types::PackageTypeKind>,
    TypeList: types::TypeList<types::PackageTypeKind>,

    GameType2: types::Type<types::GameTypeKind>,
    GameTupleType2:types::TupleType<types::GameTypeKind>,
    GameFnType2:types::FnType<types::GameTypeKind>,
    GameApplicationType: types::ArgumentedType<types::GameTypeKind>,
    GameTypeArg2:types::TypeArgument<types::GameTypeKind>,
    GameTypeArgList: types::TypeArgList<types::GameTypeKind>,
    GameTypeList: types::TypeList<types::GameTypeKind>,

    TheoremType2: types::Type<types::TheoremTypeKind>,
    TheoremTupleType2:types::TupleType<types::TheoremTypeKind>,
    TheoremFnType2:types::FnType<types::TheoremTypeKind>,
    TheoremApplicationType: types::ArgumentedType<types::TheoremTypeKind>,
    TheoremTypeArg2:types::TypeArgument<types::TheoremTypeKind>,
    TheoremTypeArgList: types::TypeArgList<types::TheoremTypeKind>,
    TheoremTypeList: types::TypeList<types::TheoremTypeKind>,

    // ## In Games

    /*
    GameType: types::Type<identifier::GameTypeIdentifierKind>,
    GameTupleType: types::TupleType<identifier::GameTypeIdentifierKind>,
    GameFnType: types::FnType<GameTypeIdentifierKind>,
    GameArgumentedType: types::ArgumentedType<identifier::GameTypeArgumentIdentifierKind>,
    PaddedGameTypeArgument: types::TypeArgument<GameTypeArgumentIdentifierKind>,
    GameTypeArgList: types::TypeArgList<GameTypeArgumentIdentifierKind>,
    GameTypeList: types::TypeList<GameTypeIdentifierKind>,

    // ## In Theorems

    TheoremType: types::Type<identifier::TheoremTypeIdentifierKind>,
    TheoremTupleType: types::TupleType<identifier::TheoremTypeIdentifierKind>,
    TheoremFnType: types::FnType<TheoremTypeIdentifierKind>,
    TheoremArgumentedType: types::ArgumentedType<identifier::TheoremTypeArgumentIdentifierKind>,
    PaddedTheoremTypeArgument: types::TypeArgument<TheoremTypeArgumentIdentifierKind>,
    TheoremTypeArgList: types::TypeArgList<TheoremTypeArgumentIdentifierKind>,
    TheoremTypeList: types::TypeList<TheoremTypeIdentifierKind>,
*/

    // Pure Expressions

    PurePackageConstValueExpression:                 package::Expression,
    PurePackageConstValueTableIndexExpression:       package::TableIndexExpression,
    PurePackageConstValueTupleExpression:            package::TupleExpression,
    PurePackageConstValueParenExpression:            package::ParenExpression,
    PurePackageConstValueBinOnExpression:            package::BinOpExpression,
    PurePackageConstValueUnOnExpression:             package::UnOpExpression,
    PurePackageConstValueCallExpression:             package::CallExpression,
    PurePackageConstValueOracleInvocationExpression: package::OracleInvocationExpression,
    PurePackageConstValueSampleExpression:           package::SampleExpression,

    PureGameConstValueExpression: game::Expression,
    PureGameConstValueTableIndexExpression: game::TableIndexExpression,
    PureGameConstValueTupleExpression: game::TupleExpression,
    PureGameConstValueParenExpression: game::ParenExpression,
    PureGameConstValueBinOnExpression:game::BinOpExpression,
    PureGameConstValueUnOnExpression:game::UnOpExpression,
    PureGameConstValueCallExpression:game::CallExpression,
    PureGameConstValueOracleInvocationExpression:game::OracleInvocationExpression,
    PureGameConstValueSampleExpression:game::SampleExpression,

    PureTheoremConstValueExpression: theorem::Expression,
    PureTheoremConstValueTableIndexExpression: theorem::TableIndexExpression,
    PureTheoremConstValueTupleExpression: theorem::TupleExpression,
    PureTheoremConstValueParenExpression: theorem::ParenExpression,
    PureTheoremConstValueBinOnExpression:theorem::BinOpExpression,
    PureTheoremConstValueUnOnExpression:theorem::UnOpExpression,
    PureTheoremConstValueCallExpression:theorem::CallExpression,
    PureTheoremConstValueOracleInvocationExpression:theorem::OracleInvocationExpression,
    PureTheoremConstValueSampleExpression:theorem::SampleExpression,

    PureConstPackageExpressionList: package::ExprList,
    PureConstGameExpressionList: game::ExprList,
    PureConstTheoremExpressionList: theorem::ExprList,

    Statement: statements::Statement,
    AssignStatement: statements::AssignStatement,
    AssertStatement: statements::AssertStatement,
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

    OracleExpression: oracles::OracleExpression,
    OracleInvocationExpression: oracles::OracleInvocationExpression,
    ExprList: oracles::ExprList,
    TableIndexExpression: oracles::TableIndexExpression,
    SampleExpression: oracles::SampleExpression,
    ParenExpression: oracles::ParenExpression,
    CallExpression: oracles::CallExpression,
    TupleExpression: oracles::TupleExpression,
    BinOpExpression: oracles::BinOpExpression,
    UnOpExpression: oracles::UnOpExpression,

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
    package::Expression,
    package::TupleExpression,
    package::TableIndexExpression,
    package::ParenExpression,
    package::BinOpExpression,
    package::UnOpExpression,
    package::CallExpression,
    package::OracleInvocationExpression,
    package::SampleExpression,

    //// game const
    game::Expression,
    game::TupleExpression,
    game::TableIndexExpression,
    game::ParenExpression,
    game::BinOpExpression,
    game::UnOpExpression,
    game::CallExpression,
    game::OracleInvocationExpression,
    game::SampleExpression,

    //// theorem const
    theorem::Expression,
    theorem::TupleExpression,
    theorem::TableIndexExpression,
    theorem::ParenExpression,
    theorem::BinOpExpression,
    theorem::UnOpExpression,
    theorem::CallExpression,
    theorem::OracleInvocationExpression,
    theorem::SampleExpression,

    // types
    //// in packages
    types::Type<types::PackageTypeKind>,
    types::TupleType<types::PackageTypeKind>,
    types::FnType<types::PackageTypeKind>,
    types::ArgumentedType<types::PackageTypeKind>,
    types::TypeArgument<types::PackageTypeKind>,


    //// in games
    types::Type<types::GameTypeKind>,
    types::TupleType<types::GameTypeKind>,
    types::FnType<types::GameTypeKind>,
    types::ArgumentedType<types::GameTypeKind>,
    types::TypeArgument<types::GameTypeKind>,

    //// in theorems
    types::Type<types::TheoremTypeKind>,
    types::TupleType<types::TheoremTypeKind>,
    types::FnType<types::TheoremTypeKind>,
    types::ArgumentedType<types::TheoremTypeKind>,
    types::TypeArgument<types::TheoremTypeKind>,

    // oracle expressions
    oracles::OracleExpression,
    oracles::TableIndexExpression,
    oracles::TupleExpression,
    oracles::ParenExpression,
    oracles::BinOpExpression,
    oracles::UnOpExpression,
    oracles::CallExpression,
    oracles::OracleInvocationExpression,
    oracles::SampleExpression,

    // statemnts
    statements::Statement,
    statements::AssertStatement,
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
