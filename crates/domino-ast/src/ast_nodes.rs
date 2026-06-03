pub mod game;
pub mod identifier;
pub mod list;
pub mod oracle_expressions;
pub mod oracles;
pub mod package;
pub mod pure_expressions;
pub mod statements;
pub mod types;

use crate::{
    arena::{Ref, Slice},
    ast_nodes::identifier::{
        GameTypeArgumentIdentifierKind, GameTypeIdentifierKind, PackageTypeArgumentIdentifierKind,
        PackageTypeIdentifierKind,
    },
    source::{FileId, SourceLocation},
    Arenas, Rule, State,
};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct NodeTypeId(pub u8);

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
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self;

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
pub enum Trivia {
    BlockComment,
    LineComment,
    BlankLine,
}

#[derive(Debug, Clone, Copy)]
pub struct Padded<T> {
    pub leading: Slice<Trivia>,
    pub inner: T,
    pub trailing: Slice<Trivia>,
}

pub type PaddedRef<T> = Padded<Ref<T>>;

impl<T: Indexable> Indexable for PaddedRef<T>
where
    PaddedRef<T>: NodeType + InArena,
{
    fn index(reference: Ref<Self>, state: &mut State) {
        let padded_node = PaddedRef::arena(&state.arenas).get(reference);
        T::index(padded_node.inner, state);
    }
}

impl<T: Parsable> Parsable for PaddedRef<T>
where
    PaddedRef<T>: NodeType + InArena,
{
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut pairs = pair.into_inner();

        let leading = Slice::from_pair(file_id, state, pairs.next().unwrap());
        let inner = T::parse_ref(file_id, state, pairs.next().unwrap());
        let trailing = Slice::from_pair(file_id, state, pairs.next().unwrap());

        PaddedRef {
            leading,
            inner,
            trailing,
        }
    }
}

impl<T: Parsable> Parsable for Padded<T>
where
    Padded<T>: NodeType + InArena + Indexable,
{
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut pairs = pair.into_inner();

        let leading = Slice::from_pair(file_id, state, pairs.next().unwrap());
        let inner = T::parse(file_id, state, pairs.next().unwrap());
        let trailing = Slice::from_pair(file_id, state, pairs.next().unwrap());

        Padded {
            leading,
            inner,
            trailing,
        }
    }
}

impl Slice<Trivia> {
    pub fn from_pair<'src>(
        file_id: FileId,
        state: &mut State,
        pair: crate::Pair<'src>,
    ) -> Slice<Trivia> {
        debug_assert_eq!(pair.as_rule(), Rule::gap);

        // set when finding the first newline in a sequence
        let mut newlines_span_start = None;

        let mut allocator = Trivia::arena_mut(&mut state.arenas).slice_allocator();

        for pair in pair.into_inner() {
            let loc = SourceLocation::from_file_and_pair(file_id, &pair);
            match pair.as_rule() {
                Rule::block_comment => {
                    newlines_span_start = None;
                    let comment = allocator.push(Trivia::BlockComment);
                    state.tables.locations.insert(comment.global_ref_id(), loc);
                }
                Rule::line_comment => {
                    newlines_span_start = None;
                    let comment = allocator.push(Trivia::LineComment);
                    state.tables.locations.insert(comment.global_ref_id(), loc);
                }
                Rule::newline => {
                    if let Some(start) = newlines_span_start {
                        let loc = SourceLocation { start, ..loc };
                        let newline = allocator.push(Trivia::BlankLine);
                        state.tables.locations.insert(newline.global_ref_id(), loc);
                    } else {
                        newlines_span_start = Some(loc.start);
                    }
                }

                _ => unreachable!(),
            }
        }

        allocator.finish()
    }
}

impl State {
    pub fn compare_trivia(&self, lhs: Slice<Trivia>, rhs: Slice<Trivia>) -> bool {
        lhs.len() == rhs.len()
            && lhs.refs().zip(rhs.refs()).all(|(lhs, rhs)| {
                let lhs = self.arenas.trivia.get(lhs);
                let rhs = self.arenas.trivia.get(rhs);

                matches!(
                    (lhs, rhs),
                    (Trivia::BlockComment, Trivia::BlockComment)
                        | (Trivia::LineComment, Trivia::LineComment)
                        | (Trivia::BlankLine, Trivia::BlankLine)
                )
            })
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

define_node_type_enum! {
    Trivia: Trivia,

    // Types
    //
    // ## In Packages

    PaddedType: PaddedRef<types::Type<identifier::PackageTypeIdentifierKind>>,
    PaddedOracleExpression: PaddedRef<oracle_expressions::OracleExpression>,
    Type: types::Type<identifier::PackageTypeIdentifierKind>,
    TupleType: types::TupleType<identifier::PackageTypeIdentifierKind>,
    ArgumentedType: types::ArgumentedType<identifier::PackageTypeArgumentIdentifierKind>,
    PaddedArgumentedType: PaddedRef<types::ArgumentedType<identifier::PackageTypeArgumentIdentifierKind>>,
    TypeArgument: types::TypeArgument<PackageTypeArgumentIdentifierKind>,
    PaddedTypeArgument: PaddedRef<types::TypeArgument<PackageTypeArgumentIdentifierKind>>,
    TypeArgList: types::TypeArgList<PackageTypeArgumentIdentifierKind>,
    TypeList: types::TypeList<PackageTypeIdentifierKind>,

    // ## In Games

    GamePaddedType: PaddedRef<types::Type<identifier::GameTypeIdentifierKind>>,
    GameType: types::Type<identifier::GameTypeIdentifierKind>,
    GameTupleType: types::TupleType<identifier::GameTypeIdentifierKind>,
    GameArgumentedType: types::ArgumentedType<identifier::GameTypeArgumentIdentifierKind>,
    PaddedGameArgumentedType: PaddedRef<types::ArgumentedType<identifier::GameTypeArgumentIdentifierKind>>,
    GameTypeArgument: PaddedRef<types::TypeArgument<GameTypeArgumentIdentifierKind>>,
    PaddedGameTypeArgument: types::TypeArgument<GameTypeArgumentIdentifierKind>,
    GameTypeArgList: types::TypeArgList<GameTypeArgumentIdentifierKind>,
    GameTypeList: types::TypeList<GameTypeIdentifierKind>,

    PurePackageConstValueExpression: pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueTableIndexExpression: pure_expressions::TableIndexExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueTupleExpression: pure_expressions::TupleExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueParenExpression: pure_expressions::ParenExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueBinOpExpression: pure_expressions::BinOpExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueUnOpExpression: pure_expressions::UnOpExpression<identifier::PackageConstValueIdentifierKind>,
    PurePackageConstValueCallExpression: pure_expressions::CallExpression<identifier::PackageConstValueIdentifierKind>,
    PaddedPurePackageConstValueExpression: PaddedRef<pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>>,

    PureGameConstValueExpression: pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueTableIndexExpression: pure_expressions::TableIndexExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueTupleExpression: pure_expressions::TupleExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueParenExpression: pure_expressions::ParenExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueBinOpExpression: pure_expressions::BinOpExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueUnOpExpression: pure_expressions::UnOpExpression<identifier::GameConstValueIdentifierKind>,
    PureGameConstValueCallExpression: pure_expressions::CallExpression<identifier::GameConstValueIdentifierKind>,
    PaddedPureGameConstValueExpression: PaddedRef<pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>>,

    PureConstPackageExpressionList: pure_expressions::PureConstPackageExpressionList,
    PureConstGameExpressionList: pure_expressions::PureConstGameExpressionList,
    Statement: statements::Statement,
    AssignStatement: statements::AssignStatement,
    IfThenElseStatement: statements::IfThenElseStatement,
    ReturnStatement: statements::ReturnStatement,
    ExpressionStatement: statements::ExpressionStatement,
    PaddedStatement: PaddedRef<statements::Statement>,
    StatementList: statements::StatementList,
    Pattern: statements::Pattern,
    TablePattern: statements::TablePattern,
    TuplePattern: statements::TuplePattern,
    PaddedPattern: PaddedRef<statements::Pattern>,
    PatternList: statements::PatternList,

    OracleSignature: oracles::OracleSignature,
    OracleValueDeclList: oracles::OracleValueDeclList,
    OracleValueArgDecl: oracles::OracleValueArgDecl,
    OracleDefinition: oracles::OracleDefinition,
    PaddedOracleValueArgDecl: PaddedRef<oracles::OracleValueArgDecl>,
    PaddedOracleSignature: PaddedRef<oracles::OracleSignature>,

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
    ConstParamBlock: package::ConstParamBlock,
    PackageTypeList: package::PackageTypeIdentifierList,
    TypeParamBlock: package::PackageTypeParamBlock,
    PackageItem: package::PackageItem,
    PaddedPackageItem: PaddedRef<package::PackageItem>,
    Package: package::Package,
    PackageItemList: package::PackageItemList,

    Colon: list::Colon,
    PaddedColon: Padded<list::Colon>,

    OracleIdentifier: identifier::OracleIdentifier,
    PackageTypeIdentifier: identifier::PackageTypeIdentifier,
    GameTypeIdentifier: identifier::GameTypeIdentifier,
    PackageTypeArgumentIdentifier: identifier::PackageTypeArgumentIdentifier,
    GameTypeArgumentIdentifier: identifier::GameTypeArgumentIdentifier,
    PackageIdentifier: identifier::PackageIdentifier,
    GameIdentifier: identifier::GameIdentifier,
    PackageInstanceIdentifier: identifier::PackageInstanceIdentifier,

    PaddedPackageTypeIdentifier: PaddedRef<identifier::PackageTypeIdentifier>,
    PaddedOracleIdentifier: PaddedRef<identifier::OracleIdentifier>,
    PaddedPackageIdentifier: PaddedRef<identifier::PackageIdentifier>,
    PaddedGameIdentifier: PaddedRef<identifier::GameIdentifier>,
    PaddedPackageInstanceIdentifier: PaddedRef<identifier::PackageInstanceIdentifier>,

    OracleValueIdentifier: identifier::OracleValueIdentifier,
    PackageConstValueIdentifier: identifier::PackageConstValueIdentifier,
    GameConstValueIdentifier: identifier::GameConstValueIdentifier,

    PaddedOracleValueIdentifier: PaddedRef<identifier::OracleValueIdentifier>,
    PaddedPackageConstValueIdentifier: PaddedRef<identifier::PackageConstValueIdentifier>,
    PaddedGameConstValueIdentifier: PaddedRef<identifier::GameConstValueIdentifier>,

    InstanceConstAssignmentItem: game::InstanceConstAssignmentItem,
    PaddedInstanceConstAssignmentItem: PaddedRef<game::InstanceConstAssignmentItem>,
    InstanceConstAssignmentList: game::InstanceConstAssignmentList,
    InstanceConstBlock: game::InstanceConstBlock,

    InstanceTypeAssignmentItem: game::InstanceTypeAssignmentItem,
    PaddedInstanceTypeAssignmentItem: PaddedRef<game::InstanceTypeAssignmentItem>,
    InstanceTypeAssignmentList: game::InstanceTypeAssignmentList,
    InstanceTypeBlock: game::InstanceTypeBlock,

    InstanceItem: game::InstanceItem,
    PaddedInstanceItem: PaddedRef<game::InstanceItem>,
    InstanceItemList: game::InstanceItemList,

    InstanceBlock: game::InstanceBlock,

    ComposeOracleAssignmentItem: game::ComposeOracleAssignmentItem,
    PaddedComposeOracleAssignmentItem: PaddedRef<game::ComposeOracleAssignmentItem>,
    ComposeOracleAssignmentList: game::ComposeOracleAssignmentList,

    ComposePackageInstanceItem: game::ComposePackageInstanceItem,
    PaddedComposePackageInstanceItem: PaddedRef<game::ComposePackageInstanceItem>,
    ComposePackageInstanceList: game::ComposePackageInstanceList,

    ComposeBlock: game::ComposeBlock,
    GameItem: game::GameItem,
    PaddedGameItem: PaddedRef<game::GameItem>,
    GameItemList: game::GameItemList,
    Game: game::Game,

}

macro_rules! impl_noop_index {
    ($($node_type:ty),* $(,)?) => {
        $(
            impl Indexable for $node_type {}
        )*

    };
}

impl_noop_index! {
    // pure expressions

    //// package const
    pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::TableIndexExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::TupleExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::ParenExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::BinOpExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::UnOpExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::CallExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions::PureConstPackageExpressionList,

    //// game const
    pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::TableIndexExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::TupleExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::ParenExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::BinOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::UnOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::CallExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions::PureConstGameExpressionList,

    // types
    //// in packages
    types::Type<PackageTypeIdentifierKind>,
    types::TypeList<PackageTypeIdentifierKind>,
    types::TupleType<PackageTypeIdentifierKind>,
    types::ArgumentedType<PackageTypeArgumentIdentifierKind>,
    types::TypeArgument<PackageTypeArgumentIdentifierKind>,
    types::TypeArgList<PackageTypeArgumentIdentifierKind>,

    //// in games
    types::Type<GameTypeIdentifierKind>,
    types::TypeList<GameTypeIdentifierKind>,
    types::TupleType<GameTypeIdentifierKind>,
    types::ArgumentedType<GameTypeArgumentIdentifierKind>,
    types::TypeArgument<GameTypeArgumentIdentifierKind>,
    types::TypeArgList<GameTypeArgumentIdentifierKind>,

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
    oracle_expressions::ExprList,

    // statemnts
    statements::Statement,
    statements::AssignStatement,
    statements::IfThenElseStatement,
    statements::ReturnStatement,
    statements::ExpressionStatement,
    statements::StatementList,
    statements::Pattern,
    statements::TablePattern,
    statements::TuplePattern,
    statements::PatternList,

    // oracles
    oracles::OracleSignature,
    oracles::OracleValueArgDecl,
    oracles::OracleValueDeclList,
    oracles::OracleDefinition,

    // packages
    package::OracleDeclList,
    package::ImportOraclesBlock,
    package::StateBlock,
    package::ConstParamBlock,
    //package::PackageTypeIdentifierList,
    package::PackageTypeDeclList,
    package::PackageTypeParamBlock,
    package::PackageItem,
    package::Package,
    package::PackageItemList,

    // games
    game::InstanceConstAssignmentItem,
    game::InstanceConstAssignmentList,
    game::InstanceConstBlock,
    game::InstanceTypeAssignmentItem,
    game::InstanceTypeAssignmentList,
    game::InstanceTypeBlock,
    game::InstanceItem,
    game::InstanceItemList,
    game::InstanceBlock,
    game::ComposeOracleAssignmentItem,
    game::ComposeOracleAssignmentList,
    game::ComposePackageInstanceItem,
    game::ComposePackageInstanceList,
    game::ComposeBlock,
    game::GameItem,
    game::GameItemList,
    game::Game,

    // lists
    list::Colon,
    Padded<list::Colon>,
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
