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
    source::{FileId, SourceLocation},
    Arenas, Rule, State,
};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct NodeTypeId(pub u8);

pub trait NodeType {
    const NODE_TYPE_ID: NodeTypeId;
}

pub trait ArenaNode: Sized {
    fn arena(arenas: &Arenas) -> &crate::arena::Arena<Self>;
    fn arena_mut(arenas: &mut Arenas) -> &mut crate::arena::Arena<Self>;
}

pub trait Indexable: Sized {
    #[allow(unused_variables)]
    fn index(reference: Ref<Self>, state: &mut State) {}
}

pub trait Parsable: NodeType + ArenaNode + Indexable {
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self;

    fn parse_ref(file_id: FileId, state: &mut State, pair: crate::Pair) -> Ref<Self> {
        // NOTE: We need to trim trailing whitespace from the span here.
        let loc = trimmed_loc(file_id, &pair);

        let node = Self::parse(file_id, state, pair);

        Ref::<Self>::from_parsed(state, loc, node)
    }
}

pub trait ParsableArenaNode: Parsable + ArenaNode + Indexable {}

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

impl<T: NodeType + ArenaNode + Indexable> Ref<T> {
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
    PaddedRef<T>: NodeType + ArenaNode,
{
    fn index(reference: Ref<Self>, state: &mut State) {
        let padded_node = PaddedRef::arena(&state.arenas).get(reference);
        T::index(padded_node.inner, state);
    }
}

impl<T: Parsable> Parsable for PaddedRef<T>
where
    PaddedRef<T>: NodeType + ArenaNode,
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

impl_node_type!(0x00, Trivia, noop_index);
impl_node_type!(0x01, PaddedRef<types::Type>);
impl_node_type!(0x02, PaddedRef<oracle_expressions::OracleExpression>);

macro_rules! impl_node_type {
    ($id:literal, $node_type:ty $(,)?) => {
        impl crate::ast_nodes::NodeType for $node_type {
            const NODE_TYPE_ID: crate::ast_nodes::NodeTypeId = crate::ast_nodes::NodeTypeId($id);
        }

        impl crate::ast_nodes::NodeTypeIdIsUnique<$id>
            for crate::ast_nodes::NodeTypeUniquenessGuard
        {
            type Node = $node_type;
        }
    };
    ($id:literal, $node_type:ty, noop_index $(,)?) => {
        impl crate::ast_nodes::NodeType for $node_type {
            const NODE_TYPE_ID: crate::ast_nodes::NodeTypeId = crate::ast_nodes::NodeTypeId($id);
        }

        impl crate::ast_nodes::Indexable for $node_type {}

        impl crate::ast_nodes::NodeTypeIdIsUnique<$id>
            for crate::ast_nodes::NodeTypeUniquenessGuard
        {
            type Node = $node_type;
        }
    };
}

use impl_node_type;

// Trick for ensuring we don't reuse node type ids

/// We implement this trait for [`NodeTypeUniquenessGuard`] for every node we run the impl macro
/// with. Implementing it twice will trigger a compiler error.
#[allow(dead_code)]
trait NodeTypeIdIsUnique<const NODE_TYPE_ID: u8> {
    type Node;
}
#[allow(dead_code)]
struct NodeTypeUniquenessGuard;
