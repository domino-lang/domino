use crate::{
    arena::Ref,
    ast_nodes::{InArena, Indexable, ListItem, NodeType, Parsable, Slice, Trivia},
    source::SourceLocation,
    Rule,
};

/// Denotes that the list is delimited with a comma
#[derive(Debug, Clone, Copy, Default)]
pub struct Comma;

/// Denotes that the list is delimited with a Semicolon
#[derive(Debug, Clone, Copy, Default)]
pub struct Semicolon;

#[derive(Debug, Clone, Copy, Default)]
pub struct Colon;

/// Denotes that the list is delimited with newlines
// NOTE: observe whether the interplay with the trivia makes sense here
#[derive(Debug, Clone, Copy, Default)]
pub struct Newlines;

trait Delimiter: Parsable {}

impl Delimiter for Comma {}
impl Delimiter for Semicolon {}

impl Parsable for Comma {
    fn parse(
        _file_id: crate::source::FileId,
        _state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::comma);

        Comma
    }
}

impl Parsable for Semicolon {
    fn parse(
        _file_id: crate::source::FileId,
        _state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::semicolon);

        Semicolon
    }
}

#[derive(Debug)]
pub struct ListNoDelim<Node> {
    pub item_leading_trivia: Slice<Trivia>,
    pub items: Slice<Node>,
    pub trailing_trivia: Ref<Trivia>,
}

#[derive(Debug)]
pub struct List<Node, Delim> {
    // Length: n
    pub item_leading_trivia: Slice<Trivia>,
    // Length: n
    pub items: Slice<Node>,
    // Length: n-1 or n, depending on whether there is a trailing delimiter (or anything at all)
    pub delim_leading_trivia: Slice<Trivia>,
    // TODO: This means we have to construct it. Maybe make it PhantomData?
    pub delim: Delim,
    pub trailing_trivia: Ref<Trivia>,
}

impl<Node, Delim> Parsable for List<Node, Delim>
where
    Node: Parsable + ListItem,
    Delim: Delimiter + Default,
    Self: InArena + Indexable + NodeType,
{
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Node::LIST_RULE);

        /// get source location and parsed node
        fn parse_with_loc<Node: Parsable>(
            file_id: crate::source::FileId,
            state: &mut crate::State,
            pair: crate::Pair,
        ) -> (Node, SourceLocation) {
            let loc = SourceLocation::from_file_and_pair(file_id, &pair);
            let node = Node::parse(file_id, state, pair);

            (node, loc)
        }

        /// allocate the full slice and store source location for all nodes.
        /// this is a macro instead of a closure so we can access `state` without moving it out.
        macro_rules! alloc_slice_and_track_locs {
            ($nodes:expr, $node:ty) => {{
                let mut allocator = <$node>::arena_mut(&mut state.arenas).slice_allocator();
                for (node, loc) in $nodes {
                    let node_ref = allocator.push(node);
                    state.tables.locations.insert(node_ref.global_ref_id(), loc);
                }
                allocator.finish()
            }};
        }

        let mut item_trivias = vec![];
        let mut items = vec![];
        let mut delim_trivias = vec![];

        let mut inner = pair.into_inner();

        /* General rule style:
         *
         *   ( gap ~ item ~ ( gap ~ delim ~ gap item )* ~ ( gap ~ delim )? )? ~ gap
         *
         * Algorithmic approach:
         * 1.  We first take one pair from the iterator.
         *     That is a gap - either the first or the last.
         * 2.  We try taking another.
         *     a.  If it fails, we know we don't have any items and return a list
         *         with just the trailing gap.
         *     b.  otherwise, we parse it as an item.
         * 3. now we process in a loop. The loop may end at two points:
         *     a.  after the post-item gap. In this case, that is the trailing trivia in case there
         *         is no trailing delimiter
         *     b.  after the post-delim gap. In this case, there is a trailing delimiter and the
         *         final trailing trivia
         */

        let trivia_pair = inner.next().unwrap();
        let Some(item_pair) = inner.next() else {
            return Self {
                item_leading_trivia: alloc_slice_and_track_locs!(item_trivias, Trivia),
                items: alloc_slice_and_track_locs!(items, Node),
                delim_leading_trivia: alloc_slice_and_track_locs!(delim_trivias, Trivia),
                trailing_trivia: Trivia::parse_ref(file_id, state, trivia_pair),

                delim: Delim::default(),
            };
        };

        item_trivias.push(parse_with_loc(file_id, state, trivia_pair));
        items.push(parse_with_loc(file_id, state, item_pair));

        let mut post_item_trivia_pair = inner.next().unwrap();
        loop {
            let Some(delim_pair) = inner.next() else {
                // if post_item_trivia_pair was the last, then it is the trailing trivia

                return Self {
                    item_leading_trivia: alloc_slice_and_track_locs!(item_trivias, Trivia),
                    items: alloc_slice_and_track_locs!(items, Node),
                    delim_leading_trivia: alloc_slice_and_track_locs!(delim_trivias, Trivia),
                    delim: Delim::default(),
                    trailing_trivia: Trivia::parse_ref(file_id, state, post_item_trivia_pair),
                };
            };

            delim_trivias.push(parse_with_loc(file_id, state, post_item_trivia_pair));
            // parse this just so the inner Rule assert fires
            let _delim = Delim::parse(file_id, state, delim_pair);

            let post_delim_trivia_pair = inner.next().unwrap();
            let Some(item_pair) = inner.next() else {
                // if post_delim_trivia_pair was the last, then it is the trailing trivia

                return Self {
                    item_leading_trivia: alloc_slice_and_track_locs!(item_trivias, Trivia),
                    items: alloc_slice_and_track_locs!(items, Node),
                    delim_leading_trivia: alloc_slice_and_track_locs!(delim_trivias, Trivia),
                    trailing_trivia: Trivia::parse_ref(file_id, state, post_delim_trivia_pair),

                    delim: Delim::default(),
                };
            };

            item_trivias.push(parse_with_loc(file_id, state, post_delim_trivia_pair));
            items.push(parse_with_loc(file_id, state, item_pair));

            post_item_trivia_pair = inner.next().unwrap();
        }
    }
}

impl<Node, Delim> Indexable for List<Node, Delim>
where
    Self: InArena,
    Node: Parsable,
{
    fn index(reference: Ref<Self>, state: &mut crate::State) {
        let node = Self::arena(&state.arenas).get(reference);
        for item in node.items.refs() {
            Node::index(item, state)
        }
    }
}

impl<Node> Indexable for ListNoDelim<Node>
where
    Self: InArena,
    Node: Parsable,
{
    fn index(reference: Ref<Self>, state: &mut crate::State) {
        let node = Self::arena(&state.arenas).get(reference);
        for item in node.items.refs() {
            Node::index(item, state)
        }
    }
}

impl<Node> Parsable for ListNoDelim<Node>
where
    Node: Parsable + ListItem,
    Self: InArena + Indexable + NodeType,
{
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Node::LIST_RULE);

        let mut trivias = vec![];
        let mut items = vec![];
        let mut latest_trivia: Trivia;

        let mut inner = pair.into_inner();

        loop {
            let trivia_pair = inner.next().unwrap();
            let trivia_loc = SourceLocation::from_file_and_pair(file_id, &trivia_pair);
            latest_trivia = Trivia::parse(file_id, state, trivia_pair);

            let Some(item_pair) = inner.next() else {
                let trailing_trivia = Ref::from_parsed(state, trivia_loc, latest_trivia);

                let mut items_allocator = Node::arena_mut(&mut state.arenas).slice_allocator();

                for (item, item_loc) in items {
                    let item_ref = items_allocator.push(item);
                    state
                        .tables
                        .locations
                        .insert(item_ref.global_ref_id(), item_loc);
                }
                let items = items_allocator.finish();

                let mut trivia_allocator = Trivia::arena_mut(&mut state.arenas).slice_allocator();

                for (trivia, trivia_loc) in trivias {
                    let trivia_ref = trivia_allocator.push(trivia);
                    state
                        .tables
                        .locations
                        .insert(trivia_ref.global_ref_id(), trivia_loc);
                }

                return Self {
                    item_leading_trivia: trivia_allocator.finish(),
                    items,
                    trailing_trivia,
                };
            };

            let item_loc = SourceLocation::from_file_and_pair(file_id, &item_pair);
            let item = Node::parse(file_id, state, item_pair);

            trivias.push((latest_trivia, trivia_loc));
            items.push((item, item_loc));
        }
    }
}
