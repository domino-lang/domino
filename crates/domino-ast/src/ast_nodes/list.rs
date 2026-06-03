use crate::ast_nodes::{PaddedRef, Slice, Trivia};

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

/// A list separated by `Delimiter`. Usually surrounded by parenthises
#[derive(Debug)]
pub enum List<Item, Delimiter> {
    /// Just the trivia where a list could be
    None(Slice<Trivia>),

    /// An actual list.
    /// This variant should never be instantiated with an empty slice.
    Some {
        items: Slice<PaddedRef<Item>>,
        delim: Delimiter,
        has_trailing_delim: bool,
    },
}

impl<T, Delimiter: Copy> Clone for List<T, Delimiter> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, Delimiter: Clone + Copy> Copy for List<T, Delimiter> {}

macro_rules! impl_list {
    ($item:ty, $list_rule:expr, $item_rule:pat, $delim:ty, $delim_rule:pat $(,)?) => {
        impl crate::ast_nodes::Parsable for List<$item, $delim> {
            fn parse(
                file_id: crate::source::FileId,
                state: &mut crate::state::State,
                pair: crate::Pair,
            ) -> Self {
                debug_assert_eq!(pair.as_rule(), $list_rule);

                let mut inner = pair.into_inner();
                match inner.peek().unwrap().as_rule() {
                    Rule::gap => List::None(crate::arena::Slice::from_pair(
                        file_id,
                        state,
                        inner.next().unwrap(),
                    )),
                    $item_rule => {
                        let mut items = vec![];
                        let mut has_trailing_delim = false;

                        for pair in inner {
                            match pair.as_rule() {
                                $item_rule => items.push((
                                    crate::source::SourceLocation::from_file_and_pair(
                                        file_id, &pair,
                                    ),
                                    crate::ast_nodes::PaddedRef::parse(file_id, state, pair),
                                )),
                                $delim_rule => {
                                    has_trailing_delim = true;
                                }
                                rule => {
                                    unreachable!("unexpected rule while parsing list: {rule:?}")
                                }
                            }
                        }

                        let mut allocator =
                            <crate::ast_nodes::PaddedRef<$item> as crate::ast_nodes::InArena>::arena_mut(
                                &mut state.arenas,
                            )
                            .slice_allocator();

                        for (loc, item) in items {
                            let item_ref = allocator.push(item);
                            state.tables.locations.insert(item_ref.global_ref_id(), loc);
                        }

                        List::Some {
                            items: allocator.finish(),
                            delim: <$delim as Default>::default(),
                            has_trailing_delim,
                        }
                    }
                    other => unreachable!("got {other:?}"),
                }
            }
        }
    };
}

pub(crate) use impl_list;
