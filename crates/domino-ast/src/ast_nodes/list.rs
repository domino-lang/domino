use crate::{
    arena::Ref,
    ast_nodes::{Slice, Trivia},
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

#[derive(Debug, Copy, Clone)]
pub struct ListNoDelim<Node> {
    pub item_leading_trivia: Slice<Trivia>,
    pub items: Slice<Node>,
    pub trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Copy, Clone)]
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
