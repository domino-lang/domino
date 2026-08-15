use domino_ast::{
    arena::Ref,
    ast_nodes::{InArena, NodeType, Trivia},
    source::FileId,
    State,
};

mod util;
pub mod ast_nodes {
    pub mod common;
    pub mod expressions;
    pub mod game;
    pub mod identifier;
    pub mod instances;
    pub mod list;
    pub mod oracles;
    pub mod package;
    pub mod statements;
    pub mod theorem;
    pub mod types;
}

// NOTE:
//   - This derive creates an enum `Rule`, which describes the grammar rules.
//   - we need all the other derives in order for the pest trait gymnastics to work.
#[derive(pest_derive::Parser, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[grammar = "../domino-ast/grammar/domino.pest"]
pub struct Domino;

type Pair<'i> = pest::iterators::Pair<'i, Rule>;

pub trait Parsable: NodeType + InArena {
    const RULE: Rule;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self;

    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Self::RULE);

        Self::parse_inner(file_id, state, pair)
    }

    fn parse_ref(file_id: FileId, state: &mut State, pair: crate::Pair) -> Ref<Self> {
        // NOTE: We need to trim trailing whitespace from the span here.
        let loc = util::trimmed_loc(file_id, &pair);

        let node = Self::parse(file_id, state, pair);

        Ref::<Self>::from_parsed(state, loc, node)
    }
}

pub trait ListItem {
    const LIST_RULE: Rule;
}

pub fn parse_ref<T: Parsable>(
    file_id: domino_ast::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
    f: fn(domino_ast::source::FileId, &mut crate::State, crate::Pair) -> T,
) -> Ref<T> {
    // NOTE: We need to trim trailing whitespace from the span here.
    let loc = util::trimmed_loc(file_id, &pair);
    let node = f(file_id, state, pair);
    Ref::<T>::from_parsed(state, loc, node)
}

impl Parsable for domino_ast::ast_nodes::Trivium {
    const RULE: Rule = Rule::trivium;

    fn parse_inner(_file_id: FileId, _state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::trivium);

        match pair.into_inner().next().unwrap().as_rule() {
            Rule::newline => domino_ast::ast_nodes::Trivium::NewLine,
            Rule::block_comment => domino_ast::ast_nodes::Trivium::BlockComment,
            Rule::line_comment => domino_ast::ast_nodes::Trivium::LineComment,
            _ => unreachable!(),
        }
    }
}

impl Parsable for Trivia {
    const RULE: Rule = Rule::gap;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::gap);

        let mut trivia = vec![];
        trivia.extend(pair.into_inner().map(|trivium_pair| {
            domino_ast::ast_nodes::Trivium::parse(file_id, state, trivium_pair)
        }));

        let mut allocator = state.arenas.trivium.slice_allocator();
        allocator.extend(trivia);

        Self {
            trivia: allocator.finish(),
        }
    }
}
