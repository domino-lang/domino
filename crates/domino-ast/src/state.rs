use crate::{arena::Ref, ast_nodes::InArena};

#[derive(Debug)]
pub struct State {
    pub arenas: crate::Arenas,
    pub tables: Tables,
    pub parse_context: ParseContext,
}

impl Default for State {
    fn default() -> Self {
        Self {
            arenas: Default::default(),
            tables: Default::default(),
            parse_context: Default::default(),
        }
    }
}

#[derive(Default, Debug)]
pub struct ParseContext {
    pub trivia: TriviaParseContext,
}

#[derive(Default, Debug)]
pub struct TriviaParseContext {
    pub newlines_span_start: Option<u32>,
}

use std::marker::PhantomData;

use crate::source::SourceLocation;

#[derive(Default, Debug, Clone)]
pub struct LocationTable(crate::ast_nodes::GrowingTables<SourceLocation>);

impl LocationTable {
    pub fn insert<T: InArena>(&mut self, r: Ref<T>, loc: SourceLocation) {
        self.0.insert(r, loc)
    }

    pub fn get<T: InArena>(&self, r: Ref<T>) -> SourceLocation {
        *self.0.get(r)
    }
}

/// A table that grows alongside the respective arena.
#[derive(Debug, Clone)]
pub struct GrowingTable<NodeType, Data>(Vec<Data>, PhantomData<fn() -> NodeType>);

impl<NodeType, Data> GrowingTable<NodeType, Data> {
    pub fn push_next(&mut self, r: Ref<NodeType>, data: Data) {
        debug_assert_eq!(r.offset(), self.0.len());

        self.0.push(data);
    }

    pub fn get<T: InArena>(&self, r: Ref<T>) -> &Data {
        &self.0[r.offset()]
    }
}
impl<NodeType, Data> Default for GrowingTable<NodeType, Data> {
    fn default() -> Self {
        Self(Default::default(), Default::default())
    }
}

#[derive(Debug)]
pub struct Tables {
    pub locations: LocationTable,
}

impl Default for Tables {
    fn default() -> Self {
        Self {
            locations: Default::default(),
        }
    }
}
