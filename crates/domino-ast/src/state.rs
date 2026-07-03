use crate::ast_nodes::NodeTypeEnum;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct GlobalRefId(pub NodeTypeEnum, pub u32);

#[derive(Default, Debug)]
pub struct State {
    pub arenas: crate::Arenas,
    pub tables: Tables,
    pub parse_context: ParseContext,
}

#[derive(Default, Debug)]
pub struct ParseContext {
    pub trivia: TriviaParseContext,
}

#[derive(Default, Debug)]
pub struct TriviaParseContext {
    pub newlines_span_start: Option<u32>,
}

use std::{collections::HashMap, marker::PhantomData};

use crate::source::SourceLocation;

/// A generic sparse table that can have any node as key.
pub type GlobalTable<T> = HashMap<GlobalRefId, T>;

/// A generic dense table: keeps a table `Ref<NodeType>` -> `Data`.
///
/// Uses the number in the [`Ref`] as an offset in a [`Vec`].
///
/// [`Ref`]: crate::arena::Ref
pub struct DenseTable<NodeType, Data>(Vec<Data>, PhantomData<NodeType>);

#[derive(Default, Debug)]
pub struct Tables {
    pub locations: GlobalTable<SourceLocation>,
}
