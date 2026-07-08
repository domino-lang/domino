use crate::{arena::Ref, ast_nodes::NodeTypeEnum};

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

pub type LocationTable = GlobalTable<SourceLocation>;

/// A generic dense table: keeps a table `Ref<NodeType>` -> `Data`.
///
/// Uses the number in the [`Ref`] as an offset in a [`Vec`].
///
/// [`Ref`]: crate::arena::Ref
pub struct DenseTable<NodeType, Data>(Vec<Data>, PhantomData<NodeType>);

impl<K, V: Clone> DenseTable<K, Option<V>> {
    pub fn with_entries(size: usize) -> Self {
        Self(vec![None; size], PhantomData)
    }

    pub fn set(&mut self, key: Ref<K>, value: V) {
        *self.get_mut(key) = Some(value);
    }
}

impl<K, V> DenseTable<K, V> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity), PhantomData)
    }

    pub fn get(&self, key: Ref<K>) -> &V {
        &self.0[key.offset()]
    }

    pub fn get_mut(&mut self, key: Ref<K>) -> &mut V {
        &mut self.0[key.offset()]
    }

    pub fn as_slice(&self) -> &[V] {
        &self.0
    }
}

impl<K, V> From<Vec<V>> for DenseTable<K, V> {
    fn from(value: Vec<V>) -> Self {
        Self(value, PhantomData)
    }
}

#[derive(Default, Debug)]
pub struct Tables {
    pub locations: LocationTable,
}
