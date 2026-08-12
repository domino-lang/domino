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
#[derive(Debug, Clone)]
pub struct DenseTable<NodeType, Data>(Vec<Data>, PhantomData<fn() -> NodeType>);

#[derive(Debug, Clone)]
pub struct PartialDenseTable<NodeType, Data>(Vec<Option<Data>>, PhantomData<fn() -> NodeType>);

impl<K, V> PartialDenseTable<K, V> {
    pub fn with_entries(size: usize) -> Self {
        let mut list = Vec::with_capacity(size);
        list.resize_with(size, || None);

        Self(list, PhantomData)
    }

    pub fn get(&self, key: Ref<K>) -> &Option<V> {
        &self.0[key.offset()]
    }

    pub fn get_mut(&mut self, key: Ref<K>) -> &mut Option<V> {
        &mut self.0[key.offset()]
    }

    pub fn set(&mut self, key: Ref<K>, value: V) {
        *self.get_mut(key) = Some(value);
    }

    pub fn as_slice(&self) -> &[Option<V>] {
        &self.0
    }

    pub fn into_vec(self) -> Vec<Option<V>> {
        self.0
    }
}

impl<K, V> PartialDenseTable<K, V> {
    pub fn finish(self) -> Result<DenseTable<K, V>, Ref<K>> {
        let list = self
            .into_iter()
            .map(|(r, maybe)| match maybe {
                Some(elem) => Ok(elem),
                None => Err(r),
            })
            .collect::<Result<Vec<_>, Ref<K>>>()?;

        Ok(DenseTable(list, PhantomData))
    }
}

impl<K: crate::ast_nodes::InArena, V> PartialDenseTable<K, V> {
    pub fn with_sizes_from_arena(arenas: &crate::Arenas) -> Self {
        Self::with_entries(K::arena(arenas).len())
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

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn into_vec(self) -> Vec<V> {
        self.0
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
