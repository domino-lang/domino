//! In this crate we define side table types that work best when the items in the arenas are already
//! all allocated.
//!
//! The general idea here is to have a dense table that is a vec, indexed by the offset in the arena.
//! In order to build such a side table, we also provide a type that can have holes. We do that
//! using Option<V> as items in the vector.

use std::marker::PhantomData;

use crate::arena::Ref;

/// A generic dense table: keeps a table `Ref<K>` -> `V`.
///
/// Uses the number in the [`Ref`] as an offset in a [`Vec`].
///
/// [`Ref`]: crate::arena::Ref
#[derive(Debug, Clone)]
pub struct DenseTable<K, V>(Vec<V>, PhantomData<fn() -> K>);

#[derive(Debug, Clone)]
pub struct PartialDenseTable<K, V>(Vec<Option<V>>, PhantomData<fn() -> K>);

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

    pub fn missing<'a>(&'a self) -> impl Iterator<Item = Ref<K>> + 'a {
        self.iter().filter_map(|(r, v)| v.is_none().then_some(r))
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

// impls for Iterator an IntoIterator
//
// Here, we often create [`Ref`]s in a maybe surprising way. But note that we use Ref<T> as the key,
// and the offset of the value in our inner Vec is the same as the offset of the item the key refers
// to in the arena.

impl<K, V> DenseTable<K, V> {
    pub fn iter(&self) -> impl Iterator<Item = (Ref<K>, &V)> {
        self.as_slice()
            .iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<K, V> IntoIterator for DenseTable<K, V> {
    type Item = (Ref<K>, V);

    type IntoIter =
        std::iter::Map<std::iter::Enumerate<std::vec::IntoIter<V>>, fn((usize, V)) -> (Ref<K>, V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec()
            .into_iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<K, V> PartialDenseTable<K, V> {
    pub fn iter(&self) -> impl Iterator<Item = (Ref<K>, &Option<V>)> {
        self.as_slice()
            .iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<K, V> IntoIterator for PartialDenseTable<K, V> {
    type Item = (Ref<K>, Option<V>);

    type IntoIter = std::iter::Map<
        std::iter::Enumerate<std::vec::IntoIter<Option<V>>>,
        fn((usize, Option<V>)) -> (Ref<K>, Option<V>),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec()
            .into_iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}
