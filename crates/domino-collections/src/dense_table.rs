//! In this module we define [`DenseTable`], a fully populated dense side table type.
//!
//! To create such a type, look to [`PartialDenseTable`].
//!
//! The structure of a [`DenseTable`] is a simple [`Vec`], where the offset stored in a [`Ref`]
//! (i.e. the offset in the [`Arena`]) is the same as the offset in the [`Vec`]. This allows O(1)
//! access, dense packing and therefore strong locality.
//!
//! The general idea here is to have a dense table that is a vec, indexed by the offset in the arena.
//! In order to build such a side table, we also provide a type that can have holes. We do that
//! using Option<V> as items in the vector.

use std::marker::PhantomData;

use crate::{arena::Ref, partial_dense_table::PartialDenseTable};

/// A generic dense table: keeps a table `Ref<K>` -> `V`.
///
/// Uses the number in the [`Ref`] as an offset in a [`Vec`].
///
/// [`Ref`]: crate::arena::Ref
#[derive(Debug, Clone)]
pub struct DenseTable<K, V>(Vec<V>, PhantomData<fn() -> K>);

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
