//! In this module we define [`GrowingTable`], a partialy populated dense side table type.
//! It is initialized with an empty vector, and must be populated alongside the matching [`Arena`].
//!
//! Once the arena is fully populated, the type can be converted into a regular [`DenseTable`] using
//! [`GrowingTable::finish`].
//!
//! Use this for building a side table while parsing, e.g. to capture source spans/locations.
//!
//! [`Arena`]: crate::arena::Arena
use std::marker::PhantomData;

use crate::{arena::Ref, dense_table::DenseTable};

/// A table that grows alongside the respective arena.
#[derive(Debug, Clone)]
pub struct GrowingTable<K, V>(Vec<V>, PhantomData<fn() -> K>);

impl<K, V> GrowingTable<K, V> {
    pub fn push_next(&mut self, r: Ref<K>, data: V) {
        debug_assert_eq!(r.offset(), self.0.len());

        self.0.push(data);
    }

    pub fn get(&self, r: Ref<K>) -> &V {
        &self.0[r.offset()]
    }

    pub fn finish(self) -> DenseTable<K, V> {
        self.0.into()
    }
}

impl<K, V> Default for GrowingTable<K, V> {
    fn default() -> Self {
        Self(Default::default(), Default::default())
    }
}
