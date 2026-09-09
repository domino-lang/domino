use std::borrow::Borrow;

use domino_collections::{arena::Ref, partial_dense_table::PartialDenseTable};

use crate::{
    ast_nodes::{Arenas, DenseTables, GrowingTables},
    source::SourceLocation,
    InArena,
};

#[derive(Debug)]
pub struct State {
    pub arenas: crate::Arenas,
    pub tables: Tables,
}

impl Default for State {
    fn default() -> Self {
        Self {
            arenas: Default::default(),
            tables: Default::default(),
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct LocationTable(crate::ast_nodes::GrowingTables<SourceLocation>);

impl LocationTable {
    pub fn push_next<T: InArena>(&mut self, r: Ref<T>, loc: SourceLocation) {
        self.0.push_next(r, loc)
    }

    pub fn get<T: InArena>(&self, r: Ref<T>) -> SourceLocation {
        *self.0.get(r)
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

impl Arenas {
    /// Returns a reference for the given [`Ref`] of a type that has an [`Arena`] in [`Arenas`].
    ///
    /// [`Arena`]: domino_collections::arena::Arena
    pub fn get<T: InArena, R: Borrow<Ref<T>>>(&self, r: R) -> &T {
        T::arena(self).get(*r.borrow())
    }

    /// Returns a new [`PartialDenseTable`] that has the correct number of entries, based on the
    /// number of entries in each [`Arena`] in [`Arenas`]. Should only be called once the arenas are
    /// fully populated.
    ///
    /// [`Arena`]: domino_collections::arena::Arena
    pub fn new_partial_dense_table<K: InArena, V>(&self) -> PartialDenseTable<K, V> {
        PartialDenseTable::with_entries(K::arena(self).len())
    }
}

impl<T> GrowingTables<T> {
    pub fn push_next<K: InArena>(&mut self, r: Ref<K>, v: T) {
        K::growing_table_mut(self).push_next(r, v);
    }

    pub fn get<'a, K: InArena + 'a>(&'a self, r: Ref<K>) -> &'a T {
        K::growing_table(self).get(r)
    }
}

impl<T> DenseTables<T> {
    pub fn get<'a, K: InArena + 'a>(&'a self, r: Ref<K>) -> &'a T {
        K::dense_table(self).get(r)
    }
}
