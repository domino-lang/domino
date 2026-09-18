//! This module implements an interner.
//!
//! Interners are similar to arenas, but when provided the same value, they will return the same
//! handle. This can make equivalence checks both easier and faster: When allocating in an interner
//! over an arena, it is enough to see that the IDs are equal. This means that a data structure
//! that uses interning IDs as references, we can just compare by value (since same value === same
//! reference).

use hashbrown::HashTable;
use std::marker::PhantomData;

#[derive(Debug)]
pub struct Interner<T, S = std::hash::RandomState> {
    items: Vec<T>,
    table: HashTable<Id<T>>,
    hasher: S,
}

fn get<T>(items: &[T], id: Id<T>) -> &T {
    &items[id.offset()]
}

impl<T: Eq + core::hash::Hash + Clone, S: core::hash::BuildHasher> Interner<T, S> {
    pub fn intern(&mut self, v: T) -> Id<T> {
        let hash = self.hasher.hash_one(&v);
        if let Some(id) = self.table.find(hash, |id| v == *get(&self.items, *id)) {
            return *id;
        }

        let id = Id::new(self.current_offset());

        self.items.push(v);
        self.table
            .insert_unique(hash, id, |id| self.hasher.hash_one(get(&self.items, *id)));

        id
    }

    pub fn get(&self, id: Id<T>) -> &T {
        &self.items[id.offset()]
    }

    fn current_offset(&self) -> u32 {
        self.items
            .len()
            .try_into()
            .expect("tried to intern one too many")
    }
}

#[derive(Debug)]
pub struct Id<T>(u32, PhantomData<T>);

impl<T> Id<T> {
    fn new(offset: u32) -> Self {
        Self(offset, PhantomData)
    }

    pub fn offset(self) -> usize {
        self.0 as usize
    }
}

// explicit impls so they are more general than what could be derived

impl<T> Default for Interner<T> {
    fn default() -> Self {
        Self {
            items: Default::default(),
            table: Default::default(),
            hasher: Default::default(),
        }
    }
}

impl<T> Eq for Id<T> {}
impl<T> PartialEq for Id<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Copy for Id<T> {}
impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> core::hash::Hash for Id<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
