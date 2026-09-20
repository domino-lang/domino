//! This module implements an interner for lists.
//!
//! Interners are similar to arenas, but when provided the same list, they will return the same
//! handle. This can make equivalence checks both easier and faster: When allocating in an interner
//! over an arena, it is enough to see that the IDs are equal. This means that a data structure
//! that uses interning IDs as references, we can just compare by value (since same value === same
//! reference).

use hashbrown::HashTable;
use std::{
    hash::{BuildHasher, Hash, Hasher},
    marker::PhantomData,
    ops::Range,
};

#[derive(Debug)]
pub struct ListInterner<T, S = std::hash::RandomState> {
    items: Vec<T>,
    table: HashTable<ListId<T>>,
    hasher: S,
}

fn get_list<T>(items: &[T], id: ListId<T>) -> &[T] {
    &items[id.range()]
}

fn hash_list(v: &[impl Hash], build_hasher: &impl BuildHasher) -> u64 {
    let mut hasher = build_hasher.build_hasher();
    v.hash(&mut hasher);
    hasher.finish()
}

impl<T: Eq + core::hash::Hash + Clone, S: core::hash::BuildHasher> ListInterner<T, S> {
    pub fn intern(&mut self, items: &[T]) -> ListId<T> {
        let hash = hash_list(items, &self.hasher);
        if let Some(id) = self
            .table
            .find(hash, |id| items == get_list(&self.items, *id))
        {
            return *id;
        }

        let id = ListId::new(self.current_offset(), items.len() as u32);

        self.items.extend(items.iter().cloned());
        self.table.insert_unique(hash, id, |id| {
            hash_list(get_list(&self.items, *id), &self.hasher)
        });

        id
    }

    pub fn get(&self, id: ListId<T>) -> &[T] {
        &self.items[id.range()]
    }

    fn current_offset(&self) -> u32 {
        self.items
            .len()
            .try_into()
            .expect("tried to intern one too many")
    }
}

#[derive(Debug)]
pub struct ListId<T> {
    base_offset: u32,
    len: u32,
    _marker: PhantomData<T>,
}

impl<T> ListId<T> {
    fn new(base_offset: u32, len: u32) -> Self {
        Self {
            base_offset,
            len,
            _marker: PhantomData,
        }
    }

    pub fn base_offset(self) -> usize {
        self.base_offset as usize
    }

    pub fn len(self) -> usize {
        self.len as usize
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    fn range(self) -> Range<usize> {
        self.base_offset()..(self.base_offset() + self.len())
    }
}

// explicit impls so they are more general than what could be derived

impl<T> Default for ListInterner<T> {
    fn default() -> Self {
        Self {
            items: Default::default(),
            table: Default::default(),
            hasher: Default::default(),
        }
    }
}

impl<T> Eq for ListId<T> {}
impl<T> PartialEq for ListId<T> {
    fn eq(&self, other: &Self) -> bool {
        self.base_offset == other.base_offset && self.len == other.len
    }
}

impl<T> Copy for ListId<T> {}
impl<T> Clone for ListId<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> core::hash::Hash for ListId<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.base_offset.hash(state);
        self.len.hash(state);
    }
}
