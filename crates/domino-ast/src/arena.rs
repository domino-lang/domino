//! This module defines a very simple arena: It's just a Vec.
//!
//! This has a few implications:
//! - each type needs a separate arena
//! - the references are just offsets into the arena
//! - these offsets are also used as typed node ids to index side tables. Since they are dense, we
//!   can use a vec, where the index just is the offset.
//!
//! As an optimization, we generally assume we never have more than u32::MAX entries in an arena.
//! That way we can use u32 for the offsets.

use std::{fmt::Debug, marker::PhantomData};

use crate::{
    ast_nodes::NodeType,
    source::{SourceFile, SourceLocation},
    GlobalRefId,
};

/// An arena for values of type T.
///
/// In order for the lookup type safety to hold, there may only be one arena for any type.
#[derive(Debug)]
pub struct Arena<T>(Vec<T>);

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

/// A reference to an arena entry of type T.
///
/// The generic argument provides some type safety when looking up values in an arena.
// PhantomData<fn() -> T> tags us with T for type safety without acting like we own a T:
// it keeps Ref covariant in T but stays Send + Sync regardless of whether T is.
pub struct Ref<T>(u32, PhantomData<fn() -> T>);

impl<T> core::fmt::Debug for Ref<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Ref").field(&self.0).finish()
    }
}

impl<T> Clone for Ref<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Ref<T> {}
impl<T> Ref<T> {
    pub fn offset(&self) -> usize {
        self.0 as usize
    }
}

impl<T: NodeType> Ref<T> {
    pub const fn global_ref_id(self) -> GlobalRefId {
        GlobalRefId(T::NODE_TYPE, self.0)
    }
}

/// A reference to an arena slice of type T.
///
/// The generic argument provides some type safety when looking up values in an arena.
// PhantomData<fn() -> T> tags us with T for type safety without acting like we own a T:
// it keeps Slice covariant in T but stays Send + Sync regardless of whether T is.
pub struct Slice<T>(u32, u32, PhantomData<fn() -> T>);

impl<T> Clone for Slice<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Slice<T> {}
impl<T> core::fmt::Debug for Slice<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Slice")
            .field(&self.0)
            .field(&self.1)
            .field(&self.2)
            .finish()
    }
}

impl<T> Slice<T> {
    pub fn empty() -> Self {
        Slice(0, 0, PhantomData)
    }

    pub fn len(self) -> usize {
        self.1 as usize
    }

    pub fn refs(self) -> impl Iterator<Item = Ref<T>> {
        (self.0..(self.0 + self.1)).map(|i| Ref(i, PhantomData))
    }
}

impl<T> Arena<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    pub fn alloc(&mut self, value: T) -> Ref<T> {
        let offset = self.current_offset();

        self.0.push(value);
        Ref(offset, PhantomData)
    }

    pub fn slice_allocator<'a>(&'a mut self) -> SliceAllocator<'a, T> {
        let base = self.current_offset();

        SliceAllocator {
            arena: self,
            base,
            count: 0,
        }
    }

    pub fn get(&self, reference: Ref<T>) -> &T {
        &self.0[reference.0 as usize]
    }

    pub fn get_slice(&self, slice: Slice<T>) -> &[T] {
        &self.0[slice.0 as usize..(slice.0 + slice.1) as usize]
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    fn current_offset(&self) -> u32 {
        self.0
            .len()
            .try_into()
            .expect("tried to alloc one too many")
    }
}

impl<T> FromIterator<T> for Arena<T> {
    fn from_iter<II: IntoIterator<Item = T>>(iter: II) -> Self {
        Self(Vec::from_iter(iter))
    }
}

pub struct SliceAllocator<'a, T> {
    arena: &'a mut Arena<T>,
    base: u32,
    count: u32,
}

impl<'a, T> SliceAllocator<'a, T> {
    pub fn push(&mut self, value: T) -> Ref<T> {
        let ref_ = self.arena.alloc(value);
        self.count += 1;
        ref_
    }

    pub fn finish(self) -> Slice<T> {
        Slice(self.base, self.count, PhantomData)
    }
}

impl<'a, I> Extend<I> for SliceAllocator<'a, I> {
    fn extend<T: IntoIterator<Item = I>>(&mut self, iter: T) {
        for item in iter {
            self.push(item);
        }
    }
}

impl Arena<SourceFile> {
    pub fn text(&self, loc: SourceLocation) -> &str {
        &self.get(loc.file_id).contents[(loc.start as usize)..(loc.end as usize)]
    }
}
