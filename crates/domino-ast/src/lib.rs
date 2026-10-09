//! This module implements a new parser for Domino.
//!
//! The main goals are:
//! - Reduce the number of Option<_> in the AST nodes to near zero by having more specific types
//! - Carry spans through all phases so we can produce good error values
//!
//!
//! General Structure:
//! - store file contents and paths in a bumpalo arena
//! - have very light per-AST-node arenas (just Vec, Refs are 32bit)
//! - have side tables for resolution
//!
//!

// We are doing a lot of generic type aliases that need bounds, and we don't care that the error is
// shown at the type use place instead of at the type alias definition.
#![allow(type_alias_bounds)]

use domino_collections::{
    arena::{Arena, Ref},
    dense_table::DenseTable,
    growing_table::GrowingTable,
};

// module definitions

pub mod ast_nodes;
pub mod source;
mod state;
pub mod walk;

// re-exports

pub use ast_nodes::{Arenas, GlobalRefId, Visitor};
pub use state::{LocationTable, State, Tables};

use ast_nodes::{GrowingTables, NodeTypeEnum};
use source::SourceLocation;

use crate::ast_nodes::DenseTables;

/// A node type.
pub trait NodeType: Sized {
    const NODE_TYPE: NodeTypeEnum;
    fn global_ref_id(r: Ref<Self>) -> GlobalRefId;
}

/// A [`Ref`] for an [`Arena`] containing a [`NodeType`].
pub trait NodeTypeRef {
    /// The [`NodeType`] that the [`Ref`] points to.
    type Type: NodeType + InArena;

    /// Allocates a parsed AST node in its [`Arena`], stores the location and returns the [`Ref`].
    fn from_parsed(state: &mut State, loc: SourceLocation, node: Self::Type) -> Self;

    /// Returns the [`GlobalRefId`] for this [`Ref`].
    fn global_ref_id(self) -> GlobalRefId;
}

impl<T: NodeType + InArena> NodeTypeRef for Ref<T> {
    type Type = T;
    fn from_parsed(state: &mut State, loc: SourceLocation, node: T) -> Self {
        let arena = T::arena_mut(&mut state.arenas);
        let id = arena.alloc(node);

        state.tables.locations.push_next(id, loc);

        id
    }

    fn global_ref_id(self) -> GlobalRefId {
        Self::Type::global_ref_id(self)
    }
}

/// Implemented by types that have an [`Arena`] in our macro-generated [`Arenas`] struct.
/// The implementations of this trait are generated the same way.
///
/// Note that it's not just [`Arenas`] that holds spots for these: The types holding side tables
/// for all AST nodes [`GrowingTables`] and [`DenseTables`] can be accessed this way, too.
///
/// [`Arena`]: domino_collections::arena::Arena
// TODO: add PartialDenseTables
// TODO: maybe move to state module?
pub trait InArena: Sized {
    /// Returns an immutable borrow to the arena for that type
    fn arena(arenas: &Arenas) -> &Arena<Self>;
    /// Returns a mutable borrow to the arena for that type
    fn arena_mut(arenas: &mut Arenas) -> &mut Arena<Self>;

    /// Returns an immutable borrow to the growing table for that type
    fn growing_table<T>(growing_tables: &GrowingTables<T>) -> &GrowingTable<Self, T>;
    /// Returns a mutable borrow to the growing table for that type
    fn growing_table_mut<T>(growing_tables: &mut GrowingTables<T>) -> &mut GrowingTable<Self, T>;

    /// Returns an immutable borrow to the dense table for that type
    fn dense_table<T>(dense_tables: &DenseTables<T>) -> &DenseTable<Self, T>;
    /// Returns a mutable borrow to the dense table for that type
    fn dense_table_mut<T>(dense_tables: &mut DenseTables<T>) -> &mut DenseTable<Self, T>;
}

/// This trait is implemented by all types that are visitable, i.e. where the [`Visitor`] trait has
/// a method for.
pub trait Visit: Sized {
    /// Makes `visitor` visit the AST node `node`.
    fn visit<'a, V: Visitor<'a> + ?Sized>(
        visitor: &mut V,
        arenas: &'a crate::Arenas,
        node: domino_collections::arena::Ref<Self>,
    );
}
