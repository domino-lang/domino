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

pub mod arena;
pub mod ast_nodes;
pub mod source;
mod state;

pub use ast_nodes::{Arenas, Visitor};
pub use state::{
    DenseTable, GlobalRefId, GlobalTable, LocationTable, PartialDenseTable, State, Tables,
};
