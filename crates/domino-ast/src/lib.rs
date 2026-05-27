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

mod arena;
pub mod ast_nodes;
mod side_tables;
mod source;
mod state;

// NOTE:
//   - This derive creates an enum `Rule`, which describes the grammar rules.
//   - we need all the other derives in order for the pest trait gymnastics to work.
#[derive(pest_derive::Parser, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[grammar = "grammar/domino.pest"]
pub struct Domino;

type Pair<'i> = pest::iterators::Pair<'i, Rule>;
type Pairs<'i> = pest::iterators::Pairs<'i, Rule>;

pub use state::{Arenas, GlobalRefId, State};
