// SPDX-License-Identifier: MIT OR Apache-2.0

//! Proving the invariants a package declares.
//!
//! A package invariant is a property of the state of a single package. It is used as an assumption
//! when proving equivalences, so it needs to be established separately -- by induction over the
//! oracle calls the package offers:
//!
//!  * *invariant start*: the invariant holds in the initial state of the package, and
//!  * *one claim per oracle*: if the invariant holds before a call to that oracle, and the call
//!    does not abort, then it holds afterwards.
//!
//! This is done once per package, for arbitrary package constants, against the synthetic game
//! built in [`virtualgame`]. That implies the property we need in every game the package is used
//! in: whatever an exported oracle of a game does, it can only touch the package's state by
//! calling the package's own oracles.

pub mod error;

mod context;
mod verify;
mod virtualgame;

pub(crate) use context::PackageInvariantContext;
pub(crate) use verify::{PackageInvariantSmtDriver, UI_SECTION_NAME};
pub(crate) use virtualgame::VirtualGame;
