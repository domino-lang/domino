// SPDX-License-Identifier: MIT OR Apache-2.0

//! Support code for the symbolic-execution proof debugger (`domino debug` /
//! `domino inline`).
//!
//! [`ir`] holds the AST-level inlined representation of one exported oracle,
//! together with the textual listing its line-number labels index into.

pub mod driver;
pub mod exec;
pub mod ir;
pub mod render;
