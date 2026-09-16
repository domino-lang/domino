// SPDX-License-Identifier: MIT OR Apache-2.0

//! EasyCrypt export: an AST that models EasyCrypt syntax
//! ([`ast`]), a total renderer from that AST to text ([`render`]), and
//! deterministic identifier mangling ([`names`]).
//!
//! This module has no dependency on Domino's own types — later stories in
//! the `easycrypt` export epic translate Domino into this AST.

pub mod ast;
pub mod names;
pub mod render;

#[cfg(test)]
mod tests;
