// SPDX-License-Identifier: MIT OR Apache-2.0

//! Support code for the symbolic-execution proof debugger (`domino debug` /
//! `domino inline`).
//!
//! [`ir`] holds the AST-level inlined representation of one exported oracle,
//! together with the textual listing its line-number labels index into.

pub mod driver;
pub mod effect;
pub mod exec;
pub mod ir;
pub mod lockstep;
pub mod lockstep_report;
pub mod lockstep_run;
pub mod lockstep_viewer;
pub mod progress;
pub mod render;
pub mod report;
pub mod smtout;

#[cfg(test)]
mod easycryptify_differential;
