// SPDX-License-Identifier: MIT OR Apache-2.0

//! Talking to a live EasyCrypt (`docs/stories/easycrypt/26-easycrypt-session-and-alignment.md`).
//!
//! - [`json`]: the Rust mirror of `easycrypt cli -json`'s `domino-json/1` format.
//! - [`session`]: a running `easycrypt cli -json` process.
//! - [`skeleton`] and [`align`]: decision skeletons of EasyCrypt's program and of the
//!   lowering's IR, and their alignment (ADR 0002).
//! - [`check`]: `domino easycrypt --check-alignment`.

pub mod align;
pub mod check;
pub mod json;
pub mod session;
pub mod skeleton;
