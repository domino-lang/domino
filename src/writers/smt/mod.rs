// SPDX-License-Identifier: MIT OR Apache-2.0

pub mod exprs;
pub mod writer;

pub mod expr_expr;
mod expr_term;

pub mod contexts;
pub mod declare;
pub mod identifier;
pub mod names;
//pub mod partials;
pub mod patterns;
pub mod sorts;

#[cfg(test)]
mod tests;
