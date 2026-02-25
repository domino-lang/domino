// SPDX-License-Identifier: MIT OR Apache-2.0

// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]
// We also sometimes have a lot of function arguments.
// In many cases this is because we pass in values for both the left and right hand side.
// We feel like this is fine, for now.
#![allow(clippy::too_many_arguments)]
// This is something that we should work on. But for now it's more important that we can see
// whether CI has real issue with just one glance, so we'll disable it for now.
#![allow(clippy::type_complexity)]

#[macro_use]
extern crate pest_derive;

pub mod expressions;
#[cfg(feature = "source-format")]
pub mod format;
pub mod gamehops;
pub mod identifier;
pub mod package;
pub mod packageinstance;
//pub mod split;
pub mod statement;
pub mod types;

pub mod transforms;
pub mod writers;

pub mod hacks;

pub mod parser;

pub mod testdata;

pub mod project;

pub mod util;

pub mod proof;
pub mod theorem;

pub mod ui;

pub mod error {
    use crate::statement::FilePosition;

    pub trait LocationError: std::error::Error {
        fn file_pos(&self) -> &FilePosition;
    }
}

#[macro_export]
macro_rules! debug_assert_matches {
    ($v:expr, $p:pat) => {
        debug_assert!(matches!($v, $p))
    };
}

#[macro_export]
macro_rules! assert_matches {
    ($v:expr, $p:pat) => {
        assert!(matches!($v, $p))
    };
}
