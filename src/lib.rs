#[macro_use]
extern crate pest_derive;

pub mod expressions;
pub mod format;
pub mod gamehops;
pub mod identifier;
pub mod package;
pub mod packageinstance;
pub mod split;
pub mod statement;
pub mod types;

pub mod transforms;
pub mod writers;

pub mod hacks;

pub mod parser;

pub mod testdata;

pub mod project;

pub mod util;

pub mod theorem;
pub mod ttheorem;

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
