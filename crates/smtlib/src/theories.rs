// SPDX-License-Identifier: MIT OR Apache-2.0

macro_rules! def_fun_assoc {
    ($name:ident, $sym:expr) => {
        pub fn $name<T: Into<Term>, I: IntoIterator<Item = T>>(terms: I) -> Term {
            let terms = terms.into_iter().map(|term| term.into());
            Term::Base($sym.into(), terms.collect())
        }
    };
}

macro_rules! def_fun_plain {
    ($name:ident, $sym:expr, ($($args:ident),*)) => {
        pub fn $name($($args: impl Into<Term>),*) -> Term {
            Term::Base($sym.into(), vec![$($args.into()),*])
        }
    };
}

use def_fun_assoc;
use def_fun_plain;

pub mod array_ex;
pub mod core;
pub mod ints;
