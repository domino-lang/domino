// SPDX-License-Identifier: MIT OR Apache-2.0

//!  https://smt-lib.org/theories-ArrayEx.shtml

use crate::syntax::{
    sort::Sort,
    term::{QualifiedIdentifier, Term},
    tokens::Symbol,
};

pub enum Symbols {
    Array,
    Select,
    Store,
    Const,
}

impl From<Symbols> for Symbol {
    fn from(value: Symbols) -> Self {
        match value {
            Symbols::Array => "Array",
            Symbols::Select => "select",
            Symbols::Store => "store",
            Symbols::Const => "const",
        }
        .into()
    }
}

pub fn array(key: impl Into<Sort>, value: impl Into<Sort>) -> Sort {
    Sort {
        name: Symbols::Array.into(),
        parameters: vec![key.into(), value.into()],
    }
}

super::def_fun_plain!(select, Symbols::Select, (array, index));
super::def_fun_plain!(store, Symbols::Select, (array, index, value));

pub fn const_(key: impl Into<Sort>, value: impl Into<Sort>, base_term: Term) -> Term {
    Term::Base(
        QualifiedIdentifier(Symbols::Const.into(), Some(array(key, value))),
        vec![base_term],
    )
}
