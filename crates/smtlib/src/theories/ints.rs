// SPDX-License-Identifier: MIT OR Apache-2.0

//! https://smt-lib.org/theories-Ints.shtml

use crate::syntax::{sort::Sort, term::Term, tokens::Symbol};

pub enum Symbols {
    Int,
    Minus,
    Plus,
    Asterisk,
    Div,
    Mod,
    Abs,
    Lte,
    Lt,
    Gte,
    Gt,
}

impl From<Symbols> for Symbol {
    fn from(value: Symbols) -> Symbol {
        match value {
            Symbols::Int => "Int",
            Symbols::Minus => "-",
            Symbols::Plus => "+",
            Symbols::Asterisk => "*",
            Symbols::Div => "div",
            Symbols::Mod => "mod",
            Symbols::Abs => "abs",
            Symbols::Lte => "<=",
            Symbols::Lt => "<",
            Symbols::Gte => ">=",
            Symbols::Gt => ">",
        }
        .into()
    }
}

pub fn int() -> Sort {
    Sort {
        name: Symbols::Int.into(),
        parameters: vec![],
    }
}

use super::def_fun_assoc;
use super::def_fun_plain;

def_fun_assoc!(add, Symbols::Plus);
def_fun_assoc!(sub, Symbols::Minus);
def_fun_assoc!(mul, Symbols::Asterisk);
def_fun_assoc!(div, Symbols::Div);

def_fun_plain!(negate, Symbols::Minus, (term));
def_fun_plain!(modulo, Symbols::Mod, (lhs, rhs));
def_fun_plain!(abs, Symbols::Abs, (term));
def_fun_plain!(lte, Symbols::Lte, (lhs, rhs));
def_fun_plain!(lt, Symbols::Lt, (lhs, rhs));
def_fun_plain!(gte, Symbols::Gte, (lhs, rhs));
def_fun_plain!(gt, Symbols::Gt, (lhs, rhs));
