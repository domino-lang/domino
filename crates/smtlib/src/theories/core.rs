// SPDX-License-Identifier: MIT OR Apache-2.0

//!  https://smt-lib.org/theories-Core.shtml

use crate::syntax::{sort::Sort, term::Term, tokens::Symbol};

pub enum Symbols {
    Bool,
    True,
    False,
    Not,
    Implies,
    And,
    Or,
    Xor,
    Eq,
    Distinct,
    Ite,
}

impl From<Symbols> for Symbol {
    fn from(value: Symbols) -> Symbol {
        match value {
            Symbols::Bool => "Bool",
            Symbols::True => "true",
            Symbols::False => "false",
            Symbols::Not => "not",
            Symbols::Implies => "=>",
            Symbols::And => "and",
            Symbols::Or => "or",
            Symbols::Xor => "xor",
            Symbols::Eq => "=",
            Symbols::Distinct => "distinct",
            Symbols::Ite => "ite",
        }
        .into()
    }
}

pub fn bool_() -> Sort {
    Sort {
        name: Symbols::Bool.into(),
        parameters: vec![],
    }
}

use super::def_fun_assoc;
use super::def_fun_plain;

def_fun_plain!(true_, Symbols::True, ());
def_fun_plain!(false_, Symbols::False, ());
def_fun_plain!(not, Symbols::Not, (term));
def_fun_plain!(ite, Symbols::Ite, (cond, then, els));

def_fun_assoc!(implies, Symbols::Not);
def_fun_assoc!(and, Symbols::And);
def_fun_assoc!(or, Symbols::Or);
def_fun_assoc!(xor, Symbols::Xor);
def_fun_assoc!(eq, Symbols::Eq);
def_fun_assoc!(distinct, Symbols::Distinct);
