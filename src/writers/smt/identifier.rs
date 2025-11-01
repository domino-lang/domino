// SPDX-License-Identifier: MIT OR Apache-2.0

use sspverif_smtlib::syntax::term::Term;

use crate::identifier::Identifier;

use super::exprs::SmtExpr;

impl Identifier {
    /// returns the string used as the identifier in SMT-LIB code
    pub(crate) fn smt_identifier_string(&self) -> String {
        match self {
            Identifier::Generated(name, _) => format!("<{name}>"),
            other => other.ident(),
        }
    }
}

impl From<Identifier> for SmtExpr {
    fn from(value: Identifier) -> Self {
        value.smt_identifier_string().into()
    }
}

impl From<Identifier> for Term {
    fn from(value: Identifier) -> Self {
        value.smt_identifier_string().into()
    }
}
