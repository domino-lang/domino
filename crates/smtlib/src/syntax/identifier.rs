// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    s_expr::SExpr,
    tokens::{Numeral, ReservedWord, Symbol},
};

#[derive(Debug, Clone)]
pub enum Index {
    Numeral(Numeral),
    Symbol(Symbol),
}

impl From<Index> for SExpr {
    fn from(value: Index) -> Self {
        match value {
            Index::Numeral(num) => num.into(),
            Index::Symbol(sym) => sym.into(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Identifier(pub Symbol, pub Vec<Index>);

impl<T: Into<Symbol>> From<T> for Identifier {
    fn from(value: T) -> Self {
        Identifier(value.into(), vec![])
    }
}

impl From<Identifier> for SExpr {
    fn from(value: Identifier) -> Self {
        if value.1.is_empty() {
            value.0.into()
        } else {
            SExpr::SExpr(
                Some(ReservedWord::Underscore.into())
                    .into_iter()
                    .chain(Some(value.0.into()))
                    .chain(value.1.into_iter().map(|index| index.into()))
                    .collect(),
            )
        }
    }
}
