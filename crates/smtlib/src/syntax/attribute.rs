// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    s_expr::{SExpr, SpecConstant},
    tokens::{Keyword, Symbol},
};

#[derive(Debug, Clone)]
pub enum AttributeValue {
    Const(SpecConstant),
    Symbol(Symbol),
    SExpr(Vec<SExpr>),
}

#[derive(Debug, Clone)]
pub struct Attribute(pub Keyword, pub Option<AttributeValue>);

impl From<AttributeValue> for SExpr {
    fn from(value: AttributeValue) -> Self {
        match value {
            AttributeValue::Const(con) => con.into(),
            AttributeValue::Symbol(sym) => sym.into(),
            AttributeValue::SExpr(exprs) => SExpr::SExpr(exprs),
        }
    }
}
