// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::Display;

use super::{
    attribute::AttributeValue,
    tokens::{Binary, Decimal, Hexadecimal, Numeral, ReservedWord, StringLiteral, Symbol},
};

#[derive(Debug, Clone)]
pub enum SpecConstant {
    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(StringLiteral),
}

impl Display for SpecConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecConstant::Numeral(num) => num.fmt(f),
            SpecConstant::Decimal(dec) => dec.fmt(f),
            SpecConstant::Hexadecimal(hex) => hex.fmt(f),
            SpecConstant::Binary(bin) => bin.fmt(f),
            SpecConstant::String(s) => s.fmt(f),
        }
    }
}

impl SpecConstant {
    pub fn into_attribute_value(self) -> AttributeValue {
        AttributeValue::Const(self)
    }

    pub fn into_sexpr(self) -> SExpr {
        SExpr::Const(self)
    }
}

#[derive(Debug, Clone)]
pub enum SExpr {
    Const(SpecConstant),
    Symbol(Symbol),
    // TODO: Keyword(Keyword),
    SExpr(Vec<SExpr>),
    Reserved(ReservedWord),
    //HintNewline,
    HintComment(String),
}

impl<T: Into<SExpr>> FromIterator<T> for SExpr {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::SExpr(iter.into_iter().map(|v| v.into()).collect())
    }
}

macro_rules! impl_spec_const_from {
    ($name:ident) => {
        impl From<$name> for SpecConstant {
            fn from(value: $name) -> Self {
                Self::$name(value)
            }
        }

        impl From<$name> for SExpr {
            fn from(value: $name) -> Self {
                Self::Const(value.into())
            }
        }
    };

    ($variant:ident, $ty:ty) => {
        impl From<$ty> for SpecConstant {
            fn from(value: $ty) -> Self {
                Self::$variant(value)
            }
        }

        impl From<$ty> for SExpr {
            fn from(value: $ty) -> Self {
                Self::Const(value.into())
            }
        }
    };
}

impl_spec_const_from!(Numeral);
impl_spec_const_from!(Decimal);
impl_spec_const_from!(Hexadecimal);
impl_spec_const_from!(Binary);
impl_spec_const_from!(String, StringLiteral);

macro_rules! impl_s_expr_from {
    ($name:ident) => {
        impl From<$name> for SExpr {
            fn from(value: $name) -> Self {
                Self::$name(value)
            }
        }
    };

    ($variant:ident, $ty:ty) => {
        impl From<$ty> for SExpr {
            fn from(value: $ty) -> Self {
                Self::$variant(value)
            }
        }
    };
}

impl_s_expr_from!(Const, SpecConstant);
impl_s_expr_from!(Reserved, ReservedWord);
impl_s_expr_from!(Symbol);
impl_s_expr_from!(SExpr, Vec<SExpr>);
