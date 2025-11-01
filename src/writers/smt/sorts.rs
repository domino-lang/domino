// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::types::Type;

use super::exprs::SmtExpr;

use sspverif_smtlib::syntax::sort::Sort as SmtlibSort;
use sspverif_smtlib::theories;

impl From<Sort> for SmtlibSort {
    fn from(value: Sort) -> Self {
        match value {
            Sort::Int => theories::ints::int(),
            Sort::Bool => theories::core::bool_(),
            Sort::String => "String".into(),
            Sort::Array(params) => SmtlibSort {
                name: "Array".into(),
                parameters: vec![params.0.into(), params.1.into()],
            },
            Sort::Parameter(name) => name.into(),
            Sort::Other(name, params) => SmtlibSort {
                name: name.into(),
                parameters: params.into_iter().map(|sort| sort.into()).collect(),
            },
        }
    }
}

impl From<&Type> for SmtlibSort {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Integer => theories::ints::int(),
            Type::String => "String".into(),
            Type::Boolean => theories::core::bool_(),
            Type::Bits(length) => {
                let length = match &**length {
                    crate::types::CountSpec::Identifier(identifier) => identifier.ident(),
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                };
                format!("Bits_{length}").into()
            }
            Type::Table(ty_idx, ty_val) => SmtlibSort {
                name: "Array".into(),
                parameters: vec![
                    (**ty_idx).clone().into(),
                    Type::Maybe((*ty_val).clone()).into(),
                ],
            },
            Type::Maybe(ty) => SmtlibSort {
                name: "Maybe".into(),
                parameters: vec![(**ty).clone().into()],
            },

            Type::Tuple(tys) => SmtlibSort {
                name: format!("Tuple{}", tys.len()).into(),
                parameters: tys.iter().map(|ty| ty.into()).collect(),
            },

            Type::UserDefined(_) => todo!(),
            Type::Set(_) => todo!(),
            Type::List(_) => todo!(),
            Type::Fn(_, _) => todo!(),
            Type::AddiGroupEl(_) => todo!(),
            Type::MultGroupEl(_) => todo!(),
            Type::Empty => todo!(),
            Type::Unknown => todo!(),
        }
    }
}

impl From<Type> for SmtlibSort {
    fn from(value: Type) -> Self {
        (&value).into()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Sort {
    Int,
    Bool,
    String,
    Array(Box<(Self, Self)>),
    Parameter(String),
    Other(String, Vec<Self>), /* TODO: sheould we put the datatype spec here? */
}

impl From<Type> for Sort {
    fn from(value: Type) -> Self {
        match value {
            Type::Bits(length) => {
                let length = match &*length {
                    crate::types::CountSpec::Identifier(identifier) => identifier.ident(),
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                };

                Sort::Other(format!("Bits_{length}"), vec![])
            }
            Type::Maybe(t) => Sort::Other("Maybe".to_string(), vec![(*t).into()]),
            Type::Boolean => Sort::Bool,
            Type::Empty => Sort::Other("Empty".to_string(), vec![]),
            Type::Integer => Sort::Int,
            Type::Table(t_idx, t_val) => {
                Sort::Array(Box::new(((*t_idx).into(), Type::Maybe(t_val).into())))
            }
            Type::Tuple(types) => Sort::Other(
                format!("Tuple{}", types.len()),
                types.into_iter().map(|ty| ty.into()).collect(),
            ),
            Type::Unknown => todo!(),
            Type::String => todo!(),
            Type::AddiGroupEl(_) => todo!(),
            Type::MultGroupEl(_) => todo!(),
            Type::List(_) => todo!(),
            Type::Set(_) => todo!(),
            Type::Fn(_, _) => todo!(),
            Type::UserDefined(_) => todo!(),
        }
    }
}

impl From<Sort> for SmtExpr {
    fn from(value: Sort) -> Self {
        match value {
            Sort::Int => "Int".into(),
            Sort::Bool => "Bool".into(),
            Sort::String => "String".into(),
            Sort::Array(types) => {
                let (k, v) = *types;
                ("Array", k, v).into()
            }
            Sort::Other(name, params) => {
                if params.is_empty() {
                    name.into()
                } else {
                    SmtExpr::List(
                        Some(name)
                            .into_iter()
                            .map(SmtExpr::Atom)
                            .chain(params.into_iter().map(|sort| sort.into()))
                            .collect(),
                    )
                }
            }
            Sort::Parameter(name) => name.into(),
        }
    }
}
