// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::types::{Type, TypeKind};

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
        match ty.kind() {
            TypeKind::Integer => theories::ints::int(),
            TypeKind::String => "String".into(),
            TypeKind::Boolean => theories::core::bool_(),
            TypeKind::Bits(length) => {
                let length = match length {
                    crate::types::CountSpec::Identifier(identifier) => identifier.ident(),
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                };
                format!("Bits_{length}").into()
            }
            TypeKind::Table(ty_idx, ty_val) => SmtlibSort {
                name: "Array".into(),
                parameters: vec![
                    (**ty_idx).clone().into(),
                    Type::maybe(*ty_val.clone()).into(),
                ],
            },
            TypeKind::Maybe(ty) => SmtlibSort {
                name: "Maybe".into(),
                parameters: vec![(**ty).clone().into()],
            },

            TypeKind::Tuple(tys) => SmtlibSort {
                name: format!("Tuple{}", tys.len()).into(),
                parameters: tys.iter().map(|ty| ty.into()).collect(),
            },

            TypeKind::UserDefined(_) => todo!(),
            TypeKind::TypeParam(_) => unreachable!("TypeParam should be fully instantiated before reaching the SMT backend"),
            TypeKind::Set(_) => todo!(),
            TypeKind::List(_) => todo!(),
            TypeKind::Fn(_, _) => todo!(),
            TypeKind::AddiGroupEl(_) => todo!(),
            TypeKind::MultGroupEl(_) => todo!(),
            TypeKind::Empty => todo!(),
            TypeKind::Unknown => todo!(),
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
        match value.into_kind() {
            TypeKind::Bits(length) => {
                let length = match &length {
                    crate::types::CountSpec::Identifier(identifier) => identifier.ident(),
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                };

                Sort::Other(format!("Bits_{length}"), vec![])
            }
            TypeKind::Maybe(t) => Sort::Other("Maybe".to_string(), vec![(*t).into()]),
            TypeKind::Boolean => Sort::Bool,
            TypeKind::Empty => Sort::Other("Empty".to_string(), vec![]),
            TypeKind::Integer => Sort::Int,
            TypeKind::Table(t_idx, t_val) => {
                Sort::Array(Box::new(((*t_idx).into(), Type::maybe(*t_val).into())))
            }
            TypeKind::Tuple(types) => Sort::Other(
                format!("Tuple{}", types.len()),
                types.into_iter().map(|ty| ty.into()).collect(),
            ),
            TypeKind::Unknown => todo!(),
            TypeKind::String => todo!(),
            TypeKind::AddiGroupEl(_) => todo!(),
            TypeKind::MultGroupEl(_) => todo!(),
            TypeKind::List(_) => todo!(),
            TypeKind::Set(_) => todo!(),
            TypeKind::Fn(_, _) => todo!(),
            TypeKind::UserDefined(_) => todo!(),
            TypeKind::TypeParam(_) => unreachable!("TypeParam should be fully instantiated before reaching the SMT backend"),
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
