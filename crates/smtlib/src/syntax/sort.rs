// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{identifier::Identifier, s_expr::SExpr};

#[derive(Debug, Clone)]
pub struct Sort {
    pub name: Identifier,
    pub parameters: Vec<Sort>,
}

impl<T: Into<Identifier>> From<T> for Sort {
    fn from(value: T) -> Self {
        Sort {
            name: value.into(),
            parameters: vec![],
        }
    }
}

impl From<Sort> for SExpr {
    fn from(value: Sort) -> Self {
        if value.parameters.is_empty() {
            value.name.into()
        } else {
            SExpr::SExpr(
                Some(value.name.into())
                    .into_iter()
                    .chain(value.parameters.into_iter().map(|par| par.into()))
                    .collect(),
            )
        }
    }
}
