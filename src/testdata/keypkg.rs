// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::block;

pub fn key_pkg(params: &HashMap<String, Expression>) -> PackageInstance {
    PackageInstance {
        name: "key".to_string(),
        types: vec![],
        params: params.clone().into_iter().collect(),
        pkg: Package {
            split_oracles: vec![],
            name: "key".to_string(),
            params: vec![("n".to_string(), Type::Integer)],
            state: vec![("k".to_string(), Type::Maybe(Box::new(Type::new_bits("n"))))],
            types: vec![],
            imports: vec![],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("k_".to_string(), Type::new_bits("n"))],
                        ty: Type::Empty,
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::None(Type::new_bits("n")),
                            ]),
                            block! {
                                Statement::Sample(Identifier::new_scalar("k_sample"), None, None, Type::new_bits("n"),
                                ),
                                Statement::Assign(Identifier::new_scalar("k"), None,
                                                  Expression::Some(Box::new(Identifier::new_scalar("k_sample").to_expression())),
                                )
                            },
                            block! {
                                Statement::Abort
                            },
                        )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![],
                        ty: Type::new_bits("n"),
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::None(Type::new_bits("n")),
                            ]),
                            block! {Statement::Abort},
                            block! {},
                        ),
                        Statement::Assign(Identifier::new_scalar("k_unwrapped"), None, Expression::Unwrap(Box::new(Identifier::new_scalar("k").to_expression()))),
                        Statement::Return(Some(Identifier::new_scalar("k_unwrapped").to_expression()))
                    },
                },
            ],
        },
    }
}
