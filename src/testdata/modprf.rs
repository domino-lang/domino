// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::{block, fncall};

pub fn mod_prf(params: &HashMap<String, Expression>) -> PackageInstance {
    PackageInstance {
        name: "mod-prf".to_string(),
        types: vec![],
        params: params.clone().into_iter().collect(),
        pkg: Package {
            name: "mod-prf".to_string(),
            params: vec![
                ("n".to_string(), Type::Integer),
                (
                    "f".to_string(),
                    Type::new_fn(
                        vec![Type::new_bits("n"), Type::new_bits("*")],
                        Type::new_bits("*"),
                    ),
                ),
            ],
            types: vec![],
            state: vec![],
            imports: vec![],
            split_oracles: vec![],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Eval".to_string(),
                    args: vec![("msg".to_string(), Type::new_bits("*"))],
                    ty: Type::new_bits("*"),
                },
                code: block! {
                    Statement::InvokeOracle{
                        id: Identifier::new_scalar("k"),
                        opt_idx: None,
                        name: "Get".into(),
                        args: vec![],
                        target_inst_name: None,
                        ty: None,
                    },
                    Statement::Return(Some(fncall! { "f",
                                                      Identifier::new_scalar("k").to_expression(),
                                                      Identifier::new_scalar("msg").to_expression()
                    }))
                },
            }],
        },
    }
}
