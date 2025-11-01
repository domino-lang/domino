// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::package::{Composition, Edge, OracleDef, Package, PackageInstance};
use crate::statement::{CodeBlock, IfThenElse, InvokeOracleStatement, Statement};

use std::collections::HashMap;

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Debug)]
pub(crate) struct ResolutionError(pub(crate) Vec<InvokeOracleStatement>);

type Result<T> = std::result::Result<T, ResolutionError>;

fn transform_helper_outer(table: &HashMap<String, String>, block: CodeBlock) -> Result<CodeBlock> {
    fn transform_helper(
        table: &HashMap<String, String>,
        block: CodeBlock,
        err_stmts: &mut Vec<InvokeOracleStatement>,
    ) -> CodeBlock {
        let out = block
            .0
            .into_iter()
            .filter_map(|stmt| match stmt {
                Statement::InvokeOracle(invoke_oracle_stmt) => {
                    if let Some(pkgname) = table.get(&invoke_oracle_stmt.name) {
                        Some(Statement::InvokeOracle(InvokeOracleStatement {
                            target_inst_name: Some(pkgname.clone()),
                            ..invoke_oracle_stmt
                        }))
                    } else {
                        err_stmts.push(invoke_oracle_stmt);
                        None
                    }
                }
                Statement::IfThenElse(ite) => Some(Statement::IfThenElse(IfThenElse {
                    then_block: transform_helper(table, ite.then_block.clone(), err_stmts),
                    else_block: transform_helper(table, ite.else_block.clone(), err_stmts),
                    ..ite.clone()
                })),
                _ => Some(stmt),
            })
            .collect();

        CodeBlock(out)
    }

    let mut err_stmts = vec![];

    let out = transform_helper(table, block, &mut err_stmts);

    if !err_stmts.is_empty() {
        Err(ResolutionError(err_stmts))
    } else {
        Ok(out)
    }
}

impl super::Transformation for Transformation<'_> {
    type Err = ResolutionError;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ())> {
        let mut pkgs = vec![];

        for (pos, inst) in self.0.pkgs.iter().enumerate() {
            let mut table = HashMap::<String, String>::new();
            let relevant = self.0.edges.iter().filter(|Edge(from, _, _)| *from == pos);

            for Edge(_, to, sig) in relevant {
                let pkgname = self.0.pkgs[*to].name.clone();
                table.insert(sig.name.clone(), pkgname);
            }

            let mut odefs = vec![];
            for oracle in &inst.pkg.oracles {
                odefs.push(OracleDef {
                    code: transform_helper_outer(&table, oracle.code.clone())?,
                    ..oracle.clone()
                });
            }

            pkgs.push(PackageInstance {
                pkg: Package {
                    oracles: odefs,
                    ..inst.pkg.clone()
                },
                ..inst.clone()
            });
        }
        Ok((
            Composition {
                pkgs,
                ..self.0.clone()
            },
            (),
        ))
    }
}
