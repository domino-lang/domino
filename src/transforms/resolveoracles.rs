// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::package::{Composition, Edge, OracleDef, Package, PackageInstance};
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Statement};

use std::collections::HashMap;

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Debug)]
pub(crate) struct ResolutionError(pub(crate) Vec<(String, usize)>); // (oracle_name, position)

type Result<T> = std::result::Result<T, ResolutionError>;

fn transform_helper_outer(table: &HashMap<String, &Edge>, block: CodeBlock) -> Result<CodeBlock> {
    fn transform_helper(
        table: &HashMap<String, &Edge>,
        block: CodeBlock,
        err_stmts: &mut Vec<(String, usize)>,
    ) -> CodeBlock {
        let mut pos = 0;
        let out = block
            .0
            .into_iter()
            .filter_map(|stmt| {
                let current_pos = pos;
                pos += 1;
                match stmt {
                    Statement::Assignment(
                        Assignment {
                            pattern,
                            rhs:
                                AssignmentRhs::Invoke {
                                    oracle_name,
                                    args,
                                    edge: _,
                                    return_type,
                                },
                        },
                        span,
                    ) => {
                        if let Some(edge) = table.get(&oracle_name) {
                            Some(Statement::Assignment(
                                Assignment {
                                    pattern,
                                    rhs: AssignmentRhs::Invoke {
                                        oracle_name,
                                        args,
                                        edge: Some((*edge).clone()),
                                        return_type,
                                    },
                                },
                                span,
                            ))
                        } else {
                            err_stmts.push((oracle_name, current_pos));
                            None
                        }
                    }
                    Statement::InvokeOracle(InvokeOracle {
                        oracle_name,
                        args,
                        edge: _,
                        file_pos,
                    }) => {
                        if let Some(edge) = table.get(&oracle_name) {
                            Some(Statement::InvokeOracle(InvokeOracle {
                                oracle_name,
                                args,
                                edge: Some((*edge).clone()),
                                file_pos,
                            }))
                        } else {
                            err_stmts.push((oracle_name, current_pos));
                            None
                        }
                    }
                    Statement::IfThenElse(ite) => Some(Statement::IfThenElse(IfThenElse {
                        then_block: transform_helper(table, ite.then_block.clone(), err_stmts),
                        else_block: transform_helper(table, ite.else_block.clone(), err_stmts),
                        ..ite.clone()
                    })),
                    Statement::For(var, lower, upper, code, span) => Some(Statement::For(
                        var,
                        lower,
                        upper,
                        transform_helper(table, code.clone(), err_stmts),
                        span,
                    )),
                    _ => Some(stmt),
                }
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
            let mut table = HashMap::<String, &Edge>::new();
            let relevant = self.0.edges.iter().filter(|edge| edge.from() == pos);

            for edge in relevant {
                let name = if let Some(alias) = edge.alias() {
                    alias.clone()
                } else {
                    edge.sig().name.clone()
                };
                table.insert(name, edge);
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
