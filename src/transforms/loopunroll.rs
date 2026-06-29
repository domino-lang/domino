// SPDX-License-Identifier: MIT OR Apache-2.0

use std::convert::Infallible;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::Identifier,
    package::Composition,
    statement::{
        Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
    },
};

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Infallible> {
        let insts = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            newinst.pkg.oracles.iter_mut().for_each(|oracle| {
                oracle.code = unroll(&oracle.code, &Vec::new());
            });
            newinst
        });
        Ok((
            Composition {
                pkgs: insts.collect(),
                ..self.0.clone()
            },
            (),
        ))
    }
}

fn unroll(cb: &CodeBlock, subst: &Vec<(&Identifier, &Identifier)>) -> CodeBlock {
    let mut newcode = Vec::new();

    let fn_subst = |expr: Expression| {
        if let Some(ident) = expr.as_identifier() {
            if let Some((_, sub)) = subst.iter().find(|(old, _)| &ident == old) {
                (*sub).clone().into()
            } else {
                expr
            }
        } else {
            expr
        }
    };

    for stmt in &cb.0 {
        match stmt {
            Statement::ForEach(pattern, args, code, span) => {
                let loopcode = unroll(code, subst);
                for arg in args {
                    newcode.push(Statement::Assignment(
                        Assignment {
                            pattern: pattern.clone(),
                            rhs: AssignmentRhs::Expression(arg.clone()),
                        },
                        *span,
                    ));
                    newcode.extend(loopcode.0.iter().cloned());
                }
            }
            Statement::For(ident, lower, upper, code, span) => {
                if let (
                    ExpressionKind::IntegerLiteral(lower),
                    ExpressionKind::IntegerLiteral(upper),
                ) = (lower.kind(), upper.kind())
                {
                    let gen_ident = Identifier::Generated(ident.ident(), ident.get_type().clone());

                    let mut newsubst = subst.clone();
                    newsubst.push((ident, &gen_ident));
                    let loopcode = unroll(code, &newsubst);

                    for i in (*lower)..(*upper) {
                        newcode.push(Statement::Assignment(
                            Assignment {
                                pattern: Pattern::Ident(gen_ident.clone()),
                                rhs: AssignmentRhs::Expression(Expression::integer(i)),
                            },
                            *span,
                        ));
                        newcode.extend(loopcode.0.iter().cloned());
                    }
                } else {
                    newcode.push(Statement::For(
                        ident.clone(),
                        lower.map(fn_subst),
                        upper.map(fn_subst),
                        unroll(code, subst),
                        *span,
                    ));
                }
            }
            Statement::IfThenElse(ite) => {
                newcode.push(Statement::IfThenElse(IfThenElse {
                    cond: ite.cond.map(fn_subst),
                    then_block: unroll(&ite.then_block, subst),
                    else_block: unroll(&ite.else_block, subst),
                    ..ite.clone()
                }));
            }
            Statement::Assignment(assign, span) => {
                let pattern = if let Pattern::Table { ident, index } = &assign.pattern {
                    Pattern::Table {
                        ident: ident.clone(),
                        index: index.map(fn_subst),
                    }
                } else {
                    assign.pattern.clone()
                };
                let rhs = match assign.rhs.clone() {
                    AssignmentRhs::Expression(e) => AssignmentRhs::Expression(e.map(fn_subst)),
                    r @ AssignmentRhs::Sample { .. } => r,
                    AssignmentRhs::Invoke {
                        oracle_name,
                        args,
                        edge,
                        return_type,
                    } => AssignmentRhs::Invoke {
                        oracle_name,
                        args: args.iter().map(|expr| expr.map(fn_subst)).collect(),
                        edge,
                        return_type,
                    },
                };
                newcode.push(Statement::Assignment(Assignment { pattern, rhs }, *span));
            }
            Statement::InvokeOracle(io) => {
                newcode.push(Statement::InvokeOracle(InvokeOracle {
                    args: io.args.iter().map(|expr| expr.map(fn_subst)).collect(),
                    ..io.clone()
                }));
            }
            Statement::Return(expr, span) => newcode.push(Statement::Return(
                expr.as_ref().map(|expr| expr.map(fn_subst)),
                *span,
            )),
            Statement::Abort(_) => newcode.push(stmt.clone()),
        }
    }

    CodeBlock(newcode)
}
