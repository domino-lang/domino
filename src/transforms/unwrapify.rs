// SPDX-License-Identifier: MIT OR Apache-2.0

use std::convert::Infallible;

use miette::SourceSpan;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{
    Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
};

pub type Error = Infallible;

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Error;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Error> {
        let insts: Result<Vec<_>, Infallible> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = Unwrapifier::default().unwrapify(&oracle.code)?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            (),
        ))
    }
}

struct Unwrapifier {
    ctr: usize,
}

impl Default for Unwrapifier {
    fn default() -> Self {
        // this is a somewhat user-facing value, but nobody needs to do math with it, so let's
        // 1-index it.
        Self { ctr: 1 }
    }
}

impl Unwrapifier {
    /// Walks through `expr` and replaces Unwrap expressions with generated identifiers. The generated
    /// identifiers are numerated, starting with the initial value of `ctr`. At the end of the
    /// function, ctr is updated to the
    ///
    /// It keeps track of which original expression corresponds to what unwrap value. The gener
    ///
    /// Returns the
    fn replace_unwrap(&mut self, expr: &Expression) -> (Expression, Vec<(Expression, String)>) {
        let (result, newexpr) = expr.mapfold(Vec::new(), |mut acc, e| {
            if let ExpressionKind::Unwrap(_) = e.kind() {
                // This closure as Fn + Copy, so we can't mutate self.ctr in here.
                // So instead, we use the initial counter, plus the length of the accumulator.
                // This has the same effect, because we'd increment at exactly the same place we
                // push to the array.
                let unwrap_id = self.ctr + acc.len();
                let varname: String = format!("unwrap-{unwrap_id}");
                let ty = e.get_type();
                let ident = Identifier::Generated(varname.clone(), ty);

                acc.push((e, varname));
                // self.ctr += 1 <-- this doesn't work, see comment above!

                (acc, ident.into())
            } else {
                (acc, e)
            }
        });

        // update the counter with the number of new unwrap_ids, see comment in the closure above.
        self.ctr += result.len();
        (newexpr, result)
    }

    pub fn unwrapify(&mut self, cb: &CodeBlock) -> Result<CodeBlock, Error> {
        let mut newcode = Vec::new();
        for stmt in cb.0.clone() {
            match stmt {
                Statement::Abort(_) | Statement::Return(None, _) => {
                    newcode.push(stmt);
                }
                Statement::Return(Some(ref expr), file_pos) => {
                    let (newexpr, unwraps) = self.replace_unwrap(expr);
                    if unwraps.is_empty() {
                        newcode.push(stmt);
                    } else {
                        newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                        newcode.push(Statement::Return(Some(newexpr), file_pos));
                    }
                }
                Statement::Assignment(Assignment { pattern, rhs }, file_pos) => {
                    // Handle unwraps in pattern index (for table patterns)
                    let new_pattern = match pattern {
                        Pattern::Table { ident, index } => {
                            let (new_index, unwraps) = self.replace_unwrap(&index);
                            newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                            Pattern::Table {
                                ident,
                                index: new_index,
                            }
                        }
                        other => other,
                    };

                    // Handle unwraps in rhs expressions
                    let new_rhs = match rhs {
                        AssignmentRhs::Expression(expr) => {
                            let (newexpr, unwraps) = self.replace_unwrap(&expr);
                            newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                            AssignmentRhs::Expression(newexpr)
                        }
                        AssignmentRhs::Invoke {
                            oracle_name,
                            args,
                            target_inst_name,
                            return_type,
                        } => {
                            let new_args = args
                                .iter()
                                .map(|expr| {
                                    let (newexpr, unwraps) = self.replace_unwrap(expr);
                                    newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                                    newexpr
                                })
                                .collect();
                            AssignmentRhs::Invoke {
                                oracle_name,
                                args: new_args,
                                target_inst_name,
                                return_type,
                            }
                        }
                        other => other,
                    };

                    newcode.push(Statement::Assignment(
                        Assignment {
                            pattern: new_pattern,
                            rhs: new_rhs,
                        },
                        file_pos,
                    ));
                }
                Statement::InvokeOracle(InvokeOracle {
                    oracle_name,
                    args,
                    target_inst_name,
                    file_pos,
                }) => {
                    let new_args = args
                        .iter()
                        .map(|expr| {
                            let (newexpr, unwraps) = self.replace_unwrap(expr);
                            newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                            newexpr
                        })
                        .collect();
                    newcode.push(Statement::InvokeOracle(InvokeOracle {
                        oracle_name,
                        args: new_args,
                        target_inst_name,
                        file_pos,
                    }));
                }
                Statement::IfThenElse(ite) => {
                    let (newcond, unwraps) = self.replace_unwrap(&ite.cond);
                    newcode.extend(create_unwrap_stmts(unwraps, ite.full_span));
                    newcode.push(Statement::IfThenElse(IfThenElse {
                        cond: newcond,
                        then_block: self.unwrapify(&ite.then_block)?,
                        else_block: self.unwrapify(&ite.else_block)?,
                        ..ite
                    }));
                }
                Statement::For(ident, lower_bound, upper_bound, body, file_pos) => {
                    let (new_lower_bound, unwraps) = self.replace_unwrap(&lower_bound);
                    newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                    let (new_upper_bound, unwraps) = self.replace_unwrap(&upper_bound);
                    newcode.extend(create_unwrap_stmts(unwraps, file_pos));
                    newcode.push(Statement::For(
                        ident,
                        new_lower_bound,
                        new_upper_bound,
                        self.unwrapify(&body)?,
                        file_pos,
                    ))
                }
            }
        }
        Ok(CodeBlock(newcode))
    }
}

fn create_unwrap_stmts(unwraps: Vec<(Expression, String)>, file_pos: SourceSpan) -> Vec<Statement> {
    unwraps
        .iter()
        .map(|(expr, varname)| {
            Statement::Assignment(
                Assignment {
                    pattern: Pattern::Ident(Identifier::Generated(
                        varname.clone(),
                        expr.get_type(),
                    )),
                    rhs: AssignmentRhs::Expression(expr.clone()),
                },
                file_pos,
            )
        })
        .collect()
}

/*
[0] foo <- bar(unwrap(x))

replace_unwrap([0])
 -> x, unwrap-x-12

[0] wurde zu foo <- bar(unwrap-12-x)
*/

#[cfg(test)]
mod test {
    use miette::SourceSpan;

    use super::Unwrapifier;
    use crate::block;
    use crate::expressions::{Expression, ExpressionKind};
    use crate::identifier::pkg_ident::{PackageIdentifier, PackageLocalIdentifier};
    use crate::identifier::Identifier;
    use crate::statement::{Assignment, AssignmentRhs, CodeBlock, Pattern, Statement};
    use crate::types::Type;

    fn local_ident(name: &str, ty: Type) -> Identifier {
        Identifier::PackageIdentifier(PackageIdentifier::Local(PackageLocalIdentifier {
            pkg_name: "TestPackage".to_string(),
            oracle_name: "TestOracle".to_string(),
            name: name.to_string(),
            ty,
            pkg_inst_name: None,
            game_name: None,
            game_inst_name: None,
            theorem_name: None,
        }))
    }

    fn gend_ident(name: &str, ty: Type) -> Identifier {
        Identifier::Generated(name.to_string(), ty)
    }

    fn unwrap<E: Clone + Into<Expression>>(expr: &E) -> Expression {
        Expression::from_kind(ExpressionKind::Unwrap(Box::new(expr.clone().into())))
    }

    fn assign(id: Identifier, expr: Expression, pos: SourceSpan) -> Statement {
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(id),
                rhs: AssignmentRhs::Expression(expr),
            },
            pos,
        )
    }

    #[test]
    fn unwrap_assign() {
        let pos: SourceSpan = (0..0).into();
        let d = local_ident("d", Type::integer());
        let e = local_ident("e", Type::maybe(Type::integer()));
        let u1 = gend_ident("unwrap-1", Type::integer());

        let code = block! {
            assign(d.clone(), unwrap(&e), pos)
        };
        let newcode = block! {
            assign(u1.clone(), unwrap(&e), pos),
            assign(d.clone(), u1.into(), pos)
        };
        assert_eq!(newcode, Unwrapifier::default().unwrapify(&code).unwrap());
    }

    #[test]
    fn unwrap_two_statements() {
        let pos0: SourceSpan = (0..0).into();
        let pos1: SourceSpan = (1..1).into();

        let d = local_ident("d", Type::integer());
        let e = local_ident("e", Type::maybe(Type::integer()));
        let u1 = gend_ident("unwrap-1", Type::integer());

        let f = local_ident("f", Type::integer());
        let g = local_ident("g", Type::maybe(Type::integer()));
        let u2 = gend_ident("unwrap-2", Type::integer());

        let code = block! {
            assign(d.clone(), unwrap(&e), pos0),
            assign(f.clone(), unwrap(&g), pos1)
        };
        let newcode = block! {
            assign(u1.clone(), unwrap(&e), pos0),
            assign(d, u1.into(), pos0),
            assign(u2.clone(), unwrap(&g), pos1),
            assign(f, u2.into(), pos1)
        };

        assert_eq!(newcode, Unwrapifier::default().unwrapify(&code).unwrap());
    }

    #[test]
    fn nested_statements() {
        let pos: SourceSpan = (0..0).into();

        let d = local_ident("d", Type::integer());
        let e = local_ident("e", Type::maybe(Type::maybe(Type::integer())));
        let u1 = gend_ident("unwrap-1", Type::maybe(Type::integer()));
        let u2 = gend_ident("unwrap-2", Type::integer());

        let code = block! {
            assign(d.clone(), unwrap(&unwrap(&e)), pos)
        };
        let newcode = block! {
            assign(u1.clone(), unwrap(&e), pos),
            assign(u2.clone(), unwrap(&u1), pos),
            assign(d, u2.into(), pos)
        };

        assert_eq!(newcode, Unwrapifier::default().unwrapify(&code).unwrap());
    }
}
