// SPDX-License-Identifier: MIT OR Apache-2.0

//! This transform splits assignments of the form
//!
//!   `(a, b, c) <- invoke Oracle(args);`
//!
//! into two separate statements:
//!
//!   `_invoke-result-N <- invoke Oracle(args);`
//!   `(a, b, c) <- _invoke-result-N;`
//!
//! This is needed because the SMT backend cannot handle tuple-pattern oracle
//! invocations directly. The split must happen before the SMT writer sees the
//! code, and has no other dependencies on the transform pipeline.

use std::convert::Infallible;

use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, IfThenElse, Pattern, Statement};

pub type Error = Infallible;

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Error;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Error> {
        let pkgs = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = Splitter::default().split(&oracle.code);
                }
                newinst
            })
            .collect();

        Ok((
            Composition {
                pkgs,
                ..self.0.clone()
            },
            (),
        ))
    }
}

struct Splitter {
    ctr: usize,
}

impl Default for Splitter {
    fn default() -> Self {
        // 1-indexed to match the convention in unwrapify
        Self { ctr: 1 }
    }
}

impl Splitter {
    fn split(&mut self, cb: &CodeBlock) -> CodeBlock {
        let mut newcode: Vec<Statement> = Vec::new();

        for stmt in &cb.0 {
            match stmt {
                Statement::Assignment(
                    Assignment {
                        pattern: Pattern::Tuple(idents),
                        rhs:
                            AssignmentRhs::Invoke {
                                oracle_name,
                                args,
                                target_inst_name,
                                return_type: Some(return_type),
                            },
                    },
                    span,
                ) => {
                    let tmp_name = format!("invoke-result-{}", self.ctr);
                    self.ctr += 1;

                    let tmp_ident = Identifier::Generated(tmp_name, return_type.clone());

                    // First statement: tmp <- invoke Oracle(args)
                    newcode.push(Statement::Assignment(
                        Assignment {
                            pattern: Pattern::Ident(tmp_ident.clone()),
                            rhs: AssignmentRhs::Invoke {
                                oracle_name: oracle_name.clone(),
                                args: args.clone(),
                                target_inst_name: target_inst_name.clone(),
                                return_type: Some(return_type.clone()),
                            },
                        },
                        *span,
                    ));

                    // Second statement: (a, b, c) <- tmp
                    newcode.push(Statement::Assignment(
                        Assignment {
                            pattern: Pattern::Tuple(idents.clone()),
                            rhs: AssignmentRhs::Expression(tmp_ident.into()),
                        },
                        *span,
                    ));
                }

                Statement::IfThenElse(ite) => {
                    newcode.push(Statement::IfThenElse(IfThenElse {
                        then_block: self.split(&ite.then_block),
                        else_block: self.split(&ite.else_block),
                        ..ite.clone()
                    }));
                }

                Statement::For(var, lower, upper, body, span) => {
                    newcode.push(Statement::For(
                        var.clone(),
                        lower.clone(),
                        upper.clone(),
                        self.split(body),
                        *span,
                    ));
                }

                other => newcode.push(other.clone()),
            }
        }

        CodeBlock(newcode)
    }
}

#[cfg(test)]
mod test {
    use miette::SourceSpan;

    use super::Splitter;
    use crate::block;
    use crate::identifier::Identifier;
    use crate::statement::{Assignment, AssignmentRhs, CodeBlock, Pattern, Statement};
    use crate::types::Type;

    fn gend(name: &str, ty: Type) -> Identifier {
        Identifier::Generated(name.to_string(), ty)
    }

    fn invoke_stmt(
        pattern: Pattern,
        oracle_name: &str,
        return_type: Type,
        pos: SourceSpan,
    ) -> Statement {
        Statement::Assignment(
            Assignment {
                pattern,
                rhs: AssignmentRhs::Invoke {
                    oracle_name: oracle_name.to_string(),
                    args: vec![],
                    target_inst_name: None,
                    return_type: Some(return_type),
                },
            },
            pos,
        )
    }

    fn assign_expr(pattern: Pattern, expr_ident: Identifier, pos: SourceSpan) -> Statement {
        Statement::Assignment(
            Assignment {
                pattern,
                rhs: AssignmentRhs::Expression(expr_ident.into()),
            },
            pos,
        )
    }

    #[test]
    fn splits_tuple_invoke() {
        let pos: SourceSpan = (0..0).into();
        let a = gend("a", Type::integer());
        let b = gend("b", Type::boolean());
        let tuple_ty = Type::tuple(vec![Type::integer(), Type::boolean()]);
        let tmp = gend("invoke-result-1", tuple_ty.clone());

        let input = block! {
            invoke_stmt(
                Pattern::Tuple(vec![a.clone(), b.clone()]),
                "MyOracle",
                tuple_ty.clone(),
                pos,
            )
        };

        let expected = block! {
            invoke_stmt(Pattern::Ident(tmp.clone()), "MyOracle", tuple_ty.clone(), pos),
            assign_expr(Pattern::Tuple(vec![a.clone(), b.clone()]), tmp.clone(), pos)
        };

        assert_eq!(expected, Splitter::default().split(&input));
    }

    #[test]
    fn leaves_non_tuple_invoke_unchanged() {
        let pos: SourceSpan = (0..0).into();
        let x = gend("x", Type::integer());

        let input = block! {
            invoke_stmt(Pattern::Ident(x.clone()), "MyOracle", Type::integer(), pos)
        };

        let result = Splitter::default().split(&input);
        assert_eq!(input, result);
    }
}
