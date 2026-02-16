// SPDX-License-Identifier: MIT OR Apache-2.0

use std::convert::Infallible;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, IfThenElse, Pattern, Statement};
use crate::types::{Type, TypeKind};

pub type Error = Infallible;

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Error;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Error> {
        let insts: Result<Vec<_>, Error> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = tableinitialize(&oracle.code, vec![])?;
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

pub fn tableinitialize(
    cb: &CodeBlock,
    mut new_initialized: Vec<String>,
) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(ite) => {
                newcode.push(Statement::IfThenElse(IfThenElse {
                    then_block: tableinitialize(&ite.then_block, new_initialized.clone())?,
                    else_block: tableinitialize(&ite.else_block, new_initialized.clone())?,

                    ..ite
                }));
            }
            Statement::Assignment(
                Assignment {
                    pattern:
                        Pattern::Table {
                            ref ident,
                            ref index,
                        },
                    ref rhs,
                },
                file_pos,
            ) => {
                // Check if the identifier is Generated
                if let Identifier::Generated(ref id, ref ty) = ident {
                    let indextype = index.get_type();

                    // Determine the value type based on RHS
                    let valuetype = match rhs {
                        AssignmentRhs::Expression(ref expr) => {
                            // For expressions, the type should be Maybe(T), extract T
                            let TypeKind::Maybe(valuetype) = expr.get_type().into_kind() else {
                                unreachable!("all expressions are expected to be typed at this point, and the value needs to be a maybe type! ({:?})", file_pos);
                            };
                            valuetype.as_ref().clone()
                        }
                        AssignmentRhs::Sample { ref ty, .. } => ty.clone(),
                        AssignmentRhs::Invoke {
                            ref return_type, ..
                        } => match return_type {
                            Some(t) => t.clone(),
                            None => Type::empty(),
                        },
                    };

                    let tabletype = Type::table(indextype.clone(), valuetype.clone());
                    debug_assert_eq!(*ty, tabletype);

                    if !new_initialized.contains(id) {
                        new_initialized.push(id.clone());
                        newcode.push(Statement::Assignment(
                            Assignment {
                                pattern: Pattern::Ident(Identifier::Generated(
                                    id.clone(),
                                    tabletype.clone(),
                                )),
                                rhs: AssignmentRhs::Expression(Expression::from_kind(
                                    ExpressionKind::EmptyTable(tabletype),
                                )),
                            },
                            file_pos,
                        ));
                    }
                }
                newcode.push(stmt);
            }
            _ => {
                newcode.push(stmt);
            }
        }
    }
    Ok(CodeBlock(newcode))
}

#[cfg(test)]
mod test {}
