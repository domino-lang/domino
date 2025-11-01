// SPDX-License-Identifier: MIT OR Apache-2.0

use std::convert::Infallible;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{CodeBlock, IfThenElse, InvokeOracleStatement, Statement};
use crate::types::Type;

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
            Statement::Assign(
                Identifier::Generated(ref id, ref ty),
                Some(ref idxexpr),
                ref expr,
                ref file_pos,
            ) => {
                let indextype = idxexpr.get_type();
                let Type::Maybe(valuetype) = expr.get_type() else {
                    unreachable!("all expressions are expected to be typed at this point, and the value needs to be a maybe type! ({:?})", file_pos);
                };
                let tabletype = Type::Table(
                    Box::new(indextype.clone()),
                    Box::new(valuetype.as_ref().clone()),
                );

                debug_assert_eq!(*ty, tabletype);

                if !new_initialized.contains(id) {
                    new_initialized.push(id.clone());
                    newcode.push(Statement::Assign(
                        Identifier::Generated(id.clone(), tabletype.clone()),
                        None,
                        Expression::EmptyTable(tabletype),
                        *file_pos,
                    ))
                }
                newcode.push(stmt);
            }
            Statement::Sample(
                Identifier::Generated(ref id, ref id_ty),
                Some(ref idxexpr),
                _,
                ref ty,
                _,
                ref file_pos,
            ) => {
                let indextype = idxexpr.get_type();
                let tabletype = Type::Table(Box::new(indextype.clone()), Box::new(ty.clone()));

                debug_assert_eq!(*id_ty, tabletype);

                if !new_initialized.contains(id) {
                    new_initialized.push(id.clone());
                    newcode.push(Statement::Assign(
                        Identifier::Generated(id.clone(), tabletype.clone()),
                        None,
                        Expression::EmptyTable(tabletype),
                        *file_pos,
                    ))
                }
                newcode.push(stmt);
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id: Identifier::Generated(ref id, _),
                opt_idx: Some(ref idxexpr),
                ty: ref opt_ret_ty,
                ref file_pos,
                ..
            }) => {
                let indextype = idxexpr.get_type();
                let valuetype = match opt_ret_ty {
                    Some(t) => t.to_owned(),
                    _ => Type::Empty,
                };
                let tabletype =
                    Type::Table(Box::new(indextype.clone()), Box::new(valuetype.clone()));

                if !new_initialized.contains(id) {
                    new_initialized.push(id.clone());
                    newcode.push(Statement::Assign(
                        Identifier::Generated(id.clone(), tabletype.clone()),
                        None,
                        Expression::EmptyTable(tabletype),
                        *file_pos,
                    ))
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
