// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::SourceSpan;

use crate::package::Composition;
use crate::statement::{CodeBlock, IfThenElse, Statement};
use crate::types::Type;

#[derive(Clone, Debug)]
pub enum Error {
    MissingReturn {
        file_pos: SourceSpan,
        pkg_inst_name: String,
        oracle_name: String,
    },
}

pub struct TransformNg;

impl super::GameTransform for TransformNg {
    type Err = Error;
    type Aux = ();

    fn transform_game(&self, game: &Composition) -> Result<(Composition, Self::Aux), Self::Err> {
        let insts: Result<Vec<_>, _> = game
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = returnify(
                        &oracle.code,
                        oracle.file_pos,
                        oracle.sig.ty == Type::Empty,
                        &inst.name,
                        &oracle.sig.name,
                    )?;
                }
                // for (i, oracle) in newinst.pkg.split_oracles.clone().iter().enumerate() {
                //     newinst.pkg.split_oracles[i].code = returnify(
                //         &oracle.code,
                //         oracle.file_pos,
                //         oracle.sig.ty == Type::Empty,
                //         &inst.name,
                //         &oracle.sig.name,
                //     )?;
                // }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..game.clone()
            },
            (),
        ))
    }
}

pub fn returnify(
    cb: &CodeBlock,
    span: SourceSpan,
    none_ok: bool,
    pkg_inst_name: &str,
    oracle_name: &str,
) -> Result<CodeBlock, Error> {
    match cb.0.last() {
        Some(Statement::IfThenElse(ite)) => {
            let mut retval = cb.0.clone();
            retval.pop();
            retval.push(Statement::IfThenElse(IfThenElse {
                then_block: returnify(
                    &ite.then_block,
                    ite.then_span,
                    none_ok,
                    pkg_inst_name,
                    oracle_name,
                )?,
                else_block: returnify(
                    &ite.else_block,
                    ite.else_span,
                    none_ok,
                    pkg_inst_name,
                    oracle_name,
                )?,
                ..ite.clone()
            }));
            Ok(CodeBlock(retval))
        }
        Some(Statement::Return(_, _)) | Some(Statement::Abort(_)) => Ok(cb.clone()),
        Some(other) => {
            if !none_ok {
                Err(Error::MissingReturn {
                    file_pos: other.file_pos(),
                    oracle_name: oracle_name.to_string(),
                    pkg_inst_name: pkg_inst_name.to_string(),
                })
            } else {
                let mut retval = cb.0.clone();
                retval.push(Statement::Return(None, other.file_pos()));
                Ok(CodeBlock(retval))
            }
        }
        None => {
            // the codeblock is empty
            if !none_ok {
                Err(Error::MissingReturn {
                    file_pos: span,
                    oracle_name: oracle_name.to_string(),
                    pkg_inst_name: pkg_inst_name.to_string(),
                })
            } else {
                let mut retval = cb.0.clone();
                retval.push(Statement::Return(None, (0..1).into())); // TODO proper source span!
                Ok(CodeBlock(retval))
            }
        }
    }
}

/// Unit tests for returnify.
/// - First, all cases where blocks already end properly should be preserved:
///     preserves_return_none, preserves_return_some, preserves_abort
/// - Second, if a block ends in a non-return-type statement, a Return(None) is added
///     adds_return
/// - Finally, returnify should also consider ell branches of if-then-else
///     adds_if_return_with_branches, adds_else_return_with_branches
#[cfg(test)]
mod test {
    use miette::SourceSpan;

    use super::returnify;
    use crate::block;
    use crate::expressions::Expression;
    use crate::identifier::pkg_ident::{PackageIdentifier, PackageLocalIdentifier};
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, IfThenElse, Statement};
    use crate::types::Type;

    fn pkg_local_test_ident(name: &str, ty: Type) -> Identifier {
        Identifier::PackageIdentifier(PackageIdentifier::Local(PackageLocalIdentifier {
            pkg_name: "TestPkg".to_string(),
            oracle_name: "TestOracle".to_string(),
            name: name.to_string(),
            ty,
            pkg_inst_name: Some("test-pkg".to_string()),
            game_name: Some("TestGame".to_string()),
            game_inst_name: Some("test-game".to_string()),
            theorem_name: Some("TestTheorem".to_string()),
        }))
    }

    #[test]
    fn preserves_return_none() {
        let d = pkg_local_test_ident("d", Type::Integer);
        let file_pos: SourceSpan = (0..1).into();
        let code = block! {
            Statement::Sample(d, None, None, Type::Integer, None, file_pos),
            Statement::Return(None, file_pos)
        };
        assert_eq!(
            code,
            returnify(&code, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
    }

    #[test]
    fn preserves_return_some() {
        let file_pos: SourceSpan = (0..1).into();
        let d = pkg_local_test_ident("d", Type::Integer);
        let code = block! {
            Statement::Sample(d, None, None, Type::Integer, None, file_pos),
            Statement::Return(Some(Expression::IntegerLiteral(5)), file_pos)
        };
        assert_eq!(
            code,
            returnify(&code, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
    }

    #[test]
    fn preserves_abort() {
        let file_pos: SourceSpan = (0..1).into();
        let d = pkg_local_test_ident("d", Type::Integer);
        let code = block! {
            Statement::Sample(d, None, None, Type::Integer, None, file_pos),
            Statement::Abort(file_pos)
        };
        assert_eq!(
            code,
            returnify(&code, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
    }

    #[test]
    fn adds_return() {
        let file_pos: SourceSpan = (0..1).into();
        let d = pkg_local_test_ident("d", Type::Integer);
        let before = block! {
            Statement::Sample(d.clone(), None, None, Type::Integer, None, file_pos)
        };
        let after = block! {
            Statement::Sample(d, None, None,  Type::Integer, None, file_pos),
            Statement::Return(None, file_pos)
        };
        assert_eq!(
            after,
            returnify(&before, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
        assert_eq!(
            after,
            returnify(&after, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
    }

    #[test]
    fn adds_if_return_with_branches() {
        let file_pos: SourceSpan = (0..1).into();
        let a = pkg_local_test_ident("a", Type::Integer);
        let d = pkg_local_test_ident("d", Type::Integer);
        let e = pkg_local_test_ident("e", Type::Integer);
        let before = block! {
            Statement::IfThenElse(IfThenElse {
                cond:

                Expression::new_equals(vec![&(a.clone().into()),
                                            &(a.clone().into())]),
                then_block:
                block!{
                    Statement::Sample(d.clone(), None, None, Type::Integer, None, file_pos)
                },

                else_block: block!{
                    Statement::Sample(e.clone(), None, None, Type::Integer, None, file_pos),
                    Statement::Return(None, file_pos)
                },

                then_span:file_pos,
                else_span:file_pos,
                full_span:file_pos,
            })
        };
        let after = block! {
            Statement::IfThenElse( IfThenElse {
                cond:
                Expression::new_equals(vec![&(a.clone().into()),
                                            &(a.clone().into())]),

                then_block:
                block!{
                    Statement::Sample(d, None, None, Type::Integer, None, file_pos),
                    Statement::Return(None, file_pos)
                },

                else_block:
                block!{
                    Statement::Sample(e, None, None, Type::Integer, None, file_pos),
                    Statement::Return(None, file_pos)
                },

                then_span: file_pos,
                else_span: file_pos,
                full_span: file_pos
            })
        };
        assert_eq!(
            after,
            returnify(&before, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
        assert_eq!(
            after,
            returnify(&after, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
    }

    #[test]
    fn adds_else_return_with_branches() {
        let file_pos: SourceSpan = (0..1).into();
        let a = pkg_local_test_ident("a", Type::Integer);
        let d = pkg_local_test_ident("d", Type::Integer);
        let e = pkg_local_test_ident("e", Type::Integer);
        let before = block! {
            Statement::IfThenElse(IfThenElse{
                cond: Expression::new_equals(vec![&(a.clone().into()),
                                                  &(a.clone().into())]),
                then_block: block!{
                    Statement::Sample(d.clone(), None, None, Type::Integer, None, file_pos)
                },
                else_block: block!{
                    Statement::Sample(e.clone(), None, None, Type::Integer, None, file_pos)
                },
                then_span: file_pos,
                else_span: file_pos,
                full_span: file_pos,
            })
        };
        let after = block! {
            Statement::IfThenElse(IfThenElse {
                cond: Expression::new_equals(vec![&(a.clone().into()),
                                                  &(a.clone().into())]),
                then_block: block!{
                    Statement::Sample(d.clone(), None, None, Type::Integer, None, file_pos),
                    Statement::Return(None, file_pos)
                },

                else_block: block!{
                    Statement::Sample(e.clone(), None, None, Type::Integer, None, file_pos),
                    Statement::Return(None, file_pos)
                },

                then_span: file_pos,
                else_span: file_pos,
                full_span: file_pos,
            })
        };
        assert_eq!(
            after,
            returnify(&before, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
        assert_eq!(
            after,
            returnify(&after, file_pos, true, "some_pkg_inst", "some_oracle").unwrap()
        );
    }
}
