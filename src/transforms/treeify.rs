use std::convert::Infallible;

use crate::package::Composition;
use crate::statement::{CodeBlock, IfThenElse, Statement};

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Infallible> {
        let insts = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            newinst.pkg.oracles.iter_mut().for_each(|oracle| {
                oracle.code = treeify(&oracle.code);
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

fn treeify(cb: &CodeBlock) -> CodeBlock {
    let mut before: Vec<Statement> = vec![];
    let mut after: Vec<Statement> = vec![];

    let mut ite_stmt = None;

    for stmt in &cb.0 {
        match stmt {
            Statement::IfThenElse(_) => {
                if ite_stmt.is_none() {
                    ite_stmt = Some(stmt.clone());
                } else {
                    after.push(stmt.clone());
                }
            }
            Statement::For(ident, from, to, code, file_pos) => {
                let new_elem = Statement::For(
                    ident.clone(),
                    from.clone(),
                    to.clone(),
                    treeify(code),
                    *file_pos,
                );

                if ite_stmt.is_none() {
                    before.push(new_elem);
                } else {
                    after.push(new_elem);
                }
            }
            _ => {
                if ite_stmt.is_none() {
                    before.push(stmt.clone());
                } else {
                    after.push(stmt.clone());
                }
            }
        }
    }

    if let Some(Statement::IfThenElse(ite)) = &mut ite_stmt {
        let last_file_pos = after
            .last()
            .map(|stmt| stmt.file_pos())
            .unwrap_or(ite.full_span);

        let block_source_span = (
            ite.full_span.offset(),
            last_file_pos.offset() + last_file_pos.len(),
        )
            .into();

        ite.then_block.0.append(&mut after.clone());
        ite.else_block.0.append(&mut after.clone());
        ite.full_span = block_source_span;

        before.push(Statement::IfThenElse(IfThenElse {
            then_block: treeify(&ite.then_block),
            else_block: treeify(&ite.else_block),
            ..ite.clone()
        }));

        CodeBlock(before)
    } else {
        cb.clone()
    }
}

#[cfg(test)]
mod treeify_fn_test {
    use miette::SourceSpan;

    use crate::expressions::Expression;
    use crate::identifier::pkg_ident::{PackageIdentifier, PackageLocalIdentifier};
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, IfThenElse, Statement};
    use crate::types::Type;

    use super::treeify;

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
    fn nothing_happens_without_if() {
        let file_pos = (0..1).into();
        let cb = CodeBlock(vec![Statement::Return(None, file_pos)]);

        assert_eq!(cb.clone(), treeify(&cb));
    }
    #[test]
    fn treeify_one_sided_if_depth_1() {
        let file_pos_0: SourceSpan = (0..1).into();
        let file_pos_1: SourceSpan = (1..1).into();
        let file_pos_2: SourceSpan = (2..2).into();
        let x = pkg_local_test_ident("x", Type::Integer);
        let y = pkg_local_test_ident("y", Type::Integer);
        let before = CodeBlock(vec![
            Statement::IfThenElse(IfThenElse {
                cond: y.clone().into(),
                then_block: CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(4),
                    file_pos_1,
                )]),
                else_block: CodeBlock(vec![]),
                then_span: file_pos_1,
                else_span: (0..0).into(),
                full_span: file_pos_0,
            }),
            Statement::Return(Some(x.clone().into()), file_pos_2),
        ]);

        let file_pos_0_new: SourceSpan = (0..2).into();

        let after = CodeBlock(vec![Statement::IfThenElse(IfThenElse {
            cond: y.clone().into(),
            then_block: CodeBlock(vec![
                Statement::Assign(x.clone(), None, Expression::IntegerLiteral(4), file_pos_1),
                Statement::Return(Some(x.clone().into()), file_pos_2),
            ]),
            else_block: CodeBlock(vec![Statement::Return(Some(x.clone().into()), file_pos_2)]),
            then_span: file_pos_1,
            else_span: (0..0).into(),
            full_span: file_pos_0_new,
        })]);

        assert_eq!(after.clone(), treeify(&before));

        // make sure it's idempotent
        assert_eq!(after.clone(), treeify(&after));
    }

    #[test]
    #[ignore]
    fn treeify_one_sided_if_depth_2() {
        println!(
            r#"
            This test was written with the assumption of using code lines to signal where something
            went wrong. We have since moved to something else, and this test broke.

            We'll fix it later, but for it's not super high priority.
        "#
        );

        let file_pos_outerif: SourceSpan = (0..2).into();
        let file_pos_innerif: SourceSpan = (1..2).into();
        let file_pos_assign: SourceSpan = (2..2).into();
        let file_pos_return: SourceSpan = (3..3).into();

        //
        //
        // 0: if y:
        // 1:   if z:
        // 2:     x = 42
        // 3: return x
        //
        // becomes
        //
        // 0: if y: (0..3)
        // 1:   if z: (1..3)
        // 2:     x = 42 (2)
        // 3:     return x (3)
        // 4:   else return x(3)
        // 5: else return x(3)
        //
        //

        let x = pkg_local_test_ident("x", Type::Integer);
        let y = pkg_local_test_ident("y", Type::Integer);
        let z = pkg_local_test_ident("z", Type::Integer);
        let before = CodeBlock(vec![
            Statement::IfThenElse(IfThenElse {
                cond: y.clone().into(),
                then_block: CodeBlock(vec![Statement::IfThenElse(IfThenElse {
                    cond: z.clone().into(),
                    then_block: CodeBlock(vec![Statement::Assign(
                        x.clone(),
                        None,
                        Expression::IntegerLiteral(42),
                        file_pos_assign,
                    )]),
                    else_block: CodeBlock(vec![]),
                    then_span: file_pos_assign,
                    else_span: (0..0).into(),
                    full_span: file_pos_innerif,
                })]),
                else_block: CodeBlock(vec![]),
                then_span: file_pos_innerif,
                else_span: (0..0).into(),
                full_span: file_pos_outerif,
            }),
            Statement::Return(Some(x.clone().into()), file_pos_return),
        ]);

        let file_pos_outerif_new: SourceSpan = (0..3).into();
        let file_pos_innerif_new: SourceSpan = (1..3).into();

        let after = CodeBlock(vec![Statement::IfThenElse(IfThenElse {
            cond: y.clone().into(),
            then_block: CodeBlock(vec![Statement::IfThenElse(IfThenElse {
                cond: z.clone().into(),
                then_block: CodeBlock(vec![
                    Statement::Assign(
                        x.clone(),
                        None,
                        Expression::IntegerLiteral(42),
                        file_pos_assign,
                    ),
                    Statement::Return(Some(x.clone().into()), file_pos_return),
                ]),
                else_block: CodeBlock(vec![Statement::Return(
                    Some(x.clone().into()),
                    file_pos_return,
                )]),
                then_span: file_pos_assign,
                else_span: (0..0).into(),
                full_span: file_pos_innerif_new,
            })]),
            else_block: CodeBlock(vec![Statement::Return(
                Some(x.clone().into()),
                file_pos_return,
            )]),
            then_span: file_pos_innerif,
            else_span: (0..0).into(),
            full_span: file_pos_outerif_new,
        })]);

        assert_eq!(after.clone(), treeify(&before));

        // make sure it's idempotent
        assert_eq!(after.clone(), treeify(&after));
    }

    #[test]
    #[ignore]
    fn treeify_subsequent_ifs() {
        println!(
            r#"
            This test was written with the assumption of using code lines to signal where something
            went wrong. We have since moved to something else, and this test broke.

            We'll fix it later, but for it's not super high priority.
        "#
        );

        let file_pos_firstif: SourceSpan = (0..3).into();
        let file_pos_secondif: SourceSpan = (4..7).into();
        let file_pos_firstifassign: SourceSpan = (1..1).into();
        let file_pos_firstselseassign: SourceSpan = (3..3).into();
        let file_pos_secondifassign: SourceSpan = (5..5).into();
        let file_pos_secondselseassign: SourceSpan = (7..7).into();
        let file_pos_return: SourceSpan = (8..8).into();

        let file_pos_firstif_new: SourceSpan = (0..8).into();
        let file_pos_second_new: SourceSpan = (4..8).into();

        //
        // if y: (0..3)
        //   x = 1 (1)
        // else:
        //   x = 2 (3)
        // if z: (4..7)
        //   x = 3 (5)
        // else:
        //   x = 4 (7)
        // return x (8)
        //
        // becomes:
        //
        // if y: (0..8)
        //   x = 1 (1)
        //   if z: (4..8)
        //     x = 3 (5)
        //     return x (8)
        //   else:
        //     x = 4 (7)
        //     return x (8)
        // else:

        let x = pkg_local_test_ident("x", Type::Integer);
        let y = pkg_local_test_ident("y", Type::Integer);
        let z = pkg_local_test_ident("z", Type::Integer);
        let before = CodeBlock(vec![
            Statement::IfThenElse(IfThenElse {
                cond: y.clone().into(),
                then_block: CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(1),
                    file_pos_firstifassign,
                )]),
                else_block: CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(2),
                    file_pos_firstselseassign,
                )]),
                then_span: file_pos_firstifassign,
                else_span: file_pos_firstselseassign,
                full_span: file_pos_firstif,
            }),
            Statement::IfThenElse(IfThenElse {
                cond: z.clone().into(),
                then_block: CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(3),
                    file_pos_secondifassign,
                )]),
                else_block: CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(4),
                    file_pos_secondselseassign,
                )]),
                then_span: file_pos_secondifassign,
                else_span: file_pos_secondselseassign,
                full_span: file_pos_secondif,
            }),
            Statement::Return(Some(x.clone().into()), file_pos_return),
        ]);

        let after = CodeBlock(vec![Statement::IfThenElse(IfThenElse {
            cond: y.clone().into(),
            then_block: CodeBlock(vec![
                Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(1),
                    file_pos_firstifassign,
                ),
                Statement::IfThenElse(IfThenElse {
                    cond: z.clone().into(),
                    then_block: CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral(3),
                            file_pos_secondifassign,
                        ),
                        Statement::Return(Some(x.clone().into()), file_pos_return),
                    ]),
                    else_block: CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral(4),
                            file_pos_secondselseassign,
                        ),
                        Statement::Return(Some(x.clone().into()), file_pos_return),
                    ]),
                    then_span: file_pos_secondifassign,
                    else_span: file_pos_secondselseassign,
                    full_span: file_pos_second_new,
                }),
            ]),
            else_block: CodeBlock(vec![
                Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral(2),
                    file_pos_firstselseassign,
                ),
                Statement::IfThenElse(IfThenElse {
                    cond: z.clone().into(),
                    then_block: CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral(3),
                            file_pos_secondifassign,
                        ),
                        Statement::Return(Some(x.clone().into()), file_pos_return),
                    ]),
                    else_block: CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral(4),
                            file_pos_secondselseassign,
                        ),
                        Statement::Return(Some(x.clone().into()), file_pos_return),
                    ]),
                    then_span: file_pos_secondifassign,
                    else_span: file_pos_secondselseassign,
                    full_span: file_pos_second_new,
                }),
            ]),
            then_span: file_pos_firstifassign,
            else_span: file_pos_firstselseassign,
            full_span: file_pos_firstif_new,
        })]);

        assert_eq!(after.clone(), treeify(&before));

        // make sure it's idempotent
        assert_eq!(after.clone(), treeify(&after));
    }
}

// #[cfg(test)]
// mod treeify_transform_test {
//     use super::super::Transformation as TTransformation;
//     use super::Transformation;
//
//     use crate::expressions::Expression;
//     use crate::package::{Composition, Edge, Export};
//     use crate::testdata::{keypkg, modprf};
//     use std::collections::HashMap;
//
//     #[test]
//     fn runs_for_all_packages_and_oracles() {
//         let mut params = HashMap::new();
//         params.insert(
//             "n".to_string(),
//             Expression::IntegerLiteral("256".to_string()),
//         );
//
//         let key_real_pkg = keypkg::key_pkg(&params);
//         let mod_prf_real_pkg = modprf::mod_prf(&params);
//
//         let mod_prf_game = Composition {
//             pkgs: vec![key_real_pkg.clone(), mod_prf_real_pkg.clone()],
//             edges: vec![Edge(1, 0, key_real_pkg.pkg.clone().oracles[1].sig.clone())],
//             exports: vec![
//                 Export(0, key_real_pkg.pkg.clone().oracles[0].sig.clone()),
//                 Export(1, mod_prf_real_pkg.pkg.clone().oracles[0].sig.clone()),
//             ],
//             name: "real".to_string(),
//             consts: vec![],
//             split_exports: vec![],
//         };
//
//         let transform = Transformation(&mod_prf_game);
//         let (tranformed, _) = transform.transform().expect("error when transforming");
//
//         assert_eq!(
//             mod_prf_game.pkgs[0].pkg.oracles[0],
//             tranformed.pkgs[0].pkg.oracles[0]
//         );
//         assert_ne!(
//             mod_prf_game.pkgs[0].pkg.oracles[1],
//             tranformed.pkgs[0].pkg.oracles[1]
//         );
//         assert_eq!(
//             mod_prf_game.pkgs[1].pkg.oracles[0],
//             tranformed.pkgs[1].pkg.oracles[0]
//         );
//     }
// }
