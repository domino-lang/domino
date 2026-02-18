// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::expressions::Expression;
use crate::package::Composition;
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, IfThenElse, Pattern, Statement};
use crate::types::Type;
use std::collections::HashSet;
use std::convert::Infallible;
use std::iter::FromIterator;

#[derive(Debug, Clone)]

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    pub game_name: String,
    pub inst_name: String,
    pub pkg_name: String,
    pub oracle_name: String,

    pub dst_name: String,
    pub dst_index: Option<Expression>,

    pub sample_id: usize,
    pub ty: Type,
    pub sample_name: String,
}

#[derive(Clone, Debug)]
pub struct SampleInfo {
    pub tys: Vec<Type>,
    pub count: usize,
    pub positions: Vec<Position>,
}

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = SampleInfo;

    fn transform(&self) -> Result<(Composition, SampleInfo), Infallible> {
        let mut ctr = 0usize;
        let mut samplings = HashSet::new();
        let mut positions = vec![];

        let game_name = self.0.name.as_str();

        let insts: Result<Vec<_>, Infallible> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let inst_name = inst.name.as_str();
                let pkg_name = inst.pkg.name.as_str();

                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    let mut oracle_ctr = 1usize;
                    newinst.pkg.oracles[i].code = samplify(
                        &oracle.code,
                        game_name,
                        pkg_name,
                        inst_name,
                        &oracle.sig.name,
                        &mut ctr,
                        &mut oracle_ctr,
                        &mut samplings,
                        &mut positions,
                    )?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            SampleInfo {
                tys: Vec::from_iter(samplings),
                count: ctr,
                positions,
            },
        ))
    }
}

pub fn samplify(
    cb: &CodeBlock,
    game_name: &str,
    pkg_name: &str,
    inst_name: &str,
    oracle_name: &str,
    ctr: &mut usize,
    oracle_ctr: &mut usize,
    sampletypes: &mut HashSet<Type>,
    positions: &mut Vec<Position>,
) -> Result<CodeBlock, Infallible> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(ite) => {
                newcode.push(Statement::IfThenElse(IfThenElse {
                    then_block: samplify(
                        &ite.then_block,
                        game_name,
                        pkg_name,
                        inst_name,
                        oracle_name,
                        ctr,
                        oracle_ctr,
                        sampletypes,
                        positions,
                    )?,
                    else_block: samplify(
                        &ite.else_block,
                        game_name,
                        pkg_name,
                        inst_name,
                        oracle_name,
                        ctr,
                        oracle_ctr,
                        sampletypes,
                        positions,
                    )?,
                    ..ite
                }));
            }
            Statement::For(iter, start, end, code, file_pos) => newcode.push(Statement::For(
                iter,
                start,
                end,
                samplify(
                    &code,
                    game_name,
                    pkg_name,
                    inst_name,
                    oracle_name,
                    ctr,
                    oracle_ctr,
                    sampletypes,
                    positions,
                )?,
                file_pos,
            )),

            Statement::Assignment(
                Assignment {
                    pattern,
                    rhs:
                        AssignmentRhs::Sample {
                            ref ty,
                            sample_name,
                            sample_id: None,
                        },
                },
                file_pos,
            ) => {
                let dst_index = match &pattern {
                    Pattern::Table { index, .. } => Some(index.clone()),
                    _ => None,
                };
                let id = match &pattern {
                    Pattern::Ident(id) => id.clone(),
                    Pattern::Table { ident, .. } => ident.clone(),
                    Pattern::Tuple(_) => unreachable!("sample cannot have tuple pattern"),
                };
                let sample_name = sample_name.clone().unwrap_or(format!("{oracle_ctr}"));
                let pos = Position {
                    game_name: game_name.to_string(),
                    inst_name: inst_name.to_string(),
                    pkg_name: pkg_name.to_string(),
                    oracle_name: oracle_name.to_string(),
                    dst_name: id.ident(),
                    dst_index,
                    sample_id: *ctr,
                    ty: ty.clone(),
                    sample_name: sample_name.clone(),
                };
                sampletypes.insert(ty.clone());
                positions.push(pos);
                newcode.push(Statement::Assignment(
                    Assignment {
                        pattern,
                        rhs: AssignmentRhs::Sample {
                            ty: ty.clone(),
                            sample_name: Some(sample_name),
                            sample_id: Some(*ctr),
                        },
                    },
                    file_pos,
                ));
                *ctr += 1;
                *oracle_ctr += 1;
            }
            _ => newcode.push(stmt),
        }
    }
    Ok(CodeBlock(newcode))
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use miette::SourceSpan;

    use crate::{
        block,
        identifier::{
            pkg_ident::{PackageIdentifier, PackageLocalIdentifier},
            Identifier,
        },
        statement::{Assignment, AssignmentRhs, CodeBlock, Pattern, Statement},
        types::Type,
    };

    use super::samplify;

    fn test_run_samplify(cb: &CodeBlock) -> CodeBlock {
        let mut ctr = 0usize;
        let mut oracle_ctr = 1usize;
        let mut sampletypes = HashSet::new();
        let mut positions = vec![];

        samplify(
            cb,
            "test",
            "test",
            "test",
            "test",
            &mut ctr,
            &mut oracle_ctr,
            &mut sampletypes,
            &mut positions,
        )
        .unwrap()
    }

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

    fn sample_stmt(
        id: Identifier,
        ty: Type,
        sample_name: Option<String>,
        sample_id: Option<usize>,
        pos: SourceSpan,
    ) -> Statement {
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(id),
                rhs: AssignmentRhs::Sample {
                    ty,
                    sample_name,
                    sample_id,
                },
            },
            pos,
        )
    }

    fn extract_sample_rhs(stmt: &Statement) -> Option<(&Option<usize>, &Option<String>)> {
        if let Statement::Assignment(
            Assignment {
                rhs:
                    AssignmentRhs::Sample {
                        sample_id,
                        sample_name,
                        ..
                    },
                ..
            },
            _,
        ) = stmt
        {
            Some((sample_id, sample_name))
        } else {
            None
        }
    }

    #[test]
    fn name_and_id_set() {
        let pos: SourceSpan = (0..0).into();
        let d = local_ident("d", Type::integer());

        let code = block! {
            sample_stmt(d.clone(), Type::integer(), None, None, pos)
        };
        let new_code = test_run_samplify(&code);

        let (sample_id, sample_name) = extract_sample_rhs(&new_code.0[0]).unwrap();
        assert_eq!(sample_id, &Some(0usize));
        assert_eq!(sample_name, &Some("1".to_string()));
    }

    #[test]
    fn name_counts_named() {
        let pos: SourceSpan = (0..0).into();
        let d = local_ident("d", Type::integer());

        let code = block! {
            sample_stmt(d.clone(), Type::integer(), Some("a".to_string()), None, pos),
            sample_stmt(d.clone(), Type::integer(), None, None, pos)
        };
        let new_code = test_run_samplify(&code);

        let (sample_id, sample_name) = extract_sample_rhs(&new_code.0[0]).unwrap();
        assert_eq!(sample_id, &Some(0usize));
        assert_eq!(sample_name, &Some("a".to_string()));

        let (sample_id, sample_name) = extract_sample_rhs(&new_code.0[1]).unwrap();
        assert_eq!(sample_id, &Some(1usize));
        assert_eq!(sample_name, &Some("2".to_string()));
    }
}
