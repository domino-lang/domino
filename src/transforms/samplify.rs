// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::expressions::Expression;
use crate::package::{Composition, Export, PackageInstance};
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, IfThenElse, Pattern, Statement};
use crate::types::{Type, TypeKind};
use core::panic;
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::iter::FromIterator;

#[derive(Debug, Clone)]

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

#[derive(Clone, Debug, Default)]
pub struct SampleInfo {
    // collection of all types of sample operations (without duplicates)
    pub tys: Vec<Type>,
    pub count: usize,
    pub positions: Vec<Position>,
    // Each exported oracle is mapped to a list of sampling positions
    // ordered based on the first time each sampling occurs in the control flow
    // together with the maximum possible counter/offset that can be sampled.
    // Instead of a new instance of Position, we use the index to the
    // `positions` vector in order to make type look up fast as well.
    pub max_offset: HashMap<Export, Vec<(usize, usize)>>,
}

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = SampleInfo;

    fn transform(&self) -> Result<(Composition, SampleInfo), Infallible> {
        let mut ctr = 0usize;
        let mut samplings = HashSet::new();
        let mut positions = vec![];

        let game_name = self.0.name.as_str();

        let insts = self
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
            .collect::<Result<Vec<_>, Infallible>>()?;

        let max_offset = extract_max_offset(&insts, &self.0.exports, &positions);

        Ok((
            Composition {
                pkgs: insts,
                ..self.0.clone()
            },
            SampleInfo {
                tys: Vec::from_iter(samplings),
                count: ctr,
                positions,
                max_offset,
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
                if !matches!(
                    ty.kind(),
                    TypeKind::Boolean | TypeKind::Integer | TypeKind::Bits(_)
                ) {
                    panic!("Only bits, bools, and integers are allowed for sampling");
                }
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

type OffsetMap = Vec<(usize, usize)>;

// add offsets but keep the order of elements in source and target
fn add_offsets(target: &mut OffsetMap, source: &OffsetMap) {
    for (pos, offset) in source {
        if let Some(idx) = target.iter().position(|(p, _)| p == pos) {
            target[idx].1 += offset;
        } else {
            target.push((*pos, *offset));
        }
    }
}

// Concatenates the given maps and for elements that exist in both maps
// compute the maximum offset.
fn max_offsets(left: &OffsetMap, right: &OffsetMap) -> OffsetMap {
    let mut result = left.to_owned();

    for (pos, offset) in right {
        if let Some(idx) = left.iter().position(|(p, _)| p == pos) {
            result[idx].1 = result[idx].1.max(*offset);
        } else {
            result.push((*pos, *offset));
        }
    }

    result
}

fn oracle_offsets(
    pkgs: &[PackageInstance],
    pkg_idx: usize,
    oracle_name: &str,
    positions: &[Position],
) -> OffsetMap {
    let oracle = pkgs[pkg_idx]
        .pkg
        .oracles
        .iter()
        .find(|oracle| oracle.sig.name == oracle_name)
        .unwrap_or_else(|| {
            panic!(
                "could not find oracle {oracle_name} in package instance {}",
                pkgs[pkg_idx].name
            )
        });

    codeblock_offsets(pkgs, pkg_idx, &oracle.code, positions)
}

fn codeblock_offsets(
    pkgs: &[PackageInstance],
    pkg_idx: usize,
    code: &CodeBlock,
    positions: &[Position],
) -> OffsetMap {
    let mut result = vec![];

    for stmt in &code.0 {
        add_offsets(
            &mut result,
            &statement_offsets(pkgs, pkg_idx, stmt, positions),
        );
    }

    result
}

fn statement_offsets(
    pkgs: &[PackageInstance],
    pkg_idx: usize,
    stmt: &Statement,
    positions: &[Position],
) -> OffsetMap {
    match stmt {
        Statement::Assignment(
            Assignment {
                rhs:
                    AssignmentRhs::Sample {
                        sample_id: Some(sample_id),
                        ..
                    },
                ..
            },
            _,
        ) => vec![(*sample_id, 1)],
        Statement::Assignment(
            Assignment {
                rhs:
                    AssignmentRhs::Sample {
                        sample_id: None, ..
                    },
                ..
            },
            _,
        ) => unreachable!("samplify should have assigned a sample_id to every sample statement"),
        Statement::Assignment(
            Assignment {
                rhs:
                    AssignmentRhs::Invoke {
                        oracle_name, edge, ..
                    },
                ..
            },
            _,
        ) => {
            let edge = edge
                .as_ref()
                .expect(&format!("oracle invocation {oracle_name} is not resolved"));
            oracle_offsets(pkgs, edge.to(), &edge.sig().name, positions)
        }
        Statement::InvokeOracle(invoke) => {
            let edge = invoke.edge.as_ref().unwrap_or_else(|| {
                panic!("oracle invocation {} is not resolved", invoke.oracle_name)
            });
            oracle_offsets(pkgs, edge.to(), &edge.sig().name, positions)
        }
        Statement::IfThenElse(ite) if ite.else_block.0.is_empty() => {
            codeblock_offsets(pkgs, pkg_idx, &ite.then_block, positions)
        }
        Statement::IfThenElse(ite) => max_offsets(
            &codeblock_offsets(pkgs, pkg_idx, &ite.then_block, positions),
            &codeblock_offsets(pkgs, pkg_idx, &ite.else_block, positions),
        ),
        Statement::For(..) => panic!("cannot extract sample max offset for loops"),
        Statement::Abort(_) | Statement::Return(_, _) | Statement::Assignment(_, _) => {
            vec![]
        }
    }
}

fn extract_max_offset<'a>(
    pkgs: &[PackageInstance],
    exports: &[Export],
    positions: &[Position],
) -> HashMap<Export, OffsetMap> {
    exports
        .iter()
        .map(|export| {
            (
                export.clone(),
                oracle_offsets(pkgs, export.to(), &export.sig().name, positions),
            )
        })
        .collect()
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
