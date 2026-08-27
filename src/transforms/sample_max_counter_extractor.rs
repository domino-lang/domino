// SPDX-License-Identifier: MIT OR Apache-2.0

//! Computes, for every exported oracle, the maximum (over-approximated)
//! counter/offset each sampling position reachable from that export can be
//! sampled at.
//!
//! This is the former second stage of `samplify`. It has been split out
//! because it needs to run after `loopunroll`, so that a sample inside a
//! bounded loop is counted once per unrolled iteration: loop bodies keep the
//! `sample_id` assigned by `samplify` when they get unrolled, so several
//! statements can share the same id by the time this transform sees them.
//! `samplify` itself has to keep running before loop unrolling, since it is
//! also used by the latex export, which must not unroll loops. It must also
//! run after `resolveoracles`, so oracle invocations carry a resolved `edge`
//! to follow, and before `treeify`, which discards the sequential structure
//! this traversal relies on.

use std::collections::HashMap;
use std::convert::Infallible;

use crate::package::{Composition, Export, PackageInstance};
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, Statement};

use super::samplify::Position;

pub struct Transformation<'a>(pub &'a Composition, pub &'a [Position]);

pub type MaxOffsets = HashMap<Export, HashMap<Position, usize>>;

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = MaxOffsets;

    fn transform(&self) -> Result<(Composition, MaxOffsets), Infallible> {
        let positions = self.1;
        let max_offset = extract_max_offset(&self.0.pkgs, &self.0.exports, positions);

        Ok((self.0.clone(), max_offset))
    }
}

type OffsetMap = HashMap<usize, usize>;

fn add_offsets(target: &mut OffsetMap, source: &OffsetMap) {
    for (pos, offset) in source {
        *target.entry(*pos).or_insert(0) += offset;
    }
}

// Takes union of the given maps and for elements that exist in both maps
// compute the maximum offset.
fn max_offsets(left: &OffsetMap, right: &OffsetMap) -> OffsetMap {
    let mut result = left.to_owned();

    for (pos, offset) in right {
        result
            .entry(*pos)
            .and_modify(|existing| *existing = (*existing).max(*offset))
            .or_insert(*offset);
    }

    result
}

fn oracle_offsets(pkgs: &[PackageInstance], pkg_idx: usize, oracle_name: &str) -> OffsetMap {
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

    codeblock_offsets(pkgs, pkg_idx, &oracle.code)
}

fn codeblock_offsets(pkgs: &[PackageInstance], pkg_idx: usize, code: &CodeBlock) -> OffsetMap {
    let mut result = HashMap::new();

    for stmt in &code.0 {
        add_offsets(&mut result, &statement_offsets(pkgs, pkg_idx, stmt));
    }

    result
}

fn statement_offsets(pkgs: &[PackageInstance], pkg_idx: usize, stmt: &Statement) -> OffsetMap {
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
        ) => HashMap::from([(*sample_id, 1)]),
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
                .unwrap_or_else(|| panic!("oracle invocation {oracle_name} is not resolved"));
            oracle_offsets(pkgs, edge.to(), &edge.sig().name)
        }
        Statement::InvokeOracle(invoke) => {
            let edge = invoke.edge.as_ref().unwrap_or_else(|| {
                panic!("oracle invocation {} is not resolved", invoke.oracle_name)
            });
            oracle_offsets(pkgs, edge.to(), &edge.sig().name)
        }
        Statement::IfThenElse(ite) if ite.else_block.0.is_empty() => {
            codeblock_offsets(pkgs, pkg_idx, &ite.then_block)
        }
        Statement::IfThenElse(ite) => max_offsets(
            &codeblock_offsets(pkgs, pkg_idx, &ite.then_block),
            &codeblock_offsets(pkgs, pkg_idx, &ite.else_block),
        ),
        Statement::For(..) => panic!("cannot extract sample max offset for loops"),
        Statement::Abort(_) | Statement::Return(_, _) | Statement::Assignment(_, _) => {
            HashMap::new()
        }
    }
}

// Converts the sample-id-indexed offsets computed per export into a map
// keyed directly by sampling `Position`, so callers don't need to thread
// `samplify`'s `positions` vector through just to resolve the index.
fn extract_max_offset(
    pkgs: &[PackageInstance],
    exports: &[Export],
    positions: &[Position],
) -> MaxOffsets {
    exports
        .iter()
        .map(|export| {
            let offsets = oracle_offsets(pkgs, export.to(), &export.sig().name);
            let by_position = offsets
                .into_iter()
                .map(|(sample_id, max_offset)| (positions[sample_id].clone(), max_offset))
                .collect();
            (export.clone(), by_position)
        })
        .collect()
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{
        parser::tests::{games, packages},
        transforms::{
            loopunroll, resolveoracles, returnify, samplify, GameTransform, Transformation as _,
        },
    };

    #[test]
    fn counts_one_sample_per_unrolled_loop_iteration() {
        let pkg_code = r#"package SumSampler {
    params {
        n: Integer,
    }

    state {
        T: Table(Integer, Bits(n)),
    }

    oracle Fill() {
        for i: 0 <= i < 3 {
            r <-$ Bits(n);
            T[i] <- Some(r);
        }
    }
}
"#;
        let (pkg_name, pkg) = packages::parse(pkg_code, "SumSampler.pkg.ssp");
        let pkg_map = HashMap::from([(pkg_name, pkg)]);

        let game_code = r#"composition SumSamplerGame {
    const n: Integer;

    instance pkg = SumSampler {
        params {
            n: n,
        }
    }

    compose {
        adversary: {
            Fill: pkg,
        }
    }
}
"#;
        let comp = games::parse(game_code, "SumSamplerGame.comp.ssp", &pkg_map);

        let (comp, _) = resolveoracles::Transformation(&comp).transform().unwrap();
        let (comp, sample_info) = samplify::Transformation(&comp).transform().unwrap();
        let (comp, _) = returnify::TransformNg.transform_game(&comp).unwrap();
        let (comp, _) = loopunroll::Transformation(&comp).transform().unwrap();

        // Before this transform moved out of samplify and started running
        // after loopunroll, this would have panicked here on the (still
        // present) `for` loop.
        let (_, max_offsets) = super::Transformation(&comp, &sample_info.positions)
            .transform()
            .unwrap();

        let export = comp.exports.iter().find(|e| e.name() == "Fill").unwrap();
        let offsets = max_offsets.get(export).unwrap();

        assert_eq!(offsets.len(), 1);
        assert_eq!(*offsets.values().next().unwrap(), 3);
    }
}
