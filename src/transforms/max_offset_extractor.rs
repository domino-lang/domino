// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashMap;

use crate::{
    package::{Composition, Export},
    statement::{Assignment, AssignmentRhs, CodeBlock, Statement},
    transforms::samplify::{Position, SampleInfo},
};

type OffsetMap = HashMap<Position, usize>;

pub struct Transformation<'a>(pub &'a Composition, pub &'a mut SampleInfo);

impl Transformation<'_> {
    pub fn transform(self) {
        self.1.max_offset = Some(extract_max_offset(
            self.0,
            self.0.exports.iter(),
            &self.1.positions,
        ));
    }
}

fn add_offsets(target: &mut OffsetMap, source: OffsetMap) {
    for (pos, offset) in source {
        *target.entry(pos).or_insert(0) += offset;
    }
}

fn max_offsets(left: OffsetMap, right: OffsetMap) -> OffsetMap {
    let mut result = left;

    for (pos, offset) in right {
        let current = result.entry(pos).or_insert(0);
        *current = (*current).max(offset);
    }

    result
}

fn oracle_offsets(
    comp: &Composition,
    pkg_idx: usize,
    oracle_name: &str,
    positions: &[Position],
) -> OffsetMap {
    let oracle = comp.pkgs[pkg_idx]
        .pkg
        .oracles
        .iter()
        .find(|oracle| oracle.sig.name == oracle_name)
        .unwrap_or_else(|| {
            panic!(
                "could not find oracle {oracle_name} in package instance {}",
                comp.pkgs[pkg_idx].name
            )
        });

    codeblock_offsets(comp, pkg_idx, &oracle.code, positions)
}

fn codeblock_offsets(
    comp: &Composition,
    pkg_idx: usize,
    code: &CodeBlock,
    positions: &[Position],
) -> OffsetMap {
    let mut result = HashMap::new();

    for stmt in &code.0 {
        add_offsets(
            &mut result,
            statement_offsets(comp, pkg_idx, stmt, positions),
        );
    }

    result
}

fn statement_offsets(
    comp: &Composition,
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
        ) => HashMap::from([(positions[*sample_id].clone(), 1)]),
        Statement::Assignment(
            Assignment {
                rhs:
                    AssignmentRhs::Sample {
                        sample_id: None, ..
                    },
                ..
            },
            _,
        ) => unreachable!("samplify should assign a sample_id to every sample statement"),
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
            oracle_offsets(comp, edge.to(), &edge.sig().name, positions)
        }
        Statement::InvokeOracle(invoke) => {
            let edge = invoke.edge.as_ref().unwrap_or_else(|| {
                panic!("oracle invocation {} is not resolved", invoke.oracle_name)
            });
            oracle_offsets(comp, edge.to(), &edge.sig().name, positions)
        }
        Statement::IfThenElse(ite) if ite.else_block.0.is_empty() => {
            codeblock_offsets(comp, pkg_idx, &ite.then_block, positions)
        }
        Statement::IfThenElse(ite) => max_offsets(
            codeblock_offsets(comp, pkg_idx, &ite.then_block, positions),
            codeblock_offsets(comp, pkg_idx, &ite.else_block, positions),
        ),
        Statement::For(..) => panic!("cannot extract sample max offset for for loops"),
        Statement::Abort(_) | Statement::Return(_, _) | Statement::Assignment(_, _) => {
            HashMap::new()
        }
    }
}

fn extract_max_offset<'a>(
    comp: &Composition,
    exports: impl Iterator<Item = &'a Export>,
    positions: &[Position],
) -> HashMap<Export, OffsetMap> {
    exports
        .map(|export| {
            (
                export.clone(),
                oracle_offsets(comp, export.to(), &export.sig().name, positions),
            )
        })
        .collect()
}
