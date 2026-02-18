// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;
use std::convert::Infallible;

use crate::identifier::pkg_ident::PackageIdentifier;
use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export};
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, InvokeOracle, Pattern, Statement};
use crate::types::{CountSpec, Type, TypeKind};

pub struct Transformation<'a>(pub &'a Composition);

fn assert_is_populated(ty: &&Type) {
    if let TypeKind::Bits(CountSpec::Identifier(id)) = ty.kind() {
        if let Identifier::PackageIdentifier(PackageIdentifier::Const(i)) = &**id {
            debug_assert!(i.game_assignment.is_some());
        }
    }
}

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = HashSet<Type>;

    fn transform(&self) -> Result<(Composition, HashSet<Type>), Infallible> {
        let mut set = HashSet::new();

        // extract game const types
        set.extend(
            self.0
                .consts
                .iter()
                .map(|(_, ty)| ty)
                .inspect(assert_is_populated)
                .cloned(),
        );

        // extract oracle arg an return types from edges
        set.extend(self.0.edges.iter().flat_map(|Edge(_, _, sig)| {
            sig.args
                .iter()
                .map(|(_, ty)| ty)
                .chain(Some(&sig.ty))
                .inspect(assert_is_populated)
                .cloned()
        }));

        // extract oracle arg an return types from exports
        set.extend(self.0.exports.iter().flat_map(|Export(_, sig)| {
            sig.args
                .iter()
                .map(|(_, ty)| ty)
                .chain(Some(&sig.ty))
                .inspect(assert_is_populated)
                .cloned()
        }));

        // extract types from package params, state, imported oracle signatures and defined oracle
        // seignatures.
        set.extend(self.0.pkgs.iter().flat_map(|pkg_inst| {
            let pkg = &pkg_inst.pkg;

            // first prepare iterators for all the relevant types that are extracted
            let params = pkg.params.iter().map(|(_, ty, _)| ty);
            let state = pkg.state.iter().map(|(_, ty, _)| ty);
            let oracle_imports = pkg.imports.iter().flat_map(|(sig, _)| {
                sig.args
                    .iter()
                    .map(|(_, ty)| ty)
                    .chain(Some(&sig.ty))
                    .inspect(assert_is_populated)
            });
            let oracle_definitions = pkg.oracles.iter().flat_map(|oracle_def| {
                let sig = &oracle_def.sig;
                sig.args
                    .iter()
                    .map(|(_, ty)| ty)
                    .chain(Some(&sig.ty))
                    .inspect(assert_is_populated)
            });

            // Then chain them and clone the items, because the set wants owned types
            params
                .chain(state)
                .chain(oracle_imports)
                .chain(oracle_definitions)
                .cloned()
        }));

        self.0.pkgs.iter().for_each(|inst| {
            inst.pkg
                .oracles
                .iter()
                .for_each(|oracle| extract_types_from_codeblock(&mut set, oracle.code.clone()))
        });

        Ok((self.0.clone(), set))
    }
}

// This is a separate function so it's easier to inject debug printing that should happen in all
// cases.
fn record_type(set: &mut HashSet<Type>, ty: Type) {
    set.insert(ty);
}

fn extract_types_from_codeblock(set: &mut HashSet<Type>, cb: CodeBlock) {
    for stmt in cb.0 {
        match stmt {
            Statement::Abort(_) => {}
            Statement::Return(Some(expr), _) => {
                record_type(set, expr.get_type());
            }
            Statement::Return(None, _) => {}
            Statement::Assignment(Assignment { pattern, rhs }, _) => {
                if let Pattern::Table { index, .. } = &pattern {
                    record_type(set, index.get_type());
                }
                match rhs {
                    AssignmentRhs::Expression(expr) => {
                        record_type(set, expr.get_type());
                    }
                    AssignmentRhs::Sample { ty, .. } => {
                        record_type(set, ty.clone());
                    }
                    AssignmentRhs::Invoke {
                        args, return_type, ..
                    } => {
                        for arg in &args {
                            record_type(set, arg.get_type());
                        }
                        if let Some(ty) = return_type {
                            record_type(set, ty.clone());
                        }
                    }
                }
            }
            Statement::InvokeOracle(InvokeOracle { args, .. }) => {
                for arg in &args {
                    record_type(set, arg.get_type());
                }
            }
            Statement::IfThenElse(ite) => {
                record_type(set, ite.cond.get_type());
                extract_types_from_codeblock(set, ite.then_block);
                extract_types_from_codeblock(set, ite.else_block);
            }
            Statement::For(_, lower_bound, upper_bound, body, _) => {
                record_type(set, lower_bound.get_type());
                record_type(set, upper_bound.get_type());
                extract_types_from_codeblock(set, body)
            }
        }
    }
}
