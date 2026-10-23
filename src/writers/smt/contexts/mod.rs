// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{BTreeSet, HashSet};

use crate::{
    hacks,
    types::{Type, TypeKind},
    writers::smt::{exprs::SmtExpr, names},
};

pub struct GlobalContext;

impl GlobalContext {
    pub fn smt_latest_gamestate() -> SmtExpr {
        ("select", names::var_globalstate_name()).into()
    }
}

mod equivalence;
mod game_inst;
mod oracle;
mod pkg_inst;

pub use equivalence::EquivalenceContext;
pub use game_inst::GameInstanceContext;
pub use oracle::OracleContext;
pub use pkg_inst::PackageInstanceContext;

fn unique_by_name(
    input: impl IntoIterator<Item = (String, SmtExpr)>,
) -> impl Iterator<Item = SmtExpr> {
    let mut already_defined = BTreeSet::new();

    input.into_iter().filter_map(move |(name, entry)| {
        if already_defined.insert(name) {
            Some(entry)
        } else {
            None
        }
    })
}

fn emit_base_declarations(types: impl IntoIterator<Item = Type>) -> Vec<SmtExpr> {
    let mut base_declarations: Vec<SmtExpr> = vec![("set-logic", "ALL").into()];

    let mut bits_sort_suffixes = HashSet::new();

    fn add_type(suffixes: &mut HashSet<String>, ty: &Type) {
        match ty.kind() {
            TypeKind::Bits(count_spec) => {
                let bits_sort_suffix = count_spec.resolved_suffix();

                log::debug!("found {bits_sort_suffix}");

                // ensure we don't write more than once. Earlier we also dedupe, but we dedupe
                // identifiers, which contain more info than just the name.
                suffixes.insert(bits_sort_suffix.clone());
            }
            TypeKind::List(inner_ty) | TypeKind::Set(inner_ty) | TypeKind::Maybe(inner_ty) => {
                add_type(suffixes, inner_ty);
            }
            TypeKind::Fn(arg_tys, return_ty) => {
                for ty in arg_tys {
                    add_type(suffixes, ty);
                }
                add_type(suffixes, return_ty);
            }
            TypeKind::Table(index_ty, value_ty) => {
                add_type(suffixes, index_ty);
                add_type(suffixes, value_ty);
            }
            TypeKind::Tuple(inner_tys) => {
                for ty in inner_tys {
                    add_type(suffixes, ty);
                }
            }
            _ => {}
        }
    }

    for ty in types {
        add_type(&mut bits_sort_suffixes, &ty);
    }
    base_declarations.extend(
        bits_sort_suffixes
            .into_iter()
            .flat_map(hacks::BitsDeclaration),
    );

    base_declarations.extend(hacks::MaybeDeclaration);
    base_declarations.push(hacks::ReturnValueDeclaration.into());
    base_declarations.extend(hacks::TuplesDeclaration(0..32));
    base_declarations.extend(hacks::EmptyDeclaration);
    base_declarations.push(hacks::SampleIdDeclaration.into());

    base_declarations
}
