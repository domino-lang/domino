// SPDX-License-Identifier: MIT OR Apache-2.0

use std::borrow::Borrow;

use crate::{
    expressions::Expression,
    identifier::{game_ident::GameIdentifier, pkg_ident::PackageIdentifier, Identifier},
    types::{Type, TypeKind},
    writers::smt::exprs::SmtExpr,
};

pub fn only_ints<'a, T: 'a, I: IntoIterator<Item = &'a (T, Expression)>>(
    iter: I,
) -> impl Iterator<Item = &'a Expression> {
    iter.into_iter()
        .filter_map(|(_, expr)| match expr.get_type().kind() {
            TypeKind::Integer => Some(expr),
            _ => None,
        })
}

pub fn only_ints_and_funs<'a, T: 'a, I: IntoIterator<Item = &'a (T, Expression)>>(
    iter: I,
) -> impl Iterator<Item = &'a Expression> {
    iter.into_iter()
        .filter_map(|(_, expr)| match expr.get_type().kind() {
            TypeKind::Integer | TypeKind::Fn(_, _) => Some(expr),
            _ => None,
        })
}

pub fn only_non_function_expression<'a, T: 'a, I: IntoIterator<Item = &'a (T, Expression)>>(
    iter: I,
) -> impl Iterator<Item = &'a Expression> {
    iter.into_iter()
        .filter_map(|(_, expr)| match expr.get_type().kind() {
            TypeKind::Fn(_, _) => None,
            _ => Some(expr),
        })
}

pub fn encode_params<'a, I>(params_iter: I) -> Option<String>
where
    I: IntoIterator<Item = &'a Expression>,
{
    encode_smt_exprs(
        params_iter
            .into_iter()
            .map(|expr: &Expression| -> SmtExpr { (&resolve_assignments(expr)).into() }),
    )
}

/// Replaces package and game consts by the values they are assigned, so that names encode the
/// value a param has in the theorem rather than the name of the const it is set to in a game.
fn resolve_assignments(expr: &Expression) -> Expression {
    expr.map(|expr| {
        let assignment = match expr.as_identifier() {
            Some(Identifier::PackageIdentifier(PackageIdentifier::Const(ident))) => {
                ident.game_assignment.as_deref()
            }
            Some(Identifier::GameIdentifier(GameIdentifier::Const(ident))) => {
                ident.assigned_value.as_deref()
            }
            _ => None,
        };

        assignment.map(resolve_assignments).unwrap_or(expr)
    })
}

pub fn encode_types<'a, I>(types_iter: I) -> Option<String>
where
    I: IntoIterator<Item = &'a Type>,
{
    encode_smt_exprs(
        types_iter
            .into_iter()
            .map(|ty: &Type| -> SmtExpr { ty.into() }),
    )
}

pub fn encode_smt_exprs<Ref: Borrow<SmtExpr>, Iter: IntoIterator<Item = Ref>>(
    exprs: Iter,
) -> Option<String> {
    let mut out = String::with_capacity(64);

    // Don't print the angle brackets if there are no parames
    let mut peekable = exprs.into_iter().peekable();
    peekable.peek()?;

    out.push_str("<$");
    let mut out = peekable.fold(out, |mut acc, expr| {
        if let Some(encoding) = encode_smt_expr(expr.borrow()) {
            acc.push_str(&encoding);
        }
        acc
    });
    out.push_str("$>");

    Some(out)
}

fn encode_smt_expr(expr: &SmtExpr) -> Option<String> {
    match expr {
        SmtExpr::Comment(_) => None,
        SmtExpr::Atom(atom) => Some(format!("<!{atom}!>")),
        SmtExpr::List(exprs) => encode_smt_exprs(exprs),
    }
}
