// SPDX-License-Identifier: MIT OR Apache-2.0

//! Translating Domino [`Type`]s and [`Expression`]s into [`EcType`]/[`EcExpr`].
//!
//! Neither `Type` nor `Expression` carries its own [`SourceSpan`] in Domino's
//! data model (only statements and package field declarations do), so every
//! entry point here takes a `span` supplied by the caller from the nearest
//! enclosing spanned Domino node, and echoes it back in any
//! [`EcExportError`] it raises.
//!
//! Resolving a Domino [`Identifier`] to an [`EcExpr`] (a mangled local
//! variable, or a module-qualified state field) is caller-specific — story
//! 03 tells locals and state fields apart — so [`translate_expr`] takes a
//! resolver callback rather than doing it itself.

use miette::SourceSpan;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::Identifier;
use crate::types::{CountSpec, Type, TypeKind};

use super::ast::{EcBinop, EcExpr, EcType, EcUnop};
use super::EcExportError;

/// A callback that resolves a Domino identifier (a package state field, a
/// local, a theorem const, …) occurring in expression position to the
/// [`EcExpr`] that refers to it — a mangled variable name, or a
/// module-qualified state name. `span` is the span of the expression the
/// identifier was found in, for the resolver's own error reporting.
pub type IdentifierResolver<'a> =
    &'a mut dyn FnMut(&Identifier, SourceSpan) -> Result<EcExpr, EcExportError>;

/// Translate a Domino type into its EasyCrypt equivalent (§3.1).
///
/// A `Tuple` of exactly one element cannot occur — EasyCrypt has no
/// 1-tuples, and Domino's own parser never produces one — but rather than
/// panic on a would-be compiler bug, it comes back as a hard
/// [`EcExportError::UnsupportedType`] like every other unsupported
/// construct.
pub fn translate_type(ty: &Type, span: SourceSpan) -> Result<EcType, EcExportError> {
    match ty.kind() {
        TypeKind::Integer => Ok(EcType::Int),
        TypeKind::Boolean => Ok(EcType::Bool),
        TypeKind::Empty => Ok(EcType::Unit),
        TypeKind::Bits(count) => Ok(EcType::Named(bits_type_name(count))),
        TypeKind::Maybe(inner) => Ok(EcType::Option(Box::new(translate_type(inner, span)?))),
        TypeKind::Table(key, value) => Ok(EcType::Fmap(
            Box::new(translate_type(key, span)?),
            Box::new(translate_type(value, span)?),
        )),
        TypeKind::Tuple(items) => {
            if items.len() == 1 {
                return Err(EcExportError::UnsupportedType {
                    construct: "1-element Tuple (EasyCrypt has no 1-tuples)",
                    span,
                });
            }
            let items = items
                .iter()
                .map(|item| translate_type(item, span))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(EcType::Tuple(items))
        }
        TypeKind::Fn(args, ret) => {
            // Fold right-to-left so the last argument ends up closest to the
            // return type: `Fn([a, b], r)` -> `a -> (b -> r)`.
            let mut result = translate_type(ret, span)?;
            for arg in args.iter().rev() {
                result = EcType::Fun(Box::new(translate_type(arg, span)?), Box::new(result));
            }
            Ok(result)
        }
        TypeKind::String => unsupported_type("String", span),
        TypeKind::List(_) => unsupported_type("List", span),
        TypeKind::Set(_) => unsupported_type("Set", span),
        TypeKind::AddiGroupEl(_) => unsupported_type("AddiGroupEl", span),
        TypeKind::MultGroupEl(_) => unsupported_type("MultGroupEl", span),
        TypeKind::UserDefined(_) => unsupported_type("UserDefined", span),
        TypeKind::Unknown => unsupported_type("Unknown", span),
    }
}

fn unsupported_type<T>(construct: &'static str, span: SourceSpan) -> Result<T, EcExportError> {
    Err(EcExportError::UnsupportedType { construct, span })
}

/// The suffix a bits width contributes to its type/constant names: `None`
/// for `Bits(*)` (whose names have no suffix at all — `bits`, `zero`, …),
/// `Some` otherwise. Panics if an identifier width was never resolved to a
/// theorem const, mirroring [`CountSpec::resolved_suffix`]'s own panic for
/// the same invariant — by the time export runs (after game instantiation)
/// every width identifier is resolved.
pub fn bits_suffix(count: &CountSpec) -> Option<String> {
    match count {
        CountSpec::Any => None,
        CountSpec::Literal(n) => Some(n.to_string()),
        CountSpec::Identifier(id) => {
            let suffix = id
                .as_theorem_identifier()
                .map(|theorem_id| theorem_id.ident())
                .unwrap_or_else(|| {
                    panic!("bits-length identifier not resolved to a theorem const: {id:?}")
                })
                .replace('-', "_");
            // §6: an empty suffix here would make this width's name collide
            // with `Bits(*)`'s bare `bits`/`zero`/`one`/`dbits` — impossible
            // today (Domino identifiers are never empty), but worth a hard
            // assert rather than a silent collision if that ever changes.
            debug_assert!(
                !suffix.is_empty(),
                "bits-width identifier {id:?} mangled to an empty suffix"
            );
            Some(suffix)
        }
    }
}

/// The EasyCrypt type name for a `Bits` width (§3.1): `bits_<n>` with `-` ->
/// `_`, or bare `bits` for `Bits(*)`. Domino width identifiers always start
/// lowercase, so — unlike [`super::names::mangle`] — no further mangling is
/// applied.
pub fn bits_type_name(count: &CountSpec) -> String {
    match bits_suffix(count) {
        Some(suffix) => format!("bits_{suffix}"),
        None => "bits".to_string(),
    }
}

/// The `op` name for a theorem constant of `Fn` type, mirroring Domino's SMT
/// name `<<func-{name}>>` (`src/writers/smt/contexts/equivalence/emit.rs`):
/// `func_<name>` with `-` -> `_`.
pub fn func_op_name(theorem_const_name: &str) -> String {
    format!("func_{}", theorem_const_name.replace('-', "_"))
}

/// Translate a Domino expression into its EasyCrypt equivalent (§3.2).
///
/// `Sample` is rejected here even though it is an `ExpressionKind` variant:
/// by the time export runs, `samplify` has already turned every sampling
/// expression into a statement (story 03's concern), so one reaching this
/// function is a translation-order bug, not unsupported Domino source.
pub fn translate_expr(
    expr: &Expression,
    span: SourceSpan,
    resolve_identifier: IdentifierResolver,
) -> Result<EcExpr, EcExportError> {
    match expr.kind() {
        ExpressionKind::IntegerLiteral(n) => Ok(EcExpr::Int(*n)),
        ExpressionKind::BooleanLiteral(b) => Ok(EcExpr::Bool(b == "true")),
        ExpressionKind::Bot => Ok(EcExpr::Unit),
        ExpressionKind::BitsLiteral(literal, ty) => translate_bits_literal(literal, ty),
        ExpressionKind::Identifier(id) => resolve_identifier(id, span),
        ExpressionKind::None(inner_ty) => {
            Ok(EcExpr::None_(translate_type(inner_ty, span)?))
        }
        ExpressionKind::Some(inner) => Ok(EcExpr::Some_(Box::new(translate_expr(
            inner,
            span,
            resolve_identifier,
        )?))),
        ExpressionKind::Unwrap(inner) => Ok(EcExpr::Oget(Box::new(translate_expr(
            inner,
            span,
            resolve_identifier,
        )?))),
        ExpressionKind::EmptyTable(_) => Ok(EcExpr::MapEmpty),
        ExpressionKind::TableAccess(id, key) => {
            let map = resolve_identifier(id, span)?;
            let key = translate_expr(key, span, resolve_identifier)?;
            Ok(EcExpr::MapGet {
                map: Box::new(map),
                key: Box::new(key),
            })
        }
        ExpressionKind::Tuple(items) => {
            Ok(EcExpr::Tuple(translate_all(items, span, resolve_identifier)?))
        }
        ExpressionKind::FnCall(id, args) => {
            let name = id
                .as_theorem_identifier()
                .expect("FnCall's identifier is always a theorem constant")
                .ident();
            let args = translate_all(args, span, resolve_identifier)?;
            Ok(EcExpr::App {
                head: func_op_name(&name),
                args,
            })
        }
        ExpressionKind::Not(inner) => unop(EcUnop::Not, inner, span, resolve_identifier),
        ExpressionKind::Neg(inner) => unop(EcUnop::Neg, inner, span, resolve_identifier),
        ExpressionKind::Add(a, b) => binop(EcBinop::Add, a, b, span, resolve_identifier),
        ExpressionKind::Sub(a, b) => binop(EcBinop::Sub, a, b, span, resolve_identifier),
        ExpressionKind::Mul(a, b) => binop(EcBinop::Mul, a, b, span, resolve_identifier),
        ExpressionKind::Div(a, b) => binop(EcBinop::Div, a, b, span, resolve_identifier),
        ExpressionKind::Mod(a, b) => binop(EcBinop::Mod, a, b, span, resolve_identifier),
        ExpressionKind::LessThen(a, b) => binop(EcBinop::Lt, a, b, span, resolve_identifier),
        ExpressionKind::LessThenEq(a, b) => binop(EcBinop::Le, a, b, span, resolve_identifier),
        // Never emit `>`/`>=`: EasyCrypt's standard library only defines
        // them for `real` (see docs/stories/easycrypt/02-…md §2.1), and
        // Domino has no `real` type, so every `>`/`>=` operand would fail to
        // typecheck. Flip to `<`/`<=` instead — always correct, and simpler
        // than a local per-type operator override.
        ExpressionKind::GreaterThen(a, b) => binop(EcBinop::Lt, b, a, span, resolve_identifier),
        ExpressionKind::GreaterThenEq(a, b) => binop(EcBinop::Le, b, a, span, resolve_identifier),
        ExpressionKind::Equals(exprs) => Ok(equals_adjacent_pairs(translate_all(
            exprs,
            span,
            resolve_identifier,
        )?)),
        ExpressionKind::And(exprs) => Ok(fold_left(
            EcBinop::And,
            translate_all(exprs, span, resolve_identifier)?,
        )),
        ExpressionKind::Or(exprs) => Ok(fold_left(
            EcBinop::Or,
            translate_all(exprs, span, resolve_identifier)?,
        )),
        ExpressionKind::Xor(exprs) => Ok(fold_left(
            EcBinop::Xor,
            translate_all(exprs, span, resolve_identifier)?,
        )),

        ExpressionKind::Sample(_) => Err(EcExportError::UnsupportedExpression {
            construct: "Sample (must already be a statement by the time EasyCrypt export runs)",
            span,
        }),
        ExpressionKind::StringLiteral(_) => unsupported_expr("StringLiteral", span),
        ExpressionKind::List(_) => unsupported_expr("List", span),
        ExpressionKind::Set(_) => unsupported_expr("Set", span),
        ExpressionKind::Inv(_) => unsupported_expr("Inv", span),
        ExpressionKind::Pow(_, _) => unsupported_expr("Pow", span),
        ExpressionKind::Sum(_) => unsupported_expr("Sum", span),
        ExpressionKind::Prod(_) => unsupported_expr("Prod", span),
        ExpressionKind::Any(_) => unsupported_expr("Any", span),
        ExpressionKind::All(_) => unsupported_expr("All", span),
        ExpressionKind::Union(_) => unsupported_expr("Union", span),
        ExpressionKind::Cut(_) => unsupported_expr("Cut", span),
        ExpressionKind::SetDiff(_) => unsupported_expr("SetDiff", span),
        ExpressionKind::Concat(_) => unsupported_expr("Concat", span),
    }
}

fn unsupported_expr(construct: &'static str, span: SourceSpan) -> Result<EcExpr, EcExportError> {
    Err(EcExportError::UnsupportedExpression { construct, span })
}

/// `BitsLiteral("0"/"1", Bits(n))` -> `zero_n`/`one_n`; `("empty", Bits(*))`
/// -> `zero`. The parser guarantees exactly these combinations
/// (`src/parser/package.rs`'s `literal_bits_zero`/`literal_bits_one` reject
/// `Bits(*)`, and `literal_empty_bitstring` only ever builds `Bits(*)`), so
/// any other combination reaching here is a translation-order bug, not
/// unsupported Domino source.
fn translate_bits_literal(literal: &str, ty: &Type) -> Result<EcExpr, EcExportError> {
    let TypeKind::Bits(count) = ty.kind() else {
        unreachable!("BitsLiteral must carry a Bits type, found {ty:?}");
    };
    match (literal, bits_suffix(count)) {
        ("0", Some(suffix)) => Ok(EcExpr::Var(format!("zero_{suffix}"))),
        ("1", Some(suffix)) => Ok(EcExpr::Var(format!("one_{suffix}"))),
        ("empty", None) => Ok(EcExpr::Var("zero".to_string())),
        (other, suffix) => unreachable!(
            "BitsLiteral({other:?}, Bits) with suffix {suffix:?} violates the parser's \
             zero/one/empty <-> width invariant"
        ),
    }
}

fn unop(
    op: EcUnop,
    inner: &Expression,
    span: SourceSpan,
    resolve_identifier: IdentifierResolver,
) -> Result<EcExpr, EcExportError> {
    Ok(EcExpr::Unop {
        op,
        arg: Box::new(translate_expr(inner, span, resolve_identifier)?),
    })
}

fn binop(
    op: EcBinop,
    lhs: &Expression,
    rhs: &Expression,
    span: SourceSpan,
    resolve_identifier: IdentifierResolver,
) -> Result<EcExpr, EcExportError> {
    let lhs = translate_expr(lhs, span, resolve_identifier)?;
    let rhs = translate_expr(rhs, span, resolve_identifier)?;
    Ok(EcExpr::Binop {
        op,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    })
}

fn translate_all(
    exprs: &[Expression],
    span: SourceSpan,
    resolve_identifier: IdentifierResolver,
) -> Result<Vec<EcExpr>, EcExportError> {
    exprs
        .iter()
        .map(|e| translate_expr(e, span, resolve_identifier))
        .collect()
}

/// Left-fold `exprs` into one `op`-chain: `[a, b, c]` -> `(a op b) op c`.
/// Domino's grammar never produces an empty `And`/`Or`/`Xor`/`Equals`.
fn fold_left(op: EcBinop, mut exprs: Vec<EcExpr>) -> EcExpr {
    assert!(!exprs.is_empty(), "Domino never produces an empty n-ary boolean expression");
    let first = exprs.remove(0);
    exprs.into_iter().fold(first, |acc, e| EcExpr::Binop {
        op,
        lhs: Box::new(acc),
        rhs: Box::new(e),
    })
}

/// `Equals([a, b])` -> `a = b`; `Equals([a, b, c, …])` -> adjacent-pairs
/// conjunction `a = b /\ b = c /\ …` (§3.2 — this appears in real code, not
/// just hypothetically: `4WHS/packages/KX.pkg.ssp`'s
/// `acc1 == acc2 == Some(true)`).
fn equals_adjacent_pairs(exprs: Vec<EcExpr>) -> EcExpr {
    let pairs: Vec<EcExpr> = exprs
        .windows(2)
        .map(|w| EcExpr::Binop {
            op: EcBinop::Eq,
            lhs: Box::new(w[0].clone()),
            rhs: Box::new(w[1].clone()),
        })
        .collect();
    fold_left(EcBinop::And, pairs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::from((3, 5))
    }

    fn no_resolver(_id: &Identifier, _span: SourceSpan) -> Result<EcExpr, EcExportError> {
        panic!("this test's expression tree contains no Identifier")
    }

    fn var(name: &str) -> EcExpr {
        EcExpr::Var(name.to_string())
    }

    fn int_lit(n: i64) -> Expression {
        Expression::integer(n)
    }

    fn theorem_const_identifier(name: &str, ty: Type) -> Identifier {
        use crate::identifier::theorem_ident::{TheoremConstIdentifier, TheoremIdentifier};
        Identifier::TheoremIdentifier(TheoremIdentifier::Const(TheoremConstIdentifier {
            theorem_name: "T".to_string(),
            name: name.to_string(),
            ty,
            inst_info: None,
        }))
    }

    // --- §3.1 type table ----------------------------------------------------

    #[test]
    fn type_integer() {
        assert_eq!(translate_type(&Type::integer(), span()).unwrap(), EcType::Int);
    }

    #[test]
    fn type_boolean() {
        assert_eq!(translate_type(&Type::boolean(), span()).unwrap(), EcType::Bool);
    }

    #[test]
    fn type_empty() {
        assert_eq!(translate_type(&Type::empty(), span()).unwrap(), EcType::Unit);
    }

    #[test]
    fn type_bits_identifier_width() {
        let id = theorem_const_identifier("n", Type::integer());
        let ty = Type::bits(CountSpec::Identifier(Box::new(id)));
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Named("bits_n".to_string())
        );
    }

    #[test]
    fn type_bits_literal_width() {
        let ty = Type::bits(CountSpec::Literal(256));
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Named("bits_256".to_string())
        );
    }

    #[test]
    fn type_bits_any() {
        let ty = Type::bits(CountSpec::Any);
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Named("bits".to_string())
        );
    }

    #[test]
    fn type_maybe() {
        let ty = Type::maybe(Type::integer());
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Option(Box::new(EcType::Int))
        );
    }

    #[test]
    fn type_maybe_maybe() {
        // §6 note: `Maybe(Maybe(T))` renders as `T option option` — legal,
        // no special case, just keep a test.
        let ty = Type::maybe(Type::maybe(Type::integer()));
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Option(Box::new(EcType::Option(Box::new(EcType::Int))))
        );
    }

    #[test]
    fn type_table() {
        let ty = Type::table(Type::integer(), Type::boolean());
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool))
        );
    }

    #[test]
    fn type_tuple() {
        let ty = Type::tuple(vec![Type::integer(), Type::boolean(), Type::integer()]);
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Tuple(vec![EcType::Int, EcType::Bool, EcType::Int])
        );
    }

    #[test]
    fn type_tuple_of_one_is_a_hard_error() {
        let ty = Type::tuple(vec![Type::integer()]);
        let err = translate_type(&ty, span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "1-element Tuple (EasyCrypt has no 1-tuples)",
                span: span(),
            }
        );
    }

    #[test]
    fn type_fn_curries() {
        let ty = Type::fun(vec![Type::integer(), Type::boolean()], Type::integer());
        assert_eq!(
            translate_type(&ty, span()).unwrap(),
            EcType::Fun(
                Box::new(EcType::Int),
                Box::new(EcType::Fun(Box::new(EcType::Bool), Box::new(EcType::Int)))
            )
        );
    }

    #[test]
    fn type_string_is_a_hard_error() {
        let err = translate_type(&Type::string(), span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "String",
                span: span(),
            }
        );
    }

    #[test]
    fn type_list_is_a_hard_error() {
        let err = translate_type(&Type::list(Type::integer()), span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "List",
                span: span(),
            }
        );
    }

    #[test]
    fn type_set_is_a_hard_error() {
        let err = translate_type(&Type::set(Type::integer()), span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "Set",
                span: span(),
            }
        );
    }

    #[test]
    fn type_addi_group_el_is_a_hard_error() {
        let ty = Type::from_kind(TypeKind::AddiGroupEl("G".to_string()));
        let err = translate_type(&ty, span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "AddiGroupEl",
                span: span(),
            }
        );
    }

    #[test]
    fn type_mult_group_el_is_a_hard_error() {
        let ty = Type::from_kind(TypeKind::MultGroupEl("G".to_string()));
        let err = translate_type(&ty, span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "MultGroupEl",
                span: span(),
            }
        );
    }

    #[test]
    fn type_user_defined_is_a_hard_error() {
        let ty = Type::from_kind(TypeKind::UserDefined("Foo".to_string()));
        let err = translate_type(&ty, span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "UserDefined",
                span: span(),
            }
        );
    }

    #[test]
    fn type_unknown_is_a_hard_error() {
        let err = translate_type(&Type::unknown(), span()).unwrap_err();
        assert_eq!(
            err,
            EcExportError::UnsupportedType {
                construct: "Unknown",
                span: span(),
            }
        );
    }

    // --- §3.2 expression table -----------------------------------------------

    #[test]
    fn expr_integer_literal() {
        let e = int_lit(42);
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Int(42)
        );
    }

    #[test]
    fn expr_boolean_literal() {
        let e = Expression::boolean(true);
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Bool(true)
        );
    }

    #[test]
    fn expr_bot() {
        let e = Expression::from_kind(ExpressionKind::Bot);
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Unit
        );
    }

    #[test]
    fn expr_bits_literal_zero_and_one() {
        let ty = Type::bits(CountSpec::Literal(256));
        let zero = Expression::from_kind(ExpressionKind::BitsLiteral("0".to_string(), ty.clone()));
        let one = Expression::from_kind(ExpressionKind::BitsLiteral("1".to_string(), ty));
        assert_eq!(
            translate_expr(&zero, span(), &mut no_resolver).unwrap(),
            var("zero_256")
        );
        assert_eq!(
            translate_expr(&one, span(), &mut no_resolver).unwrap(),
            var("one_256")
        );
    }

    #[test]
    fn expr_bits_literal_empty() {
        let ty = Type::bits(CountSpec::Any);
        let e = Expression::from_kind(ExpressionKind::BitsLiteral("empty".to_string(), ty));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            var("zero")
        );
    }

    #[test]
    fn expr_identifier_uses_the_resolver() {
        let e = Expression::from_kind(ExpressionKind::Identifier(Identifier::Generated(
            "x".to_string(),
            Type::integer(),
        )));
        let mut resolver = |id: &Identifier, s: SourceSpan| {
            assert_eq!(s, span());
            match id {
                Identifier::Generated(name, _) => Ok(EcExpr::Var(name.clone())),
                _ => unreachable!(),
            }
        };
        assert_eq!(
            translate_expr(&e, span(), &mut resolver).unwrap(),
            var("x")
        );
    }

    #[test]
    fn expr_none() {
        let e = Expression::from_kind(ExpressionKind::None(Type::integer()));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::None_(EcType::Int)
        );
    }

    #[test]
    fn expr_some() {
        let e = Expression::from_kind(ExpressionKind::Some(Box::new(int_lit(3))));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Some_(Box::new(EcExpr::Int(3)))
        );
    }

    #[test]
    fn expr_unwrap() {
        let e = Expression::from_kind(ExpressionKind::Unwrap(Box::new(int_lit(3))));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Oget(Box::new(EcExpr::Int(3)))
        );
    }

    #[test]
    fn expr_empty_table() {
        let e = Expression::from_kind(ExpressionKind::EmptyTable(Type::table(
            Type::integer(),
            Type::boolean(),
        )));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::MapEmpty
        );
    }

    #[test]
    fn expr_table_access() {
        let id = Identifier::Generated("t".to_string(), Type::table(Type::integer(), Type::boolean()));
        let e = Expression::from_kind(ExpressionKind::TableAccess(id, Box::new(int_lit(1))));
        let mut resolver = |id: &Identifier, _s: SourceSpan| match id {
            Identifier::Generated(name, _) => Ok(EcExpr::Var(name.clone())),
            _ => unreachable!(),
        };
        assert_eq!(
            translate_expr(&e, span(), &mut resolver).unwrap(),
            EcExpr::MapGet {
                map: Box::new(var("t")),
                key: Box::new(EcExpr::Int(1)),
            }
        );
    }

    #[test]
    fn expr_tuple() {
        let e = Expression::from_kind(ExpressionKind::Tuple(vec![int_lit(1), int_lit(2)]));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Tuple(vec![EcExpr::Int(1), EcExpr::Int(2)])
        );
    }

    #[test]
    fn expr_fncall() {
        let id = theorem_const_identifier("prf", Type::fun(vec![Type::integer()], Type::integer()));
        let e = Expression::from_kind(ExpressionKind::FnCall(id, vec![int_lit(1)]));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::App {
                head: "func_prf".to_string(),
                args: vec![EcExpr::Int(1)],
            }
        );
    }

    #[test]
    fn expr_not_and_neg() {
        let not = Expression::from_kind(ExpressionKind::Not(Box::new(Expression::boolean(true))));
        let neg = Expression::from_kind(ExpressionKind::Neg(Box::new(int_lit(1))));
        assert_eq!(
            translate_expr(&not, span(), &mut no_resolver).unwrap(),
            EcExpr::Unop {
                op: EcUnop::Not,
                arg: Box::new(EcExpr::Bool(true)),
            }
        );
        assert_eq!(
            translate_expr(&neg, span(), &mut no_resolver).unwrap(),
            EcExpr::Unop {
                op: EcUnop::Neg,
                arg: Box::new(EcExpr::Int(1)),
            }
        );
    }

    #[test]
    fn expr_arith_binops() {
        let cases: Vec<(fn(Box<Expression>, Box<Expression>) -> ExpressionKind, EcBinop)> = vec![
            (ExpressionKind::Add, EcBinop::Add),
            (ExpressionKind::Sub, EcBinop::Sub),
            (ExpressionKind::Mul, EcBinop::Mul),
            (ExpressionKind::Div, EcBinop::Div),
            (ExpressionKind::Mod, EcBinop::Mod),
            (ExpressionKind::LessThen, EcBinop::Lt),
            (ExpressionKind::LessThenEq, EcBinop::Le),
        ];
        for (make, op) in cases {
            let e = Expression::from_kind(make(Box::new(int_lit(1)), Box::new(int_lit(2))));
            assert_eq!(
                translate_expr(&e, span(), &mut no_resolver).unwrap(),
                EcExpr::Binop {
                    op,
                    lhs: Box::new(EcExpr::Int(1)),
                    rhs: Box::new(EcExpr::Int(2)),
                }
            );
        }
    }

    #[test]
    fn expr_greater_then_flips_to_less_then() {
        let e = Expression::from_kind(ExpressionKind::GreaterThen(
            Box::new(int_lit(1)),
            Box::new(int_lit(2)),
        ));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::Lt,
                lhs: Box::new(EcExpr::Int(2)),
                rhs: Box::new(EcExpr::Int(1)),
            }
        );
    }

    #[test]
    fn expr_greater_then_eq_flips_to_less_then_eq() {
        let e = Expression::from_kind(ExpressionKind::GreaterThenEq(
            Box::new(int_lit(1)),
            Box::new(int_lit(2)),
        ));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::Le,
                lhs: Box::new(EcExpr::Int(2)),
                rhs: Box::new(EcExpr::Int(1)),
            }
        );
    }

    #[test]
    fn expr_and_left_fold() {
        let e = Expression::from_kind(ExpressionKind::And(vec![
            Expression::boolean(true),
            Expression::boolean(false),
            Expression::boolean(true),
        ]));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::And,
                lhs: Box::new(EcExpr::Binop {
                    op: EcBinop::And,
                    lhs: Box::new(EcExpr::Bool(true)),
                    rhs: Box::new(EcExpr::Bool(false)),
                }),
                rhs: Box::new(EcExpr::Bool(true)),
            }
        );
    }

    #[test]
    fn expr_or_left_fold() {
        let e = Expression::from_kind(ExpressionKind::Or(vec![
            Expression::boolean(true),
            Expression::boolean(false),
            Expression::boolean(true),
        ]));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::Or,
                lhs: Box::new(EcExpr::Binop {
                    op: EcBinop::Or,
                    lhs: Box::new(EcExpr::Bool(true)),
                    rhs: Box::new(EcExpr::Bool(false)),
                }),
                rhs: Box::new(EcExpr::Bool(true)),
            }
        );
    }

    #[test]
    fn expr_xor_left_fold() {
        let e = Expression::from_kind(ExpressionKind::Xor(vec![
            Expression::boolean(true),
            Expression::boolean(false),
            Expression::boolean(true),
        ]));
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::Xor,
                lhs: Box::new(EcExpr::Binop {
                    op: EcBinop::Xor,
                    lhs: Box::new(EcExpr::Bool(true)),
                    rhs: Box::new(EcExpr::Bool(false)),
                }),
                rhs: Box::new(EcExpr::Bool(true)),
            }
        );
    }

    #[test]
    fn expr_equals_two_operands() {
        let e = Expression::equals(vec![int_lit(1), int_lit(2)]);
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::Eq,
                lhs: Box::new(EcExpr::Int(1)),
                rhs: Box::new(EcExpr::Int(2)),
            }
        );
    }

    #[test]
    fn expr_equals_three_operands_is_adjacent_pairs() {
        // acc1 == acc2 == Some(true), 4WHS/packages/KX.pkg.ssp.
        let e = Expression::equals(vec![int_lit(1), int_lit(2), int_lit(3)]);
        assert_eq!(
            translate_expr(&e, span(), &mut no_resolver).unwrap(),
            EcExpr::Binop {
                op: EcBinop::And,
                lhs: Box::new(EcExpr::Binop {
                    op: EcBinop::Eq,
                    lhs: Box::new(EcExpr::Int(1)),
                    rhs: Box::new(EcExpr::Int(2)),
                }),
                rhs: Box::new(EcExpr::Binop {
                    op: EcBinop::Eq,
                    lhs: Box::new(EcExpr::Int(2)),
                    rhs: Box::new(EcExpr::Int(3)),
                }),
            }
        );
    }

    #[test]
    fn expr_equals_four_operands_is_adjacent_pairs() {
        let e = Expression::equals(vec![int_lit(1), int_lit(2), int_lit(3), int_lit(4)]);
        let EcExpr::Binop {
            op: EcBinop::And,
            lhs,
            rhs,
        } = translate_expr(&e, span(), &mut no_resolver).unwrap()
        else {
            panic!("expected a top-level And");
        };
        // (1=2 /\ 2=3) /\ 3=4
        assert_eq!(
            *rhs,
            EcExpr::Binop {
                op: EcBinop::Eq,
                lhs: Box::new(EcExpr::Int(3)),
                rhs: Box::new(EcExpr::Int(4)),
            }
        );
        assert_eq!(
            *lhs,
            EcExpr::Binop {
                op: EcBinop::And,
                lhs: Box::new(EcExpr::Binop {
                    op: EcBinop::Eq,
                    lhs: Box::new(EcExpr::Int(1)),
                    rhs: Box::new(EcExpr::Int(2)),
                }),
                rhs: Box::new(EcExpr::Binop {
                    op: EcBinop::Eq,
                    lhs: Box::new(EcExpr::Int(2)),
                    rhs: Box::new(EcExpr::Int(3)),
                }),
            }
        );
    }

    #[test]
    fn expr_sample_is_a_hard_error() {
        let e = Expression::from_kind(ExpressionKind::Sample(Type::bits(CountSpec::Any)));
        let err = translate_expr(&e, span(), &mut no_resolver).unwrap_err();
        assert!(matches!(err, EcExportError::UnsupportedExpression { .. }));
    }

    macro_rules! hard_error_expr_test {
        ($name:ident, $kind:expr, $construct:expr) => {
            #[test]
            fn $name() {
                let e = Expression::from_kind($kind);
                let err = translate_expr(&e, span(), &mut no_resolver).unwrap_err();
                assert_eq!(
                    err,
                    EcExportError::UnsupportedExpression {
                        construct: $construct,
                        span: span(),
                    }
                );
            }
        };
    }

    hard_error_expr_test!(
        expr_string_literal_is_a_hard_error,
        ExpressionKind::StringLiteral("s".to_string()),
        "StringLiteral"
    );
    hard_error_expr_test!(
        expr_list_is_a_hard_error,
        ExpressionKind::List(vec![int_lit(1)]),
        "List"
    );
    hard_error_expr_test!(
        expr_set_is_a_hard_error,
        ExpressionKind::Set(vec![int_lit(1)]),
        "Set"
    );
    hard_error_expr_test!(
        expr_inv_is_a_hard_error,
        ExpressionKind::Inv(Box::new(int_lit(1))),
        "Inv"
    );
    hard_error_expr_test!(
        expr_pow_is_a_hard_error,
        ExpressionKind::Pow(Box::new(int_lit(1)), Box::new(int_lit(2))),
        "Pow"
    );
    hard_error_expr_test!(
        expr_sum_is_a_hard_error,
        ExpressionKind::Sum(Box::new(int_lit(1))),
        "Sum"
    );
    hard_error_expr_test!(
        expr_prod_is_a_hard_error,
        ExpressionKind::Prod(Box::new(int_lit(1))),
        "Prod"
    );
    hard_error_expr_test!(
        expr_any_is_a_hard_error,
        ExpressionKind::Any(Box::new(int_lit(1))),
        "Any"
    );
    hard_error_expr_test!(
        expr_all_is_a_hard_error,
        ExpressionKind::All(Box::new(int_lit(1))),
        "All"
    );
    hard_error_expr_test!(
        expr_union_is_a_hard_error,
        ExpressionKind::Union(Box::new(int_lit(1))),
        "Union"
    );
    hard_error_expr_test!(
        expr_cut_is_a_hard_error,
        ExpressionKind::Cut(Box::new(int_lit(1))),
        "Cut"
    );
    hard_error_expr_test!(
        expr_set_diff_is_a_hard_error,
        ExpressionKind::SetDiff(Box::new(int_lit(1))),
        "SetDiff"
    );
    hard_error_expr_test!(
        expr_concat_is_a_hard_error,
        ExpressionKind::Concat(vec![int_lit(1)]),
        "Concat"
    );

    // --- naming helpers -------------------------------------------------------

    #[test]
    fn bits_type_name_dash_to_underscore() {
        let id = theorem_const_identifier("key-width", Type::integer());
        assert_eq!(
            bits_type_name(&CountSpec::Identifier(Box::new(id))),
            "bits_key_width"
        );
    }

    #[test]
    fn func_op_name_dash_to_underscore() {
        assert_eq!(func_op_name("keys-computed"), "func_keys_computed");
    }
}
