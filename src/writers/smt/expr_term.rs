// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    expressions::ExpressionKind,
    identifier::{
        game_ident::{GameConstIdentifier, GameIdentifier},
        pkg_ident::{PackageConstIdentifier, PackageIdentifier},
        theorem_ident::{TheoremConstIdentifier, TheoremIdentifier},
        Identifier,
    },
    types::Type,
};
use sspverif_smtlib::{
    syntax::{
        term::{QualifiedIdentifier, Term},
        tokens::{Numeral, StringLiteral},
    },
    theories,
};

fn build_none(ty: Type) -> Term {
    Term::Base(
        QualifiedIdentifier("mk-none".into(), Some(Type::Maybe(Box::new(ty)).into())),
        vec![],
    )
}

fn build_some<T: Into<Term>>(term: T) -> Term {
    Term::Base("mk-some".into(), vec![term.into()])
}

impl From<Expression> for Term {
    fn from(expr: Expression) -> Self {
        let ty = expr.get_type();
        match expr.into_kind() {
            ExpressionKind::EmptyTable(t) => {
                if let Type::Table(ty_idx, ty_val) = t {
                    let none = build_none(*ty_val.clone());
                    sspverif_smtlib::theories::array_ex::const_(*ty_idx, *ty_val, none)
                } else {
                    panic!("Empty table of type {t:?}")
                }
            }
            ExpressionKind::Unwrap(inner) => {
                panic!("found an unwrap and don't knwo what to do with it -- {inner:?}");
                //panic!("unwrap expressions need to be on the right hand side of an assign!");
                // TODO find a better way to present that error to the user.
            }
            ExpressionKind::Some(inner) => build_some(*inner),
            ExpressionKind::None(ty) => build_none(ty),

            ExpressionKind::StringLiteral(text) => StringLiteral::from(text).into_const().into(),
            ExpressionKind::IntegerLiteral(num) if num < 0 => {
                panic!("smt-lib does not support negative literals at the moment")
            }
            ExpressionKind::IntegerLiteral(num) => Numeral::from(num as u64).into_const().into(),
            ExpressionKind::BooleanLiteral(bit) => match bit.as_str() {
                "true" => theories::core::true_(),
                "false" => theories::core::false_(),
                _ => unreachable!(
                    "found a boolean literal '{bit}', the parse should have caught that"
                ),
            },

            ExpressionKind::GreaterThen(lhs, rhs) => theories::ints::gt(*lhs, *rhs),
            ExpressionKind::LessThen(lhs, rhs) => theories::ints::lt(*lhs, *rhs),
            ExpressionKind::GreaterThenEq(lhs, rhs) => theories::ints::gte(*lhs, *rhs),
            ExpressionKind::LessThenEq(lhs, rhs) => theories::ints::lte(*lhs, *rhs),
            ExpressionKind::Equals(exprs) => theories::core::eq(exprs),
            ExpressionKind::Add(lhs, rhs) => theories::ints::add(vec![*lhs, *rhs]),
            ExpressionKind::Sub(lhs, rhs) => theories::ints::sub(vec![*lhs, *rhs]),
            ExpressionKind::Mul(lhs, rhs) => theories::ints::mul(vec![*lhs, *rhs]),
            ExpressionKind::Div(lhs, rhs) => theories::ints::div(vec![*lhs, *rhs]),
            ExpressionKind::Mod(lhs, rhs) => theories::ints::modulo(*lhs, *rhs),
            ExpressionKind::Neg(expr) => theories::ints::negate(*expr),
            ExpressionKind::Not(expr) => theories::core::not(*expr),
            ExpressionKind::And(exprs) => theories::core::and(exprs),
            ExpressionKind::Or(exprs) => theories::core::or(exprs),
            ExpressionKind::Xor(exprs) => theories::core::xor(exprs),
            ExpressionKind::Identifier(ident) => ident.into(),
            ExpressionKind::Bot => "bot".into(),
            ExpressionKind::TableAccess(table, index) => theories::array_ex::select(table, *index),

            ExpressionKind::Tuple(exprs) => Term::Base(
                format!("mk-tuple{}", exprs.len()).into(),
                exprs.into_iter().map(|expr| expr.into()).collect(),
            ),
            ExpressionKind::List(exprs) => {
                let nil = QualifiedIdentifier("nil".into(), Some(ty.into())).into();

                exprs.into_iter().rev().fold(nil, |acc, cur| {
                    Term::Base("insert".into(), vec![acc, cur.into()])
                })
            }
            ExpressionKind::Set(exprs) => {
                let empty_set = Term::Base(
                    QualifiedIdentifier("const".into(), Some(ty.into())),
                    vec![theories::core::false_()],
                );

                exprs.into_iter().fold(empty_set, |set, el| {
                    Term::Base(
                        "store".into(),
                        vec![set, el.into(), theories::core::true_()],
                    )
                })
            }
            ExpressionKind::FnCall(id, exprs) => {
                let func_name = match id {
                    Identifier::PackageIdentifier(PackageIdentifier::Const(
                        PackageConstIdentifier {
                            name,
                            game_inst_name: Some(game_inst_name),
                            pkg_inst_name: Some(pkg_inst_name),
                            ..
                        },
                    )) => {
                        format!("<<func-pkg-{game_inst_name}-{pkg_inst_name}-{name}>>")
                    }

                    Identifier::GameIdentifier(GameIdentifier::Const(GameConstIdentifier {
                        name,
                        game_inst_name: Some(game_inst_name),
                        ..
                    })) => {
                        format!("<<func-game-{game_inst_name}-{name}>>")
                    }
                    Identifier::TheoremIdentifier(TheoremIdentifier::Const(
                        TheoremConstIdentifier { name, .. },
                    )) => {
                        format!("<<func-theorem-{name}>>")
                    }
                    other => unreachable!("unexpected identifier in function call: {other:?}"),
                };

                Term::Base(
                    func_name.into(),
                    exprs.into_iter().map(|e| e.into()).collect(),
                )
            }

            ExpressionKind::Inv(_) => todo!(),
            ExpressionKind::Pow(_, _) => todo!(),
            ExpressionKind::Sum(_) => todo!(),
            ExpressionKind::Prod(_) => todo!(),
            ExpressionKind::Any(_) => todo!(),
            ExpressionKind::All(_) => todo!(),
            ExpressionKind::Union(_) => todo!(),
            ExpressionKind::Cut(_) => todo!(),
            ExpressionKind::SetDiff(_) => todo!(),
            ExpressionKind::Concat(_) => todo!(),
            ExpressionKind::Sample(_) => todo!(),
        }
    }
}
