use crate::{
    expressions::Expression,
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
        match expr {
            Expression::EmptyTable(t) => {
                if let Type::Table(ty_idx, ty_val) = t {
                    let none = build_none(*ty_val.clone());
                    sspverif_smtlib::theories::array_ex::const_(*ty_idx, *ty_val, none)
                } else {
                    panic!("Empty table of type {t:?}")
                }
            }
            Expression::Unwrap(inner) => {
                panic!("found an unwrap and don't knwo what to do with it -- {inner:?}");
                //panic!("unwrap expressions need to be on the right hand side of an assign!");
                // TODO find a better way to present that error to the user.
            }
            Expression::Some(inner) => build_some(*inner),
            Expression::None(ty) => build_none(ty),

            Expression::StringLiteral(text) => StringLiteral::from(text).into_const().into(),
            Expression::IntegerLiteral(num) if num < 0 => {
                panic!("smt-lib does not support negative literals at the moment")
            }
            Expression::IntegerLiteral(num) => Numeral::from(num as u64).into_const().into(),
            Expression::BooleanLiteral(bit) => match bit.as_str() {
                "true" => theories::core::true_(),
                "false" => theories::core::false_(),
                _ => unreachable!(
                    "found a boolean literal '{bit}', the parse should have caught that"
                ),
            },

            Expression::Equals(exprs) => theories::core::eq(exprs),
            Expression::Add(lhs, rhs) => theories::ints::add(vec![*lhs, *rhs]),
            Expression::Sub(lhs, rhs) => theories::ints::sub(vec![*lhs, *rhs]),
            Expression::Mul(lhs, rhs) => theories::ints::mul(vec![*lhs, *rhs]),
            Expression::Div(lhs, rhs) => theories::ints::div(vec![*lhs, *rhs]),
            Expression::Mod(lhs, rhs) => theories::ints::modulo(*lhs, *rhs),
            Expression::Neg(expr) => theories::ints::negate(*expr),
            Expression::Not(expr) => theories::core::not(*expr),
            Expression::And(exprs) => theories::core::and(exprs),
            Expression::Or(exprs) => theories::core::or(exprs),
            Expression::Xor(exprs) => theories::core::xor(exprs),
            Expression::Identifier(ident) => ident.into(),
            Expression::Bot => "bot".into(),
            Expression::TableAccess(table, index) => theories::array_ex::select(table, *index),

            Expression::Tuple(exprs) => Term::Base(
                format!("mk-tuple{}", exprs.len()).into(),
                exprs.into_iter().map(|expr| expr.into()).collect(),
            ),
            Expression::List(exprs) => {
                let nil = QualifiedIdentifier("nil".into(), Some(ty.into())).into();

                exprs.into_iter().rev().fold(nil, |acc, cur| {
                    Term::Base("insert".into(), vec![acc, cur.into()])
                })
            }
            Expression::Set(exprs) => {
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
            Expression::FnCall(id, exprs) => {
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
                    Identifier::TheoremIdentifier(TheoremIdentifier::Const(TheoremConstIdentifier {
                        name,
                        ..
                    })) => {
                        format!("<<func-theorem-{name}>>")
                    }
                    other => unreachable!("unexpected identifier in function call: {other:?}"),
                };

                Term::Base(
                    func_name.into(),
                    exprs.into_iter().map(|e| e.into()).collect(),
                )
            }

            Expression::Inv(_) => todo!(),
            Expression::Pow(_, _) => todo!(),
            Expression::Sum(_) => todo!(),
            Expression::Prod(_) => todo!(),
            Expression::Any(_) => todo!(),
            Expression::All(_) => todo!(),
            Expression::Union(_) => todo!(),
            Expression::Cut(_) => todo!(),
            Expression::SetDiff(_) => todo!(),
            Expression::Concat(_) => todo!(),
            Expression::Sample(_) => todo!(),
        }
    }
}
