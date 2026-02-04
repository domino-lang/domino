// SPDX-License-Identifier: MIT OR Apache-2.0

use super::exprs::SmtExpr;
use crate::expressions::Expression;
use crate::expressions::ExpressionKind;
use crate::types::Type;
use crate::types::TypeKind;

impl From<Expression> for SmtExpr {
    fn from(expr: Expression) -> SmtExpr {
        match expr.into_kind() {
            ExpressionKind::EmptyTable(t) => match t.into_kind() {
                TypeKind::Table(idxty, valty) => (
                    (
                        "as",
                        "const",
                        ("Array", *idxty, Type::maybe(*valty.clone())),
                    ),
                    ("as", "mk-none", Type::maybe(*valty)),
                )
                    .into(),
                other => panic!("Empty table of type {other:?}"),
            },
            ExpressionKind::Unwrap(inner) => {
                panic!("found an unwrap and don't knwo what to do with it -- {inner:?}");
                //panic!("unwrap expressions need to be on the right hand side of an assign!");
                // TODO find a better way to present that error to the user.
            }
            ExpressionKind::Some(inner) => {
                SmtExpr::List(vec![SmtExpr::Atom("mk-some".into()), SmtExpr::from(*inner)])
            }
            ExpressionKind::None(inner) => SmtExpr::List(vec![
                SmtExpr::Atom("as".into()),
                SmtExpr::Atom("mk-none".into()),
                Type::maybe(inner).into(),
            ]),
            ExpressionKind::StringLiteral(litname) => SmtExpr::Atom(format!("\"{litname}\"")),
            ExpressionKind::BooleanLiteral(litname) => SmtExpr::Atom(litname),
            ExpressionKind::IntegerLiteral(litname) => SmtExpr::Atom(format!("{litname}")),
            ExpressionKind::Equals(exprs) => {
                let mut acc = vec![SmtExpr::Atom("=".to_string())];
                for expr in exprs {
                    acc.push(expr.clone().into());
                }

                SmtExpr::List(acc)
            }
            ExpressionKind::Add(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("+".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::Sub(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("-".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::Mul(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("*".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::Div(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("/".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::LessThen(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("<".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::GreaterThen(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom(">".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::LessThenEq(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("<=".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::GreaterThenEq(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom(">=".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            ExpressionKind::Not(expr) => {
                SmtExpr::List(vec![SmtExpr::Atom("not".to_string()), (*expr).into()])
            }
            ExpressionKind::And(vals) => SmtExpr::List({
                let mut list = vec![SmtExpr::Atom("and".to_owned())];
                for val in vals {
                    list.push(SmtExpr::from(val))
                }
                list
            }),
            ExpressionKind::Or(vals) => SmtExpr::List({
                let mut list = vec![SmtExpr::Atom("or".to_owned())];
                for val in vals {
                    list.push(SmtExpr::from(val))
                }
                list
            }),
            ExpressionKind::Xor(vals) => SmtExpr::List({
                let mut list = vec![SmtExpr::Atom("xor".to_owned())];
                for val in vals {
                    list.push(SmtExpr::from(val))
                }
                list
            }),
            ExpressionKind::Identifier(ident) => ident.into(),

            // TODO
            // I would love to use PackageStatePattern here, but in order to use the access
            // method, we need the Package, which we don't have here. We also need the type of
            // the variable. All this means we'd need a lot more context. The only way I see
            // how to introduce the context here withing the constraints of the Into trait
            // would be to have all the information inside the Identifier, ideally as
            // references.
            //
            // Having them as references would mean that Identifier gets a lifetime, and by
            // extension also Expression and probably Statement. This sounds like it would be
            // pretty cumbersome, but maybe necessary for a clean structure.
            //
            // For now I'll leave it be.
            //
            // TODO: We got rid of this variant of Identifier! Need to update to the current one(s)
            //
            // ExpressionKind::Identifier(Identifier::State(PackageState {
            //     name: ident_name,
            //     ref game_inst_name,
            //     ref pkg_inst_name,
            //     ..
            // })) => (
            //     format!("state-{game_inst_name}-{pkg_inst_name}-{ident_name}"),
            //     &SelfStatePattern,
            // )
            //     .into(),
            ExpressionKind::Bot => SmtExpr::Atom("bot".to_string()),
            ExpressionKind::TableAccess(table, index) => SmtExpr::List(vec![
                SmtExpr::Atom("select".into()),
                table.clone().into(),
                (*index).into(),
            ]),
            ExpressionKind::Tuple(exprs) => {
                let mut l = vec![SmtExpr::Atom(format!("mk-tuple{}", exprs.len()))];

                for expr in exprs {
                    l.push(expr.into())
                }

                SmtExpr::List(l)
            }
            /* I will leave this here for now, because it might turn out that
               we need a special case for this. But if we do, this is not it
               (because we got rid of the variant. It would be somethign else now)
            ExpressionKind::FnCall(
                Identifier::Parameter(PackageConst {
                    name_in_comp: name,
                    game_inst_name,
                    ..
                }),
                args,
            ) => {
                let fn_name = format!("__func-{game_inst_name}-{name}");
                let mut call = vec![SmtExpr::Atom(fn_name)];

                for expr in args {
                    call.push(expr.into());
                }

                SmtExpr::List(call)
            }
             */
            ExpressionKind::FnCall(id, exprs) => {
                let name_in_theorem = id.as_theorem_identifier().unwrap().ident_ref();
                let func_name = format!("<<func-{name_in_theorem}>>");

                SmtExpr::List(
                    Some(func_name.into())
                        .into_iter()
                        .chain(exprs.into_iter().map(|expr| expr.into()))
                        .collect(),
                )
            }
            ExpressionKind::List(inner) => {
                let t = inner[0].get_type();

                let nil = SmtExpr::List(vec![
                    SmtExpr::Atom("as".to_owned()),
                    SmtExpr::Atom("nil".to_owned()),
                    SmtExpr::List(vec![SmtExpr::Atom("List".to_owned()), t.into()]),
                ]);

                let mut lst = nil;

                for el in inner.iter().rev() {
                    lst =
                        SmtExpr::List(vec![SmtExpr::Atom("insert".into()), el.clone().into(), lst])
                }

                lst
            }
            ExpressionKind::Set(inner) => {
                let t = inner[0].get_type();

                let empty_set = SmtExpr::List(vec![
                    SmtExpr::List(vec![
                        SmtExpr::Atom("as".to_owned()),
                        SmtExpr::Atom("const".to_owned()),
                        SmtExpr::List(vec![SmtExpr::Atom("Set".to_owned()), t.into()]),
                    ]),
                    SmtExpr::Atom("false".to_string()),
                ]);

                let mut set = empty_set;

                for el in inner.iter().rev() {
                    set = SmtExpr::List(vec![
                        SmtExpr::Atom("store".into()),
                        set,
                        el.clone().into(),
                        SmtExpr::Atom("true".to_string()),
                    ])
                }

                set
            }
            expr => {
                panic!("not implemented: {expr:?}");
            }
        }
    }
}
