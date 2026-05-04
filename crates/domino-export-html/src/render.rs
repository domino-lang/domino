use maud::{html, Markup, PreEscaped, Render};

use std::fs::read_to_string;

use sspverif::{
    expressions::{Expression, ExpressionKind},
    identifier::Identifier,
    package::{Composition, OracleDef, OracleSig, Package},
    packageinstance::PackageInstance,
    statement::{AssignmentRhs, CodeBlock, Pattern, Statement},
    theorem::GameInstance,
};

use crate::util::{ite_is_assert, join};

#[derive(Debug)]
pub(crate) struct Renderable<'a, T>(pub(crate) &'a T);

impl<'a, T> From<&'a T> for Renderable<'a, T> {
    fn from(val: &'a T) -> Self {
        Self(val)
    }
}

fn renderable<'a, T: 'a, I>(data: I) -> impl ExactSizeIterator<Item = Renderable<'a, T>>
where
    I: IntoIterator<Item = &'a T>,
    I::IntoIter: ExactSizeIterator,
{
    data.into_iter().map(|x| Renderable(x))
}

impl Render for Renderable<'_, Identifier> {
    fn render(&self) -> Markup {
        html! {
            mi {(self.0.ident())}
        }
    }
}

impl Render for Renderable<'_, GameInstance> {
    fn render(&self) -> Markup {
        html! {
            h2 {(self.0.name())}
            (Renderable(self.0.game()))
        }
    }
}

impl Render for Renderable<'_, Composition> {
    fn render(&self) -> Markup {
        let svg = read_to_string(format!("_build/html/Graph_{}.svg", self.0.name));
        html! {
            @if let Ok(svg) = svg {
                div .graph {
                    (PreEscaped(svg))
                }
            }
            div .packages {
                @for pkg in &self.0.pkgs {
                    (Renderable(pkg))
                }
            }
        }
    }
}

impl Render for Renderable<'_, PackageInstance> {
    fn render(&self) -> Markup {
        html! {
            div .package {
                h3 {(self.0.name)}
                (Renderable(&self.0.pkg))
            }
        }
    }
}

impl Render for Renderable<'_, Package> {
    fn render(&self) -> Markup {
        html! {
            @for oracle in &self.0.oracles {
                (Renderable(oracle))
            }
        }
    }
}

impl Render for Renderable<'_, OracleSig> {
    fn render(&self) -> Markup {
        html! {
            math {
                mi { (self.0.name) } "(" (join(",", &self.0.args.iter().map(|(name, _ty)| name).collect::<Vec<_>>())) ")"
            }
        }
    }
}

impl Render for Renderable<'_, OracleDef> {
    fn render(&self) -> Markup {
        html! {
            details ."oracle-def" {
                summary ."oracle-sig" {
                    (Renderable(&self.0.sig))
                }

                (Renderable(&self.0.code))
            }
        }
    }
}

impl Render for Renderable<'_, Expression> {
    fn render(&self) -> Markup {
        match self.0.kind() {
            ExpressionKind::Identifier(ident) => Renderable(ident).render(),
            ExpressionKind::IntegerLiteral(value) => html! {mn{(value)}},
            ExpressionKind::BooleanLiteral(value) => html! {mi{(value)}},
            ExpressionKind::Tuple(exprs) => html! { "(" (join(",", renderable(exprs)))  ")" },
            ExpressionKind::None(_) => PreEscaped("&#x22A5;".to_string()),
            ExpressionKind::And(terms) => html! { "(" (join("&and;", renderable(terms))) ")" },
            ExpressionKind::Or(terms) => html! {"(" (join("&or;", renderable(terms))) ")"},
            ExpressionKind::Equals(terms) => html! {"(" (join("=", renderable(terms))) ")"},
            ExpressionKind::Add(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {"+"} (Renderable(&**rhs))
            },
            ExpressionKind::Sub(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {"-"} (Renderable(&**rhs))
            },
            ExpressionKind::Mul(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {(PreEscaped("&sdot;"))} (Renderable(&**rhs))
            },
            ExpressionKind::Div(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {(PreEscaped("/"))} (Renderable(&**rhs))
            },
            ExpressionKind::GreaterThen(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {">"} (Renderable(&**rhs))
            },
            ExpressionKind::LessThen(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {"<"} (Renderable(&**rhs))
            },
            ExpressionKind::GreaterThenEq(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {(PreEscaped("&ge;"))} (Renderable(&**rhs))
            },
            ExpressionKind::LessThenEq(lhs, rhs) => html! {
                (Renderable(&**lhs)) mo {(PreEscaped("&le;"))} (Renderable(&**rhs))
            },
            ExpressionKind::TableAccess(ident, expr) => html! {
                (Renderable(ident)) "[" (Renderable(&**expr)) "]"
            },
            ExpressionKind::Some(expr) => Renderable(&**expr).render(),
            ExpressionKind::Not(expr) => html! { (PreEscaped("&not;")) (Renderable(&**expr)) },
            ExpressionKind::FnCall(name, exprs) => html! {
                mi{(Renderable(name))} "(" (join(",", renderable(exprs))) ")"
            },
            ExpressionKind::Unwrap(expr) => Renderable(&**expr).render(),
            ExpressionKind::EmptyTable(_) => html! {mi{"EmptyTable"}"()"},
            _ => todo!("{self:?}"),
        }
    }
}

impl Render for Renderable<'_, CodeBlock> {
    fn render(&self) -> Markup {
        html! {
            div ."code-block" {
                @for stmt in &self.0.0 {
                    (Renderable(stmt))
                }
            }
        }
    }
}

impl Render for Renderable<'_, Statement> {
    fn render(&self) -> Markup {
        match self.0 {
            Statement::Abort(_) => html! {
                math {mtext .keyword {"abort"}}
            },
            Statement::Return(None, _) => html! {
                math {mtext .keyword {"return"}}
            },
            Statement::Return(Some(val), _) => html! {
                math {mtext .keyword {(PreEscaped("return&nbsp;"))} (Renderable(val))}
            },
            Statement::Assignment(assign, _) => html! {
                math {(Renderable(&assign.pattern)) {mo {(PreEscaped("&larr;"))}} (Renderable(&assign.rhs))}
            },
            Statement::InvokeOracle(invoke) => html! {
                math {mi{(invoke.oracle_name)} "(" (join(",", renderable(&invoke.args))) ")"}
            },
            Statement::IfThenElse(ite) if ite_is_assert(ite) => html! {
                math {mtext .keyword {(PreEscaped("assert&nbsp;"))}  (Renderable(&ite.cond))}
            },
            Statement::IfThenElse(ite) => html! {
                math {mtext .keyword {(PreEscaped("if&nbsp;"))} (Renderable(&ite.cond))}
                (Renderable(&ite.then_block))
                    @if !ite.else_block.0.is_empty() {
                        math {mtext .keyword {"else"}}
                        (Renderable(&ite.else_block))
                    }
            },
            Statement::For(ident, lower, upper, block, _) => html! {
                math {mtext .keyword {(PreEscaped("for&nbsp;"))} (Renderable(lower)) mo{(PreEscaped("&le;"))} (Renderable(ident)) mo{"<"} (Renderable(upper))}
                (Renderable(block))
            },
        }
    }
}

impl Render for Renderable<'_, Pattern> {
    fn render(&self) -> Markup {
        match self.0 {
            Pattern::Ident(ident) => html! {(Renderable(ident))},
            Pattern::Table { ident, index } => {
                html! { (Renderable(ident)) "[" (Renderable(index)) "]"}
            }
            Pattern::Tuple(idents) => html! { "(" (join(",", renderable(idents))) ")" },
        }
    }
}

impl Render for Renderable<'_, AssignmentRhs> {
    fn render(&self) -> Markup {
        match self.0 {
            AssignmentRhs::Expression(expr) => Renderable(expr).render(),
            AssignmentRhs::Sample { ty, .. } => html! {
                mo{"$"} (ty)
            },
            AssignmentRhs::Invoke {
                oracle_name, args, ..
            } => html! {
                mi{(oracle_name)} "(" (join(",", renderable(args))) ")"
            },
        }
    }
}
