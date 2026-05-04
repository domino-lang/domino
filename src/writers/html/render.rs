use maud::{html, Markup, PreEscaped, Render};

use std::fs::read_to_string;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::Identifier,
    package::{Composition, OracleDef, OracleSig, Package},
    packageinstance::PackageInstance,
    statement::{AssignmentRhs, CodeBlock, Pattern, Statement},
    theorem::GameInstance,
    writers::html::util::{ite_is_assert, join},
};

impl Render for Identifier {
    fn render(&self) -> Markup {
        html! {
            mi {(self.ident())}
        }
    }
}

impl Render for GameInstance {
    fn render(&self) -> Markup {
        html! {
            h2 {(self.name)}
            (self.game)
        }
    }
}

impl Render for Composition {
    fn render(&self) -> Markup {
        let svg = read_to_string(format!("_build/html/Graph_{}.svg", self.name));
        html! {
            @if let Ok(svg) = svg {
                div .graph {
                    (PreEscaped(svg))
                }
            }
            div .packages {
                @for pkg in &self.pkgs {
                    (pkg)
                }
            }
        }
    }
}

impl Render for PackageInstance {
    fn render(&self) -> Markup {
        html! {
            div .package {
                h3 {(self.name)}
                (self.pkg)
            }
        }
    }
}

impl Render for Package {
    fn render(&self) -> Markup {
        html! {
            @for oracle in &self.oracles {
                (oracle)
            }
        }
    }
}

impl Render for OracleSig {
    fn render(&self) -> Markup {
        html! {
            math {
                mi { (self.name) } "(" (join(",", &self.args.iter().map(|(name, _ty)| name).collect::<Vec<_>>())) ")"
            }
        }
    }
}

impl Render for OracleDef {
    fn render(&self) -> Markup {
        html! {
            details ."oracle-def" {
                summary ."oracle-sig" {
                    (self.sig)
                }

                (self.code)
            }
        }
    }
}

impl Render for Expression {
    fn render(&self) -> Markup {
        match self.kind() {
            ExpressionKind::Identifier(ident) => ident.render(),
            ExpressionKind::IntegerLiteral(value) => html! {mn{(value)}},
            ExpressionKind::BooleanLiteral(value) => html! {mi{(value)}},
            ExpressionKind::Tuple(exprs) => html! { "(" (join(",", exprs))  ")" },
            ExpressionKind::None(_) => PreEscaped("&#x22A5;".to_string()),
            ExpressionKind::And(terms) => html! { "(" (join("&and;", terms)) ")" },
            ExpressionKind::Or(terms) => html! {"(" (join("&or;", terms)) ")"},
            ExpressionKind::Equals(terms) => html! {"(" (join("=", terms)) ")"},
            ExpressionKind::Add(lhs, rhs) => html! {
                (lhs) mo {"+"} (rhs)
            },
            ExpressionKind::TableAccess(ident, expr) => html! {
                (ident) "[" (expr) "]"
            },
            ExpressionKind::Some(expr) => expr.render(),
            ExpressionKind::Not(expr) => html! { (PreEscaped("&not;")) (expr) },
            ExpressionKind::FnCall(name, exprs) => html! {
                mi{(name)} "(" (join(",", exprs)) ")"
            },
            ExpressionKind::Unwrap(expr) => expr.render(),
            _ => todo!("{self:?}"),
        }
    }
}

impl Render for CodeBlock {
    fn render(&self) -> Markup {
        html! {
            div ."code-block" {
                @for stmt in &self.0 {
                    (stmt)
                }
            }
        }
    }
}

impl Render for Statement {
    fn render(&self) -> Markup {
        match self {
            Statement::Abort(_) => html! {
                math {mtext .keyword {"abort"}}
            },
            Statement::Return(None, _) => html! {
                math {mtext .keyword {"return"}}
            },
            Statement::Return(Some(val), _) => html! {
                math {mtext .keyword {"return "} (val)}
            },
            Statement::Assignment(assign, _) => html! {
                math {(assign.pattern) (PreEscaped("&larr;")) (assign.rhs)}
            },
            Statement::InvokeOracle(invoke) => html! {
                math {mi{(invoke.oracle_name)} "(" (join(",", &invoke.args)) ")"}
            },
            Statement::IfThenElse(ite) if ite_is_assert(ite) => html! {
                math {mtext .keyword {"assert"} " " (ite.cond)}
            },
            Statement::IfThenElse(ite) => html! {
                math {mtext .keyword {"if "} " " (ite.cond)}
                (ite.then_block)
                    @if !ite.else_block.0.is_empty() {
                        math {mtext .keyword {"else"}}
                        (ite.else_block)
                    }
            },
            Statement::For(_ident, _lower, _upper, _block, _) => todo!(),
        }
    }
}

impl Render for Pattern {
    fn render(&self) -> Markup {
        match self {
            Pattern::Ident(ident) => html! {(ident)},
            Pattern::Table { ident, index } => html! { (ident) "[" (index) "]"},
            Pattern::Tuple(idents) => html! { "(" (join(",", idents)) ")" },
        }
    }
}

impl Render for AssignmentRhs {
    fn render(&self) -> Markup {
        match self {
            AssignmentRhs::Expression(expr) => expr.render(),
            AssignmentRhs::Sample { ty, .. } => html! {
                mo{"$"} (ty)
            },
            AssignmentRhs::Invoke {
                oracle_name, args, ..
            } => html! {
                mi{(oracle_name)} "(" (join(",", args)) ")"
            },
        }
    }
}
