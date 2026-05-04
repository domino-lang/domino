use maud::{html, Markup, PreEscaped, Render};
use std::fs::File;
use std::path::Path;
use std::io::Write;
use std::fmt::Debug;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::Identifier,
    theorem::GameInstance,
    package::{OracleDef, OracleSig, Package, Composition},
    packageinstance::PackageInstance,
    statement::{AssignmentRhs, CodeBlock, Pattern, Statement},
};

pub fn render_oracle(oracle: &OracleDef) -> String {
    oracle.render().into()
}


pub fn write_game_instance(instance: &Composition, target: &Path) -> std::io::Result<()> {
    let fname = target.join(format!(
        "GameInstance_{}.html",
        instance.name,
    ));
    let mut file = File::create(fname.clone())?;

    write!(file, "{}", instance.render().into_string())
}

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
        html!{
            @for pkg in &self.pkgs {
                (pkg)
            }
        }
    }
}

impl Render for PackageInstance {
    fn render(&self) -> Markup {
        html! {
            h3 {(self.name)}
            (self.pkg)
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
            div #"oracle-sig" {
                math {
                    mi { (self.name) } "(" (join(",", &self.args.iter().map(|(name, _ty)| name).collect::<Vec<_>>())) ")"
                }
            }
        }
    }
}

impl Render for OracleDef {
    fn render(&self) -> Markup {
        html! {
            div #"oracle-def" {
                (self.sig) (self.code)
            }
        }
    }
}

impl Render for Expression {
    fn render(&self) -> Markup {
        
        match self.kind() {
            ExpressionKind::Identifier(ident) => ident.render(),
            ExpressionKind::Tuple(exprs) => html!{ "(" (join(",", exprs))  ")" },
            ExpressionKind::IntegerLiteral(value) => html!{mn{(value)}},
            ExpressionKind::Bot => PreEscaped("&#x22A5;".to_string()),
            ExpressionKind::And(terms) => join("&and;", terms),
            ExpressionKind::Or(terms) => join("&or;", terms),
            ExpressionKind::Equals(terms) => join("=", terms),
            ExpressionKind::Add(lhs, rhs) => html! {
                (lhs) mo {"+"} (rhs)
            },
            _ => todo!("{self:?}"),
        }
    }
}

impl Render for CodeBlock {
    fn render(&self) -> Markup {
        html! {
            div #"code-block" {
                @for stmt in &self.0 {
                    p #statement {
                        (stmt)
                    }
                }
            }
        }
    }
}

impl Render for Statement {
    fn render(&self) -> Markup {
        dbg!(&self);
        
        match self {
            Statement::Abort(_) => html! {
                math {mi #keyword {"abort"}}
            },
            Statement::Return(None, _) => html! {
                math {mi #keyword {"return"}}
            },
            Statement::Return(Some(val), _) => html! {
                math {mi #keyword {"return"} (val)}
            },
            Statement::Assignment(assign, _) => html! {
                math {(assign.pattern) (PreEscaped("&larr;")) (assign.rhs)}
            },
            Statement::InvokeOracle(invoke) => html! {
                math {mi{(invoke.oracle_name)} "(" (join(",", &invoke.args)) ")"}
            },
            Statement::IfThenElse(ite) => html! {
                math {mi #keyword {"if"} (ite.cond)}
                (ite.then_block)
                    @if !ite.else_block.0.is_empty() {
                        math {mi #keyword {"else"}}
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
            Pattern::Tuple(idents) => join(",", idents),
        }
    }
}

impl Render for AssignmentRhs {
    fn render(&self) -> Markup {
        match self {
            AssignmentRhs::Expression(expr) => expr.render(),
            AssignmentRhs::Sample { ty, .. } => html! {
                (ty)
            },
            AssignmentRhs::Invoke {
                oracle_name, args, ..
            } => html! {
                mi{(oracle_name)} "(" (join(",", args)) ")"
            },
        }
    }
}

fn join<V: Render + Debug>(with: &str, values: &[V]) -> Markup {
    dbg!(values);
        

    if values.is_empty() {
        return html!{};
    }
    if values.len() == 1 {
        return html!{(values[0])};
    }
    let prefix = html! {
        @for value in &values[..(values.len()-1)] {
            (value) mo{(with)}
        }
    };
    html! {(prefix) (values[values.len()-1])}
}
