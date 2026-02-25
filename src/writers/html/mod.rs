use maud::{html, PreEscaped, Render, DOCTYPE};

use std::fs::File;
use std::io::Write;
use std::path::Path;

pub mod graph;
pub mod render;
mod util;

use crate::{
    package::{Composition, OracleDef},
    theorem::Theorem,
    util::smtsolver::SmtSolverBackend,
};

pub fn render_oracle(oracle: &OracleDef) -> String {
    oracle.render().into()
}

pub fn write_game_instance(
    target: &Path,
    backend: &Option<impl SmtSolverBackend>,
    instance: &Composition,
) -> std::io::Result<()> {
    util::ensure_css_file(target)?;
    if let Some(backend) = backend {
        graph::write_composition_graph(target, backend, instance)?;
    }

    let fname = target.join(format!("GameInstance_{}.html", instance.name,));
    let mut file = File::create(fname.clone())?;

    let content = html! {
        (DOCTYPE)
        head {
            title {
                (instance.name)
            }
            style type="text/css" {
                (PreEscaped(include_str!("assets/domino.css")))
            }
        }
        body{
            h1 {(instance.name)}
            (instance)
        }
    };

    write!(file, "{}", content.into_string())
}
pub fn write_theorem(
    target: &Path,
    backend: &Option<impl SmtSolverBackend>,
    theorem: &Theorem,
) -> std::io::Result<()> {
    util::ensure_css_file(target)?;
    if let Some(backend) = backend {
        for instance in &theorem.instances {
            graph::write_composition_graph(target, backend, &instance.game)?;
        }
    }

    let fname = target.join(format!("Theorem_{}.html", theorem.name,));
    let mut file = File::create(fname.clone())?;

    let content = html! {
        (DOCTYPE)
        head {
            title {
                (theorem.name)
            }
            style type="text/css" {
                (PreEscaped(include_str!("assets/domino.css")))
            }
        }
        body{
            h1 {(theorem.name)}
            @for instance in &theorem.instances {
                details {
                    summary { h2 {(instance.name)} }
                    (instance.game)
                }
            }
        }
    };

    write!(file, "{}", content.into_string())
}
