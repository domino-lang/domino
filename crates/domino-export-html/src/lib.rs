// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]

use maud::{html, PreEscaped, Render, DOCTYPE};

use std::fs::File;
use std::io::Write;
use std::path::Path;

mod graph;
mod render;
mod util;

use sspverif::{
    transforms::Transformation,
    package::{Composition, OracleDef},
    theorem::Theorem,
    project::{Project, error::Result, DirectoryProject},
    util::smtsolver::SmtSolverBackend,
};

use crate::render::Renderable;

pub trait HtmlProject : Project {
    fn html(&self, backend: &Option<impl SmtSolverBackend>) -> Result<()> {
        let mut path = self.get_root_dir();
        path.push("_build/html/");
        std::fs::create_dir_all(&path)?;

        for name in self.games() {
            let game = self.get_game(name).unwrap();
            let (transformed, _) = sspverif::transforms::samplify::Transformation(game)
                .transform()
                .unwrap();
            let (transformed, _) = sspverif::transforms::resolveoracles::Transformation(&transformed)
                .transform()
                .unwrap();
            write_game_instance(&path, backend, &transformed)?;
        }
        for name in self.theorems() {
            let theorem = self.get_theorem(name).unwrap();
            write_theorem(&path, backend, theorem)?;
        }
        Ok(())
    }
}

impl HtmlProject for DirectoryProject<'_> {}


pub fn render_oracle(oracle: &OracleDef) -> String {
    Renderable(oracle).render().into()
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
                (instance.name())
            }
            style type="text/css" {
                (PreEscaped(include_str!("assets/domino.css")))
            }
        }
        body{
            h1 {(instance.name())}
            (Renderable(instance))
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
            graph::write_composition_graph(target, backend, instance.game())?;
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
                    summary { h2 {(instance.name())} }
                    (Renderable(instance.game()))
                }
            }
        }
    };

    write!(file, "{}", content.into_string())
}
