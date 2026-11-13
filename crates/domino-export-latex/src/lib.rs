// SPDX-License-Identifier: MIT OR Apache-2.0

// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]

use sspverif::{
    transforms::Transformation,
    util::smtsolver::SmtSolverBackend,
    project::{Project, error::Result, DirectoryProject},
    ui::{LatexUI, LatexUIGameIterator},
};

pub(crate) mod label;
pub(crate) mod tikzgraph;
pub mod writer;

pub use writer::tex_write_theorem;

pub trait LatexProject : Project {
    fn latex(&self, ui: impl LatexUI, backend: &Option<impl SmtSolverBackend>) -> Result<()> {
        let mut path = self.get_root_dir();
        path.push("_build/latex/");
        std::fs::create_dir_all(&path)?;

        for name in self.games().ui_iter(&ui, "Exporting Games") {
            let game = self.get_game(name).unwrap();
            let (transformed, _) = sspverif::transforms::samplify::Transformation(game)
                .transform()
                .unwrap();
            let (transformed, _) =
                sspverif::transforms::resolveoracles::Transformation(&transformed)
                    .transform()
                    .unwrap();
            writer::tex_write_composition_graph_file(backend, &transformed, name, path.as_path())?;
            for lossy in [true, false] {
                writer::tex_write_composition(lossy, &transformed, name, path.as_path())?;
            }
        }

        for name in self.theorems().ui_iter(&ui, "Exporting Theorems") {
            let theorem = self.get_theorem(name).unwrap();
            for lossy in [true, false] {
                tex_write_theorem(backend, lossy, theorem, name, path.as_path())?;
            }
        }

        Ok(())
    }
}

impl LatexProject for DirectoryProject<'_> {}
