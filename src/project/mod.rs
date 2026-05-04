// SPDX-License-Identifier: MIT OR Apache-2.0

/**
 *  project is the high-level structure of sspverif.
 *
 *  here we assemble all the users' packages, assumptions, game hops and equivalence theorems.
 *  we also facilitate individual theorem steps here, and provide an interface for doing the whole theorem.
 *
 */
use std::path::PathBuf;

use error::Result;

use crate::parser::ast::Identifier;
use crate::{
    gamehops::{equivalence, GameHop},
    package::Composition,
    theorem::Theorem,
    transforms::Transformation,
    util::smtsolver::SmtSolverBackend,
};

use crate::ui::{
    LatexUI, LatexUIGameIterator, ProofstepUI, ProveProofstepUI, ProveTheoremUI, ProveUI,
};

mod consts;
mod load;

#[cfg(feature = "zipfile")]
pub mod zipfile;
#[cfg(feature = "zipfile")]
pub use zipfile::{ZipFiles, ZipProject};

pub mod directory;
pub use directory::{DirectoryFiles, DirectoryProject};

pub mod error;

pub trait Project: Sync {
    fn get_root_dir(&self) -> PathBuf;

    fn theorems(&self) -> impl ExactSizeIterator<Item = &String>;
    fn games(&self) -> impl ExactSizeIterator<Item = &String>;

    fn get_theorem(&self, name: &str) -> Option<&Theorem<'_>>;
    fn get_game(&self, name: &str) -> Option<&Composition>;

    fn read_input_file(&self, extension: &str) -> std::io::Result<String>;

    fn proofsteps(&self, ui: impl ProofstepUI) -> Result<()> {
        let mut theorem_keys: Vec<_> = self.theorems().collect();
        theorem_keys.sort();

        for theorem_key in theorem_keys.into_iter() {
            let theorem = self.get_theorem(theorem_key).unwrap();
            let max_width_left = theorem
                .game_hops
                .iter()
                .map(GameHop::left_game_instance_name)
                .map(str::len)
                .max()
                .unwrap_or(0);

            ui.println(&format!("{theorem_key}:"))?;
            for (i, game_hop) in theorem.game_hops.iter().enumerate() {
                match game_hop {
                    GameHop::Equivalence(eq) => {
                        let left_name = eq.left_name();
                        let right_name = eq.right_name();
                        let spaces = " ".repeat(max_width_left - left_name.len());
                        ui.println(&format!(
                            "{i}: Equivalence {left_name}{spaces} == {right_name}"
                        ))?;
                    }
                    GameHop::Reduction(red) => {
                        ui.println(&format!(
                            "{i}: Reduction   {} ~= {} using {}",
                            red.left().construction_game_instance_name().as_str(),
                            red.right().construction_game_instance_name().as_str(),
                            red.assumption_name()
                        ))?;
                    }
                    GameHop::Conjecture(conj) => {
                        ui.println(&format!(
                            "{i}: Conjecture   {} ~= {}",
                            conj.left_name().as_str(),
                            conj.right_name().as_str()
                        ))?;
                    }
                    GameHop::Hybrid(hybrid) => {
                        let hybrid_name = hybrid.hybrid_name().as_str();
                        ui.println(&format!("hybrid: {hybrid_name}"))?;
                    }
                }
            }
        }
        Ok(())
    }

    // we might want to return a theorem trace here instead
    // we could then extract the theorem viewer output and other useful info trom the trace
    fn prove(
        &self,
        ui: impl ProveUI,
        backend: &(impl SmtSolverBackend + Sync),
        transcript: bool,
        parallel: usize,
        req_theorem: &Option<String>,
        req_proofstep: Option<usize>,
        req_oracle: &Option<String>,
    ) -> Result<()>
    where
        Self: Sized,
    {
        let mut theorem_keys: Vec<_> = self.theorems().collect();
        theorem_keys.sort();

        for (theorem_key, mut ui) in theorem_keys
            .into_iter()
            .map(|theorem_name| (theorem_name, ui.start_theorem(theorem_name)))
            .collect::<Vec<_>>()
        {
            ui.start();
            let theorem = &self.get_theorem(theorem_key).unwrap();

            if let Some(ref req_theorem) = req_theorem {
                if theorem_key != req_theorem {
                    ui.finish();
                    continue;
                }
            }

            for (i, game_hop, mut ui) in theorem
                .game_hops
                .iter()
                .enumerate()
                .map(|(idx, game_hop)| (idx, game_hop, ui.start_proofstep(format!("{game_hop}"))))
                .collect::<Vec<_>>()
            {
                ui.start();
                if let Some(ref req_proofstep) = req_proofstep {
                    if i != *req_proofstep {
                        ui.finish();
                        continue;
                    }
                }

                match game_hop {
                    GameHop::Reduction(_) => {
                        ui.is_reduction();
                    }
                    GameHop::Conjecture(_) => {
                        ui.is_reduction();
                    }
                    GameHop::Equivalence(eq) => {
                        if parallel > 1 {
                            equivalence::verify_parallel(
                                self, &ui, eq, theorem, backend, transcript, parallel, req_oracle,
                            )?;
                        } else {
                            equivalence::verify(
                                self, &ui, eq, theorem, backend, transcript, req_oracle,
                            )?;
                        }
                    }
                    GameHop::Hybrid(hyb) => {
                        if parallel > 1 {
                            equivalence::verify_parallel(
                                self,
                                &ui,
                                hyb.equivalence(),
                                theorem,
                                backend,
                                transcript,
                                parallel,
                                req_oracle,
                            )?;
                        } else {
                            equivalence::verify(
                                self,
                                &ui,
                                hyb.equivalence(),
                                theorem,
                                backend,
                                transcript,
                                req_oracle,
                            )?;
                        }
                        //unimplemented!()
                    }
                }
                ui.finish();
            }

            ui.finish();
        }

        ui.finish();
        Ok(())
    }

    fn html(&self, backend: &Option<impl SmtSolverBackend>) -> Result<()> {
        let mut path = self.get_root_dir();
        path.push("_build/html/");
        std::fs::create_dir_all(&path)?;

        for (name, game) in &self.games {
            let (transformed, _) = crate::transforms::samplify::Transformation(game)
                .transform()
                .unwrap();
            let (transformed, _) = crate::transforms::resolveoracles::Transformation(&transformed)
                .transform()
                .unwrap();
            crate::writers::html::write_game_instance(game, &path)?;
        }
        Ok(())
    }

    #[cfg(feature = "latex-export")]
    fn latex(&self, ui: impl LatexUI, backend: &Option<impl SmtSolverBackend>) -> Result<()> {
        let mut path = self.get_root_dir();
        path.push("_build/latex/");
        std::fs::create_dir_all(&path)?;

        for name in self.games().ui_iter(&ui, "Exporting Games") {
            let game = self.get_game(name).unwrap();
            let (transformed, _) = crate::transforms::samplify::Transformation(game)
                .transform()
                .unwrap();
            let (transformed, _) = crate::transforms::resolveoracles::Transformation(&transformed)
                .transform()
                .unwrap();
            crate::writers::tex::writer::tex_write_composition_graph_file(
                backend,
                &transformed,
                name,
                path.as_path(),
            )?;
            for lossy in [true, false] {
                crate::writers::tex::writer::tex_write_composition(
                    lossy,
                    &transformed,
                    name,
                    path.as_path(),
                )?;
            }
        }
        
        for name in self.theorems().ui_iter(&ui, "Exporting Theorems") {
            let theorem = self.get_theorem(name).unwrap();
            for lossy in [true, false] {
                crate::writers::tex::tex_write_theorem(
                    backend,
                    lossy,
                    theorem,
                    name,
                    path.as_path(),
                )?;
            }
        }

        Ok(())
    }

    fn get_joined_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
        oracle_name: Option<&str>,
    ) -> Result<std::fs::File> {
        let mut path = self.get_root_dir();

        path.push("_build/code_eq/joined/");
        std::fs::create_dir_all(&path)?;

        if let Some(oracle_name) = oracle_name {
            path.push(format!(
                "{left_game_name}_{right_game_name}_{oracle_name}.smt2"
            ));
        } else {
            path.push(format!("{left_game_name}_{right_game_name}.smt2"));
        }
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }
}
