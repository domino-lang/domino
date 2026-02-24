// SPDX-License-Identifier: MIT OR Apache-2.0

/**
 *  project is the high-level structure of sspverif.
 *
 *  here we assemble all the users' packages, assumptions, game hops and equivalence theorems.
 *  we also facilitate individual theorem steps here, and provide an interface for doing the whole theorem.
 *
 */
use std::path::Path;

use itertools::Itertools;

use std::fmt::Write;
use std::io::{Read, Seek};

use error::{Error, Result};

use crate::parser::ast::Identifier;
use crate::parser::package::handle_pkg;
use crate::parser::SspParser;
use crate::{
    gamehops::{equivalence, GameHop},
    package::{Composition, Package},
    theorem::Theorem,
    transforms::Transformation,
    util::prover::ProverBackend,
};

use crate::ui::{BaseUI, TheoremUI};

pub const PROJECT_FILE: &str = "ssp.toml";

pub const PACKAGES_DIR: &str = "packages";
pub const GAMES_DIR: &str = "games";
pub const THEOREM_DIR: &str = "theorem";
pub const ASSUMPTIONS_DIR: &str = "assumptions";

pub const PACKAGE_EXT: &str = ".pkg.ssp";
pub const GAME_EXT: &str = ".comp.ssp"; // TODO maybe change this to .game.ssp later, and also rename the Composition type

mod load;
mod resolve;

pub mod error;

mod directory;
pub use directory::DirectoryProject;
pub use directory::ZipProject;

pub trait Project: Sync {
    fn proofsteps(&self, mut to: impl std::fmt::Write) -> Result<()> {
        let mut theorem_keys: Vec<_> = self.theorems().collect();
        theorem_keys.sort();

        for theorem_key in theorem_keys.into_iter() {
            let theorem = &self.get_theorem(theorem_key).unwrap();
            let max_width_left = theorem
                .game_hops
                .iter()
                .map(GameHop::left_game_instance_name)
                .map(str::len)
                .max()
                .unwrap_or(0);

            writeln!(to, "{theorem_key}:")?;
            for (i, game_hop) in theorem.game_hops.iter().enumerate() {
                match game_hop {
                    GameHop::Equivalence(eq) => {
                        let left_name = eq.left_name();
                        let right_name = eq.right_name();
                        let spaces = " ".repeat(max_width_left - left_name.len());
                        writeln!(to, "{i}: Equivalence {left_name}{spaces} == {right_name}")?;
                    }
                    GameHop::Reduction(red) => {
                        writeln!(
                            to,
                            "{i}: Reduction   {} ~= {} using {}",
                            red.left().construction_game_instance_name().as_str(),
                            red.right().construction_game_instance_name().as_str(),
                            red.assumption_name()
                        )?;
                    }
                    GameHop::Conjecture(conj) => {
                        writeln!(
                            to,
                            "{i}: Conjecture   {} ~= {}",
                            conj.left_name().as_str(),
                            conj.right_name().as_str()
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn prove(
        &self,
        ui: impl BaseUI,
        backend: ProverBackend,
        transcript: bool,
        parallel: usize,
        req_theorem: &Option<String>,
        req_proofstep: Option<usize>,
        req_oracle: &Option<String>,
    ) -> Result<()>
    where
        Self: Sized,
    {
        let mut theorem_keys = self.theorems().sorted();

        let mut ui = ui.into_theorem_ui(theorem_keys.len().try_into().unwrap());

        for theorem_key in theorem_keys {
            let theorem = &self.get_theorem(theorem_key).unwrap();
            ui.start_theorem(&theorem.name, theorem.game_hops.len().try_into().unwrap());

            if let Some(ref req_theorem) = req_theorem {
                if theorem_key != req_theorem {
                    ui.finish_theorem(&theorem.name);
                    continue;
                }
            }

            for (i, game_hop) in theorem.game_hops.iter().enumerate() {
                ui.start_proofstep(&theorem.name, &format!("{game_hop}"));

                if let Some(ref req_proofstep) = req_proofstep {
                    if i != *req_proofstep {
                        ui.finish_proofstep(&theorem.name, &format!("{game_hop}"));
                        continue;
                    }
                }

                match game_hop {
                    GameHop::Reduction(_) => {
                        ui.proofstep_is_reduction(&theorem.name, &format!("{game_hop}"));
                    }
                    GameHop::Conjecture(_) => {
                        ui.proofstep_is_reduction(&theorem.name, &format!("{game_hop}"));
                    }
                    GameHop::Equivalence(eq) => {
                        if parallel > 1 {
                            equivalence::verify_parallel(
                                self, &mut ui, eq, theorem, backend, transcript, parallel,
                                req_oracle,
                            )?;
                        } else {
                            equivalence::verify(
                                self, &mut ui, eq, theorem, backend, transcript, req_oracle,
                            )?;
                        }
                    }
                }
                ui.finish_proofstep(&theorem.name, &format!("{game_hop}"));
            }

            ui.finish_theorem(&theorem.name);
        }

        Ok(())
    }

    fn latex(&self, backend: Option<ProverBackend>) -> Result<()>
    where
        Self: Sized,
    {
        for (name, game) in self
            .games()
            .map(|name| (name, self.get_game(name).unwrap()))
        {
            let (transformed, _) = crate::transforms::samplify::Transformation(game)
                .transform()
                .unwrap();
            let (transformed, _) = crate::transforms::resolveoracles::Transformation(&transformed)
                .transform()
                .unwrap();
            for lossy in [true, false] {
                crate::writers::tex::writer::tex_write_composition(
                    &backend,
                    lossy,
                    &transformed,
                    name,
                    self,
                )?;
            }
        }

        for (name, theorem) in self
            .theorems()
            .map(|name| (name, self.get_theorem(name).unwrap()))
        {
            for lossy in [true, false] {
                crate::writers::tex::writer::tex_write_theorem(
                    &backend, lossy, theorem, name, self,
                )?;
            }
        }

        Ok(())
    }

    fn print_wire_check_smt(&self, game_name: &str, _dst_idx: usize) {
        let _game = self.get_game(game_name).unwrap();
        // for command in wire_theorems::build_smt(&game, dst_idx) {
        //     println!("{}", command);
        // }
    }

    fn theorems(&self) -> impl Iterator<Item = &String>;
    fn get_theorem(&self, name: &str) -> Option<&Theorem>;

    fn games(&self) -> impl Iterator<Item = &String>;
    fn get_game(&self, name: &str) -> Option<&Composition>;

    fn read_input_file(&self, extension: &str) -> std::io::Result<String>;

    fn get_output_file(
        &self,
        extension: String,
    ) -> std::io::Result<impl std::io::Write + Send + Sync + 'static>;

    fn get_joined_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
        oracle_name: Option<&str>,
    ) -> std::io::Result<impl std::io::Write + Send + Sync + 'static> {
        let extension = if let Some(oracle_name) = oracle_name {
            format!("code_eq/joined/{left_game_name}_{right_game_name}_{oracle_name}.smt2")
        } else {
            format!("code_eq/joined/{left_game_name}_{right_game_name}.smt2")
        };
        self.get_output_file(extension)
    }
}
