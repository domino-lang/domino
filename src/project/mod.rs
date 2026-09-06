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
    gamehops::{equivalence::EquivalenceSmtDriver, GameHop},
    package::{Composition, Package},
    package_invariant::{
        self, PackageInvariantContext, PackageInvariantSmtDriver, UI_SECTION_NAME,
    },
    theorem::Theorem,
    transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform, Transformation},
    util::smtsolver::SmtSolverBackend,
    writers::smt::contexts::EquivalenceContext,
};

use crate::ui::{indicatif::IndicatifTheoremUI, TheoremUI};

mod consts;
mod load;

#[cfg(feature = "zipfile")]
pub mod zipfile;
#[cfg(feature = "zipfile")]
pub use zipfile::{ZipFiles, ZipProject};

pub mod directory;
pub use directory::{DirectoryFiles, DirectoryProject};

pub mod error;

pub trait Project {
    fn get_root_dir(&self) -> PathBuf;

    fn theorems(&self) -> impl Iterator<Item = &str>;
    fn packages(&self) -> impl Iterator<Item = &str>;
    fn games(&self) -> impl Iterator<Item = &str>;

    fn get_theorem(&self, name: &str) -> Option<&Theorem<'_>>;
    fn get_game(&self, name: &str) -> Option<&Composition>;
    fn get_package(&self, name: &str) -> Option<&Package>;

    fn read_input_file(&self, extension: &str) -> std::io::Result<String>;

    fn proofsteps(&self) -> Result<()> {
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

            println!("{theorem_key}:");
            for (i, game_hop) in theorem.game_hops.iter().enumerate() {
                match game_hop {
                    GameHop::Equivalence(eq) => {
                        let left_name = eq.left_name();
                        let right_name = eq.right_name();
                        let spaces = " ".repeat(max_width_left - left_name.len());
                        println!("{i}: Equivalence {left_name}{spaces} == {right_name}");
                    }
                    GameHop::Reduction(red) => {
                        println!(
                            "{i}: Reduction   {} ~= {} using {}",
                            red.left().construction_game_instance_name().as_str(),
                            red.right().construction_game_instance_name().as_str(),
                            red.assumption_name()
                        );
                    }
                    GameHop::Conjecture(conj) => {
                        println!(
                            "{i}: Conjecture   {} ~= {}",
                            conj.left_name().as_str(),
                            conj.right_name().as_str()
                        );
                    }
                    GameHop::Hybrid(hybrid) => {
                        let hybrid_name = hybrid.hybrid_name().as_str();
                        println!("hybrid: {hybrid_name}");
                    }
                }
            }
        }
        Ok(())
    }

    /// The names of the packages that declare an invariant, sorted.
    fn packages_with_invariants(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self
            .packages()
            .filter(|name| {
                self.get_package(name)
                    .is_some_and(|pkg| !pkg.invariants.is_empty())
            })
            .collect();
        names.sort();
        names
    }

    /// The packages whose invariant needs to be proved for the requested part of the project.
    ///
    /// Package invariants are used as assumptions in equivalence proofs, so we only need those of
    /// the packages that are instantiated in a game of an equivalence (or hybrid) game hop that we
    /// are actually going to verify. When the whole project is proved, all package invariants are
    /// checked.
    fn required_package_invariants(
        &self,
        req_theorem: &Option<String>,
        req_proofstep: Option<usize>,
    ) -> Vec<&str> {
        let all = self.packages_with_invariants();

        let Some(req_theorem) = req_theorem else {
            return all;
        };

        let Some(theorem) = self.get_theorem(req_theorem) else {
            return vec![];
        };

        let mut needed: Vec<&str> = all
            .into_iter()
            .filter(|pkg_name| {
                theorem
                    .game_hops
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| req_proofstep.is_none_or(|req| *i == req))
                    .filter_map(|(_, game_hop)| match game_hop {
                        GameHop::Equivalence(eq) => Some(eq),
                        GameHop::Hybrid(hybrid) => Some(hybrid.equivalence()),
                        GameHop::Reduction(_) | GameHop::Conjecture(_) => None,
                    })
                    .flat_map(|eq| [eq.left_name(), eq.right_name()])
                    .filter_map(|game_inst_name| theorem.find_game_instance(game_inst_name))
                    .any(|game_inst| {
                        game_inst
                            .game()
                            .pkgs
                            .iter()
                            .any(|pkg_inst| pkg_inst.pkg.name == *pkg_name)
                    })
            })
            .collect();

        needed.sort();
        needed
    }

    /// Proves the invariants of the given packages, as one section of the UI.
    fn prove_package_invariants<UI: TheoremUI + Send>(
        &self,
        ui: &mut UI,
        backend: &(impl SmtSolverBackend + Sync),
        transcript: bool,
        parallel: usize,
        pkg_names: &[&str],
        req_oracle: &Option<String>,
        invariant_start: bool,
    ) -> Result<()>
    where
        Self: Sized + Sync,
    {
        if pkg_names.is_empty() {
            return Ok(());
        }

        ui.start_theorem(UI_SECTION_NAME, pkg_names.len().try_into().unwrap());

        for pkg_name in pkg_names {
            let pkg = self.get_package(pkg_name).unwrap();

            ui.start_proofstep(UI_SECTION_NAME, pkg_name);

            let ctx = PackageInvariantContext::new(pkg, self)?;
            let driver = PackageInvariantSmtDriver::new(
                &ctx,
                self,
                backend,
                transcript,
                req_oracle.as_deref(),
                parallel,
                invariant_start,
            );
            driver.verify(ui)?;

            ui.finish_proofstep(UI_SECTION_NAME, pkg_name);
        }

        ui.finish_theorem(UI_SECTION_NAME);

        Ok(())
    }

    /// Proves the invariant of a single package, without proving anything else.
    ///
    /// This is what `domino prove --package <name>` does.
    fn prove_package(
        &self,
        backend: &(impl SmtSolverBackend + Sync),
        transcript: bool,
        parallel: usize,
        pkg_name: &str,
        req_oracle: &Option<String>,
        invariant_start: bool,
    ) -> Result<()>
    where
        Self: Sized + Sync,
    {
        if self.get_package(pkg_name).is_none() {
            let mut known_pkg_names: Vec<String> = self.packages().map(str::to_string).collect();
            known_pkg_names.sort();

            return Err(package_invariant::error::Error::UnknownPackage {
                pkg_name: pkg_name.to_string(),
                known_pkg_names,
            }
            .into());
        }

        let mut ui = IndicatifTheoremUI::new(1);

        self.prove_package_invariants(
            &mut ui,
            backend,
            transcript,
            parallel,
            &[pkg_name],
            req_oracle,
            invariant_start,
        )
    }

    // we might want to return a theorem trace here instead
    // we could then extract the theorem viewer output and other useful info trom the trace
    fn prove(
        &self,
        backend: &(impl SmtSolverBackend + Sync),
        transcript: bool,
        parallel: usize,
        req_theorem: &Option<String>,
        req_proofstep: Option<usize>,
        req_oracle: &Option<String>,
        req_claim: &Option<String>,
        invariant_start: bool,
    ) -> Result<()>
    where
        Self: Sized + Sync,
    {
        let mut theorem_keys: Vec<_> = self.theorems().collect();
        theorem_keys.sort();

        // Package invariants are theorem-independent, so we prove them once, up front, for the
        // packages the requested part of the project actually relies on. When the user asks for a
        // specific oracle, we only look at the packages that have an oracle of that name.
        let package_invariants: Vec<&str> = self
            .required_package_invariants(req_theorem, req_proofstep)
            .into_iter()
            .filter(|pkg_name| match req_oracle {
                Some(req_oracle) if !invariant_start => self
                    .get_package(pkg_name)
                    .unwrap()
                    .oracles
                    .iter()
                    .any(|odef| &odef.sig.name == req_oracle),
                _ => true,
            })
            .collect();

        let num_sections = theorem_keys.len() + usize::from(!package_invariants.is_empty());
        let mut ui = IndicatifTheoremUI::new(num_sections.try_into().unwrap());

        self.prove_package_invariants(
            &mut ui,
            backend,
            transcript,
            parallel,
            &package_invariants,
            req_oracle,
            invariant_start,
        )?;

        for theorem_key in theorem_keys.into_iter() {
            let theorem = self.get_theorem(theorem_key).unwrap();
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
                        let (theorem, auxs) =
                            EquivalenceTransform.transform_theorem(theorem).unwrap();

                        let mut eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
                        eqctx.load_invariants(self)?;

                        let mut driver = EquivalenceSmtDriver::new(
                            &eqctx,
                            self,
                            backend,
                            transcript,
                            req_oracle.as_deref(),
                            req_claim.as_deref(),
                            parallel,
                            invariant_start,
                        );
                        driver.verify(&mut ui)?;
                    }
                    GameHop::Hybrid(hyb) => {
                        let (theorem, auxs) =
                            EquivalenceTransform.transform_theorem(theorem).unwrap();

                        let mut eqctx = EquivalenceContext::new(hyb.equivalence(), &theorem, &auxs);
                        eqctx.load_invariants(self)?;

                        let mut driver = EquivalenceSmtDriver::new(
                            &eqctx,
                            self,
                            backend,
                            transcript,
                            req_oracle.as_deref(),
                            req_claim.as_deref(),
                            parallel,
                            invariant_start,
                        );
                        driver.verify(&mut ui)?;
                    }
                }
                ui.finish_proofstep(&theorem.name, &format!("{game_hop}"));
            }

            ui.finish_theorem(&theorem.name);
        }

        Ok(())
    }

    fn latex(&self, backend: &Option<impl SmtSolverBackend>) -> Result<()> {
        let mut path = self.get_root_dir();
        path.push("_build/latex/");
        std::fs::create_dir_all(&path)?;

        for name in self.games() {
            let game = self.get_game(name).unwrap();
            let (transformed, _) = crate::transforms::samplify::Transformation(game)
                .transform()
                .unwrap();
            let (transformed, _) = crate::transforms::resolveoracles::Transformation(&transformed)
                .transform()
                .unwrap();
            for lossy in [true, false] {
                crate::writers::tex::writer::tex_write_composition(
                    backend,
                    lossy,
                    &transformed,
                    name,
                    path.as_path(),
                )?;
            }
        }

        for name in self.theorems() {
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

    /// The transcript file for one claim group of a package invariant proof.
    fn get_package_invariant_smt_file(
        &self,
        pkg_name: &str,
        claim_group_name: &str,
    ) -> Result<std::fs::File> {
        let mut path = self.get_root_dir();

        path.push("_build/code_pkg/");
        path.push(pkg_name);
        std::fs::create_dir_all(&path)?;

        path.push(format!("{claim_group_name}.smt2"));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }

    fn get_smt_file(
        &self,
        theorem_name: &str,
        left_game_name: &str,
        right_game_name: &str,
        claim_group_name: &str,
        claim_name: &str,
    ) -> Result<std::fs::File> {
        let mut path = self.get_root_dir();

        path.push("_build/code_eq/");
        path.push(theorem_name);
        path.push(format!("{left_game_name}-{right_game_name}"));
        path.push(claim_group_name);
        std::fs::create_dir_all(&path)?;

        path.push(format!("{claim_name}.smt2"));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }
}
