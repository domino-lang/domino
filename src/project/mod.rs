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

use crate::{
    gamehops::{equivalence::EquivalenceSmtDriver, GameHop},
    package::{Composition, Package},
    theorem::{claim_closure, Claim, Theorem},
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

    /// `req_oracle`/`req_claim` narrow the generated dependency graphs, same
    /// spirit as `prove`'s `--proof`/`--proofstep`/`--oracle`: with neither
    /// set, every oracle of a game hop is merged into one file; with
    /// `req_oracle` set, only that oracle's tree is emitted, on its own;
    /// with `req_claim` also set, only that claim's transitive dependency
    /// closure (not just its direct `lemmas { claim: [...] }` list) is
    /// emitted, down to admitted/built-in leaves.
    fn proofsteps(
        &self,
        req_theorem: &Option<String>,
        req_proofstep: Option<usize>,
        req_oracle: &Option<String>,
        req_claim: &Option<String>,
    ) -> Result<()> {
        let mut theorem_keys: Vec<_> = self.theorems().collect();
        theorem_keys.sort();

        for theorem_key in theorem_keys.into_iter() {
            if let Some(req_theorem) = req_theorem {
                if theorem_key != req_theorem {
                    continue;
                }
            }

            let theorem = self.get_theorem(theorem_key).unwrap();

            println!("{theorem_key}:");
            for (i, game_hop) in theorem.game_hops.iter().enumerate() {
                if let Some(req_proofstep) = req_proofstep {
                    if i != req_proofstep {
                        continue;
                    }
                }

                match game_hop {
                    GameHop::Equivalence(eq) => {
                        println!("  Equivalence {}", game_hop.name());
                        self.write_lemma_dependency_dot(
                            theorem_key,
                            eq.left_name(),
                            eq.right_name(),
                            eq.trees(),
                            req_oracle.as_deref(),
                            req_claim.as_deref(),
                        )?;
                    }
                    GameHop::Reduction(red) => {
                        println!(
                            "  Reduction   {} using {}",
                            game_hop.name(),
                            red.assumption_name()
                        );
                    }
                    GameHop::Conjecture(_) => {
                        println!("  Conjecture   {}", game_hop.name());
                    }
                    GameHop::Hybrid(hybrid) => {
                        println!("  Hybrid      {}", game_hop.name());
                        let eq = hybrid.equivalence();
                        self.write_lemma_dependency_dot(
                            theorem_key,
                            eq.left_name(),
                            eq.right_name(),
                            eq.trees(),
                            req_oracle.as_deref(),
                            req_claim.as_deref(),
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Writes a Graphviz DOT file for a `equivalence`/`hybrid` game hop,
    /// containing lemma dependency tree(s) (as declared in the theorem's
    /// `lemmas { ... }` blocks) of either every oracle (one cluster
    /// subgraph each), a single oracle, or a single claim's transitive
    /// dependency closure within a single oracle -- see [`Project::proofsteps`].
    /// Called automatically by [`Project::proofsteps`] as a side effect,
    /// mirroring how [`Project::latex`] writes into `_build/latex`.
    ///
    /// Named like the SMT transcript files from [`Project::get_joined_smt_file`]
    /// (`{left_game_name}-{right_game_name}-{oracle}-{claim}.smt2`), with the
    /// oracle/claim suffix dropped for whichever of the two are merged over.
    fn write_lemma_dependency_dot(
        &self,
        theorem_key: &str,
        left_name: &str,
        right_name: &str,
        trees: &[(String, Vec<Claim>)],
        req_oracle: Option<&str>,
        req_claim: Option<&str>,
    ) -> Result<()> {
        let mut dir = self.get_root_dir();
        dir.push("_build/dot");
        std::fs::create_dir_all(&dir)?;

        let Some(oracle_name) = req_oracle else {
            let path = dir.join(format!("{left_name}-{right_name}.dot"));
            let graph_name = format!("{left_name}_{right_name}").replace('-', "_");
            let label = format!("{theorem_key}: {left_name} == {right_name}");

            std::fs::write(
                &path,
                crate::writers::dot::lemma_dependency_dot(&graph_name, &label, trees),
            )?;
            println!("    lemma dependency graph: {}", path.display());
            return Ok(());
        };

        let Some((_, oracle_tree)) = trees.iter().find(|(name, _)| name == oracle_name) else {
            // This game hop doesn't export the requested oracle; nothing to do here.
            return Ok(());
        };

        let tree = match req_claim {
            None => oracle_tree.clone(),
            Some(claim_name) => match claim_closure(oracle_tree, claim_name) {
                Some(closure) => closure,
                None => {
                    eprintln!(
                        "warning: claim `{claim_name}` not found for oracle `{oracle_name}` in {theorem_key} ({left_name} == {right_name})"
                    );
                    return Ok(());
                }
            },
        };

        let mut filename = format!("{left_name}-{right_name}-{oracle_name}");
        let mut graph_name = format!("{left_name}_{right_name}_{oracle_name}");
        let mut label = format!("{theorem_key}: {left_name} == {right_name} (oracle {oracle_name}");
        if let Some(claim_name) = req_claim {
            filename.push('-');
            filename.push_str(claim_name);
            graph_name.push('_');
            graph_name.push_str(claim_name);
            label.push_str(", claim ");
            label.push_str(claim_name);
        }
        filename.push_str(".dot");
        label.push(')');
        let graph_name = graph_name.replace('-', "_");

        let path = dir.join(filename);
        let trees_for_dot = [(oracle_name.to_string(), tree)];

        std::fs::write(
            &path,
            crate::writers::dot::lemma_dependency_dot(&graph_name, &label, &trees_for_dot),
        )?;
        println!("    lemma dependency graph: {}", path.display());

        Ok(())
    }

    // we might want to return a theorem trace here instead
    // we could then extract the theorem viewer output and other useful info trom the trace
    fn prove(
        &self,
        backend: &(impl SmtSolverBackend + Sync),
        transcript: bool,
        parallel: usize,
        req_theorem: &Option<String>,
        req_proofstep: &Option<String>,
        req_oracle: &Option<String>,
        req_claim: &Option<String>,
    ) -> Result<()>
    where
        Self: Sized + Sync,
    {
        let mut theorem_keys: Vec<_> = self.theorems().collect();
        theorem_keys.sort();

        let mut ui = IndicatifTheoremUI::new(theorem_keys.len().try_into().unwrap());

        for theorem_key in theorem_keys.into_iter() {
            let theorem = self.get_theorem(theorem_key).unwrap();
            ui.start_theorem(&theorem.name, theorem.game_hops.len().try_into().unwrap());

            if let Some(ref req_theorem) = req_theorem {
                if theorem_key != req_theorem {
                    ui.finish_theorem(&theorem.name);
                    continue;
                }
            }

            for game_hop in theorem.game_hops.iter() {
                ui.start_proofstep(&theorem.name, &format!("{game_hop}"));

                if let Some(req_proofstep) = req_proofstep {
                    if game_hop.name() != *req_proofstep {
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

    fn get_joined_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
        scope_name: &str,
        claim_name: &str,
    ) -> Result<std::fs::File> {
        let mut path = self.get_root_dir();

        path.push("_build/code_eq/joined/");
        std::fs::create_dir_all(&path)?;

        path.push(format!(
            "{left_game_name}-{right_game_name}-{scope_name}-{claim_name}.smt2"
        ));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }
}
