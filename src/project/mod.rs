/**
 *  project is the high-level structure of sspverif.
 *
 *  here we assemble all the users' packages, assumptions, game hops and equivalence proofs.
 *  we also facilitate individual proof steps here, and provide an interface for doing the whole proof.
 *
 */
use std::path::Path;
use std::{collections::HashMap, path::PathBuf};
use walkdir;

use error::{Error, Result};

use crate::parser::ast::Identifier;
use crate::parser::package::handle_pkg;
use crate::parser::SspParser;
use crate::{
    gamehops::{equivalence, GameHop},
    package::{Composition, Package},
    proof::Proof,
    theorem::Theorem,
    transforms::Transformation,
    util::prover_process::ProverBackend,
};

use crate::ui::{indicatif::IndicatifProofUI, ProofUI};

pub const PROJECT_FILE: &str = "ssp.toml";

pub const PACKAGES_DIR: &str = "packages";
pub const GAMES_DIR: &str = "games";
pub const PROOFS_DIR: &str = "proofs";
pub const ASSUMPTIONS_DIR: &str = "assumptions";

pub const PACKAGE_EXT: &str = ".pkg.ssp";
pub const GAME_EXT: &str = ".comp.ssp"; // TODO maybe change this to .game.ssp later, and also rename the Composition type

mod load;
mod resolve;

pub mod error;

pub struct Files {
    proofs: Vec<(String, String)>,
    games: Vec<(String, String)>,
    packages: Vec<(String, String)>,
}

impl Files {
    pub fn load(root: &Path) -> Result<Self> {
        fn load_files(path: impl AsRef<Path>) -> Result<Vec<(String, String)>> {
            walkdir::WalkDir::new(path.as_ref())
                .into_iter()
                .filter_map(|e| e.ok())
                .map(|dir_entry| {
                    let file_name = dir_entry.file_name();
                    let Some(file_name) = file_name.to_str() else {
                        return Ok(None);
                    };

                    if file_name.ends_with(".ssp") {
                        let file_content = std::fs::read_to_string(dir_entry.path())?;
                        Ok(Some((file_name.to_string(), file_content)))
                    } else {
                        Ok(None)
                    }
                })
                .filter_map(Result::transpose)
                .collect()
        }

        Ok(Self {
            proofs: load_files(root.join(PROOFS_DIR))?,
            games: load_files(root.join(GAMES_DIR))?,
            packages: load_files(root.join(PACKAGES_DIR))?,
        })
    }

    pub(crate) fn packages(&self) -> impl Iterator<Item = Result<Package>> + '_ {
        let mut filenames: HashMap<String, &String> = HashMap::new();

        self.packages.iter().map(move |(file_name, file_content)| {
            let mut ast =
                SspParser::parse_package(file_content).map_err(|e| (file_name.as_str(), e))?;

            let (pkg_name, pkg) = handle_pkg(file_name, file_content, ast.next().unwrap())
                .map_err(Error::ParsePackage)?;

            if let Some(other_filename) = filenames.insert(pkg_name.clone(), file_name) {
                return Err(Error::RedefinedPackage(
                    pkg_name,
                    file_name.to_string(),
                    other_filename.to_string(),
                ));
            }

            Ok(pkg)
        })
    }
}

#[derive(Debug)]
pub struct Project<'a> {
    root_dir: PathBuf,
    games: HashMap<String, Composition>,
    proofs: HashMap<String, Proof<'a>>,
}

impl<'a> Project<'a> {
    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        Self {
            root_dir: PathBuf::new(),
            games: HashMap::new(),
            proofs: HashMap::new(),
        }
    }

    pub fn load(files: &'a Files) -> Result<Project<'a>> {
        let root_dir = find_project_root()?;

        let packages: HashMap<_, _> = files
            .packages()
            .map(|pkg| pkg.map(|pkg| (pkg.name.clone(), pkg)))
            .collect::<Result<_>>()?;

        /* we already typecheck during parsing, and the typecheck transform uses a bunch of deprecated
           stuff, so we just comment it out.

        let mut pkg_names: Vec<_> = packages.keys().collect();
        pkg_names.sort();

        for pkg_name in pkg_names.into_iter() {
            let pkg = &packages[pkg_name];
            let mut scope = TypeCheckScope::new();
            typecheck_pkg(pkg, &mut scope)?;
        }
         */

        let games = load::games(&files.games, &packages)?;
        // let mut game_names: Vec<_> = games.keys().collect();
        // game_names.sort();
        //
        // for game_name in game_names.into_iter() {
        //     let game = &games[game_name];
        //     let mut scope = Scope::new();
        //     typecheck_comp(game, &mut scope)?;
        // }

        let proofs = load::proofs(&files.proofs, packages.to_owned(), games.to_owned())?;

        let project = Project {
            root_dir,
            games,
            proofs,
        };

        Ok(project)
    }

    pub fn proofsteps(&self) -> Result<()> {
        let mut proof_keys: Vec<_> = self.proofs.keys().collect();
        proof_keys.sort();

        for proof_key in proof_keys.into_iter() {
            let proof = &self.proofs[proof_key];
            let max_width_left = proof
                .game_hops
                .iter()
                .map(GameHop::left_game_instance_name)
                .map(str::len)
                .max()
                .unwrap_or(0);

            println!("{proof_key}:");
            for (i, game_hop) in proof.game_hops.iter().enumerate() {
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
                }
            }
        }
        Ok(())
    }

    // we might want to return a proof trace here instead
    // we could then extract the proof viewer output and other useful info trom the trace
    pub fn prove(
        &self,
        backend: ProverBackend,
        transcript: bool,
        parallel: usize,
        req_proof: &Option<String>,
        req_proofstep: Option<usize>,
        req_oracle: &Option<String>,
    ) -> Result<()> {
        let mut proof_keys: Vec<_> = self.proofs.keys().collect();
        proof_keys.sort();

        let mut ui = IndicatifProofUI::new(proof_keys.len().try_into().unwrap());

        for proof_key in proof_keys.into_iter() {
            let proof = &self.proofs[proof_key];
            ui.start_proof(&proof.name, proof.game_hops.len().try_into().unwrap());

            let theorem = Theorem::try_new(proof);
            if theorem.is_none() {
                log::warn!("Could not conclude Real ~ Ideal from game-hops");
            } else {
                log::info!("{}", theorem.unwrap());
            }

            if let Some(ref req_proof) = req_proof {
                if proof_key != req_proof {
                    ui.finish_proof(&proof.name);
                    continue;
                }
            }

            for (i, game_hop) in proof.game_hops.iter().enumerate() {
                ui.start_proofstep(&proof.name, &format!("{game_hop}"));

                if let Some(ref req_proofstep) = req_proofstep {
                    if i != *req_proofstep {
                        ui.finish_proofstep(&proof.name, &format!("{game_hop}"));
                        continue;
                    }
                }

                match game_hop {
                    GameHop::Reduction(_) => {
                        ui.proofstep_is_reduction(&proof.name, &format!("{game_hop}"));
                    }
                    GameHop::Conjecture(_) => {
                        ui.proofstep_is_reduction(&proof.name, &format!("{game_hop}"));
                    }
                    GameHop::Equivalence(eq) => {
                        if parallel > 1 {
                            equivalence::verify_parallel(
                                self, &mut ui, eq, proof, backend, transcript, parallel, req_oracle,
                            )?;
                        } else {
                            equivalence::verify(
                                self, &mut ui, eq, proof, backend, transcript, req_oracle,
                            )?;
                        }
                    }
                }
                ui.finish_proofstep(&proof.name, &format!("{game_hop}"));
            }

            ui.finish_proof(&proof.name);
        }

        Ok(())
    }

    pub fn latex(&self, backend: Option<ProverBackend>) -> Result<()> {
        let mut path = self.root_dir.clone();
        path.push("_build/latex/");
        std::fs::create_dir_all(&path)?;

        for (name, game) in &self.games {
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
                    path.as_path(),
                )?;
            }
        }

        for (name, proof) in &self.proofs {
            for lossy in [true, false] {
                crate::writers::tex::writer::tex_write_proof(
                    &backend,
                    lossy,
                    proof,
                    name,
                    path.as_path(),
                )?;
            }
        }

        Ok(())
    }

    /*

    pub fn explain_game(&self, game_name: &str) -> Result<String> {
        let game = self.get_game(game_name).ok_or(Error::UndefinedGame(
            game_name.to_string(),
            format!("in explain"),
        ))?;

        let mut buf = String::new();
        let mut w = crate::writers::pseudocode::fmtwriter::FmtWriter::new(&mut buf, true);
        let (game, _, _) = crate::transforms::transform_explain(&game)?;

        println!("Explaining game {game_name}:");
        for inst in game.pkgs {
            let pkg = inst.pkg;
            w.write_package(&pkg).unwrap();
        }

        Ok(buf)
        //tex_write_composition(&comp, Path::new(&args.output));
    }

    */
    pub fn get_game<'b>(&'b self, name: &str) -> Option<&'b Composition> {
        self.games.get(name)
    }

    /*
    pub fn get_assumption<'a>(&'a self, name: &str) -> Option<&'a Assumption> {
        self.assumptions.get(name)
    }
    */

    pub fn get_root_dir(&self) -> PathBuf {
        self.root_dir.clone()
    }

    pub fn get_game_smt_file(&self, game_name: &str) -> Result<std::fs::File> {
        let mut path = self.root_dir.clone();

        path.push("_build/code_eq/games/");
        std::fs::create_dir_all(&path)?;

        path.push(format!("{game_name}.smt2"));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }

    pub fn get_base_decl_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
    ) -> Result<std::fs::File> {
        let mut path = self.root_dir.clone();

        path.push("_build/code_eq/base_decls/");
        std::fs::create_dir_all(&path)?;

        path.push(format!("{left_game_name}_{right_game_name}.smt2"));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }

    pub fn get_const_decl_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
    ) -> Result<std::fs::File> {
        let mut path = self.root_dir.clone();

        path.push("_build/code_eq/const_decls/");
        std::fs::create_dir_all(&path)?;

        path.push(format!("{left_game_name}_{right_game_name}.smt2"));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }

    pub fn get_epilogue_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
    ) -> Result<std::fs::File> {
        let mut path = self.root_dir.clone();

        path.push("_build/code_eq/epilogue/");
        std::fs::create_dir_all(&path)?;

        path.push(format!("{left_game_name}_{right_game_name}.smt2"));
        let f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;

        Ok(f)
    }

    pub fn get_joined_smt_file(
        &self,
        left_game_name: &str,
        right_game_name: &str,
        oracle_name: Option<&str>,
    ) -> Result<std::fs::File> {
        let mut path = self.root_dir.clone();

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

    pub fn print_wire_check_smt(&self, game_name: &str, _dst_idx: usize) {
        let _game = self.get_game(game_name).unwrap();
        // for command in wire_proofs::build_smt(&game, dst_idx) {
        //     println!("{}", command);
        // }
    }
}

pub fn find_project_root() -> std::result::Result<std::path::PathBuf, FindProjectRootError> {
    let mut dir = std::env::current_dir().map_err(FindProjectRootError::CurrentDir)?;

    loop {
        let lst = dir.read_dir().map_err(FindProjectRootError::ReadDir)?;
        for entry in lst {
            let entry = entry.map_err(FindProjectRootError::ReadDir)?;
            let file_name = match entry.file_name().into_string() {
                Err(_) => continue,
                Ok(name) => name,
            };
            if file_name == PROJECT_FILE {
                return Ok(dir);
            }
        }

        match dir.parent() {
            None => return Err(FindProjectRootError::NotInProject),
            Some(parent) => dir = parent.into(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum FindProjectRootError {
    #[error("Error determining current directory:")]
    CurrentDir(std::io::Error),
    #[error("Error reading directory:")]
    ReadDir(std::io::Error),
    #[error("Not in project: no ssp.toml file in this or any parent directory")]
    NotInProject,
}
