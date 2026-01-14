use walkdir;

use std::{
    collections::HashMap,
    io::{Read, Seek, Write},
    path::{Path, PathBuf},
};
use zip::ZipArchive;

use crate::{
    gamehops::{equivalence, GameHop},
    package::{Composition, Package},
    parser::{ast::Identifier, package::handle_pkg, SspParser},
    project::{
        error::{Error, Result},
        load, Project, GAMES_DIR, PACKAGES_DIR, PROJECT_FILE, THEOREM_DIR,
    },
    theorem::Theorem,
    transforms::Transformation,
    ui::{BaseUI, TheoremUI},
    util::prover::ProverBackend,
};

#[derive(Debug)]
pub struct DirectoryProject<'a> {
    files: DirectoryFiles,
    root_dir: PathBuf,
    games: HashMap<String, Composition>,
    theorems: HashMap<String, Theorem<'a>>,
}

impl<'a> DirectoryProject<'a> {
    pub fn new(root: &Path) -> Result<Self> {
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

        let root_dir = find_project_root()?;

        let theorems = load_files(root.join(THEOREM_DIR))?;
        let games = load_files(root.join(GAMES_DIR))?;
        let packages = load_files(root.join(PACKAGES_DIR))?;

        let files = DirectoryFiles {
            theorems,
            games,
            packages,
        };
        Ok(DirectoryProject {
            files,
            root_dir,
            games: HashMap::new(),
            theorems: HashMap::new(),
        })
    }

    pub fn init(&'a mut self) -> Result<()> {
        let packages = load::packages(&self.files.packages)?;
        self.games = load::games(&self.files.games, &packages)?;
        self.theorems = load::theorems(
            &self.files.theorems,
            packages.to_owned(),
            self.games.to_owned(),
        )?;

        Ok(())
    }
}

impl<'a> Project for DirectoryProject<'a> {
    fn theorems(&self) -> impl Iterator<Item = &String> {
        self.theorems.keys()
    }

    fn get_theorem(&self, name: &str) -> Option<&Theorem> {
        self.theorems.get(name)
    }

    fn games(&self) -> impl Iterator<Item = &String> {
        self.games.keys()
    }

    fn get_game(&self, name: &str) -> Option<&Composition> {
        self.games.get(name)
    }

    fn get_output_file(
        &self,
        extension: String,
    ) -> std::io::Result<impl Write + Send + Sync + 'static> {
        let mut path = self.root_dir.clone();
        path.push("_build/");
        path.push(extension);

        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(&parent)?;
        }
        Ok(std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?)
    }
    fn read_input_file(&self, extension: &str) -> std::io::Result<String> {
        let mut path = self.root_dir.clone();
        path.push(extension);
        let file = std::fs::OpenOptions::new()
            .read(true)
            .open(path)?;
        std::io::read_to_string(file)
    }
}

#[derive(Debug)]
pub struct ZipProject<'a, R> {
    files: &'a ZipFiles<R>,
    games: HashMap<String, Composition>,
    theorems: HashMap<String, Theorem<'a>>,
}

impl<'a, R: Read + Seek + Clone> ZipProject<'a, R> {
    pub fn load(reader: R) -> Result<ZipFiles<R>> {
        let mut archive = zip::ZipArchive::new(reader.clone())?;
        let mut theorems = Vec::new();
        let mut games = Vec::new();
        let mut packages = Vec::new();

        for i in 0..archive.len() {
            let file = archive.by_index(i)?;
            if !file.is_file() {
                continue;
            }

            let filename = file.name().to_string();
            if !filename.ends_with(".ssp") {
                continue;
            }

            let content = std::io::read_to_string(file)?;

            match filename {
                _ if filename.starts_with(THEOREM_DIR) => theorems.push((filename, content)),
                _ if filename.starts_with(GAMES_DIR) => games.push((filename, content)),
                _ if filename.starts_with(PACKAGES_DIR) => packages.push((filename, content)),
                _ => {}
            }
        }

        Ok(ZipFiles {
            archive: reader,            
            theorems,
            games,
            packages,
        })
    }
    
    pub fn new(files: &'a ZipFiles<R>) -> Result<Self> {

        let packages = load::packages(&files.packages)?;
        let games = load::games(&files.games, &packages)?;
        let theorems = load::theorems(&files.theorems, packages.to_owned(), games.to_owned())?;

        Ok(
            Self {
                files,
                games,
                theorems,
            }
        )
    }

    pub fn init(&'a mut self) -> Result<()> {
        Ok(())
    }
}

impl<'a, R: Sync + Read + Seek + Clone> Project for ZipProject<'a, R> {
    fn theorems(&self) -> impl Iterator<Item = &String> {
        self.theorems.keys()
    }

    fn get_theorem(&self, name: &str) -> Option<&Theorem> {
        self.theorems.get(name)
    }

    fn games(&self) -> impl Iterator<Item = &String> {
        self.games.keys()
    }

    fn get_game(&self, name: &str) -> Option<&Composition> {
        self.games.get(name)
    }

    fn get_output_file(
        &self,
        extension: String,
    ) -> std::io::Result<impl std::io::Write + Send + Sync + 'static> {
        unimplemented!("Can not write to zip file based projects");
        Ok(std::io::Cursor::new(Vec::<u8>::new()))
    }

    fn read_input_file(&self, extension: &str) -> std::io::Result<String> {
        let extension = if extension.starts_with("./") {
            &extension[2..]
        } else {
            extension
        };
        let mut archive = zip::ZipArchive::new(self.files.archive.clone())?;
        let file = archive.by_name(extension)?;
        std::io::read_to_string(file)
    }
}

#[derive(Debug)]
pub struct DirectoryFiles {
    theorems: Vec<(String, String)>,
    games: Vec<(String, String)>,
    packages: Vec<(String, String)>,
}

#[derive(Debug)]
pub struct ZipFiles<R> {
    archive: R,
    theorems: Vec<(String, String)>,
    games: Vec<(String, String)>,
    packages: Vec<(String, String)>,
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
