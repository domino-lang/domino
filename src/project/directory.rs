use std::path::Path;
use std::{collections::HashMap, path::PathBuf};
use walkdir;

use crate::{package::Composition, theorem::Theorem};

use super::consts::{GAMES_DIR, PACKAGES_DIR, PROJECT_FILE, THEOREM_DIR};
use super::error::{FindProjectRootError, Result};
use super::Project;

pub struct DirectoryFiles {
    theorems: Vec<(String, String)>,
    games: Vec<(String, String)>,
    packages: Vec<(String, String)>,
}

impl DirectoryFiles {
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
            theorems: load_files(root.join(THEOREM_DIR))?,
            games: load_files(root.join(GAMES_DIR))?,
            packages: load_files(root.join(PACKAGES_DIR))?,
        })
    }
}

#[derive(Debug)]
pub struct DirectoryProject<'a> {
    root_dir: PathBuf,
    games: HashMap<String, Composition>,
    theorems: HashMap<String, Theorem<'a>>,
}

impl<'a> DirectoryProject<'a> {
    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        Self {
            root_dir: PathBuf::new(),
            games: HashMap::new(),
            theorems: HashMap::new(),
        }
    }

    pub fn load(files: &'a DirectoryFiles) -> Result<DirectoryProject<'a>> {
        let root_dir = find_project_root()?;

        let packages = super::load::packages(&files.packages)?;
        let games = super::load::games(&files.games, &packages)?;
        let theorems =
            super::load::theorems(&files.theorems, packages.to_owned(), games.to_owned())?;

        let project = DirectoryProject {
            root_dir,
            games,
            theorems,
        };

        Ok(project)
    }
}

impl Project for DirectoryProject<'_> {
    fn games(&self) -> impl Iterator<Item = &String> {
        self.games.keys()
    }
    fn theorems(&self) -> impl Iterator<Item = &String> {
        self.theorems.keys()
    }
    fn get_game(&self, name: &str) -> Option<&Composition> {
        self.games.get(name)
    }
    fn get_theorem(&self, name: &str) -> Option<&Theorem<'_>> {
        self.theorems.get(name)
    }

    fn get_root_dir(&self) -> PathBuf {
        self.root_dir.clone()
    }

    fn read_input_file(&self, extension: &str) -> std::io::Result<String> {
        let mut path = self.root_dir.clone();
        path.push(extension);
        let file = std::fs::OpenOptions::new().read(true).open(path)?;
        std::io::read_to_string(file)
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
