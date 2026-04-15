use std::io::{Cursor, Read, Seek};
use std::{collections::HashMap, path::PathBuf};
use zip::ZipArchive;

use crate::{package::Composition, theorem::Theorem};

use super::consts::{GAMES_DIR, PACKAGES_DIR, THEOREM_DIR};
use super::error::Result;
use super::Project;

#[derive(Debug)]
pub struct ZipProject<'a> {
    archive: &'a Vec<u8>,
    games: HashMap<String, Composition>,
    theorems: HashMap<String, Theorem<'a>>,
}

#[derive(Debug)]
pub struct ZipFiles {
    archive: Vec<u8>,
    theorems: Vec<(String, String)>,
    games: Vec<(String, String)>,
    packages: Vec<(String, String)>,
}

impl ZipFiles {
    pub fn load<R: Read>(mut reader: R) -> Result<Self> {
        let mut archive_bytes = Vec::new();
        reader.read_to_end(&mut archive_bytes)?;
        let mut archive = zip::ZipArchive::new(Cursor::new(archive_bytes.clone()))?;
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
            archive: archive_bytes,
            theorems,
            games,
            packages,
        })
    }
}

impl<'a> ZipProject<'a> {
    pub fn load(files: &'a ZipFiles) -> Result<Self> {
        let packages = super::load::packages(&files.packages)?;
        let games = super::load::games(&files.games, &packages)?;
        let theorems =
            super::load::theorems(&files.theorems, packages.to_owned(), games.to_owned())?;

        Ok(Self {
            archive: &files.archive,
            games,
            theorems,
        })
    }
}

impl Project for ZipProject<'_> {
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
        unreachable!()
    }

    fn read_input_file(&self, extension: &str) -> std::io::Result<String> {
        let extension = if extension.starts_with("./") {
            &extension[2..]
        } else {
            extension
        };

        let mut archive = zip::ZipArchive::new(Cursor::new(self.archive.clone()))?;
        let file = archive.by_name(extension)?;
        std::io::read_to_string(file)
    }
}
