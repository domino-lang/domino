
use std::{
    path::{Path, PathBuf},
    io::{Read,Write,Seek},
    collections::HashMap,
};

use crate::{
    ui::{BaseUI, TheoremUI},
    util::prover::ProverBackend,
    transforms::Transformation,
    package::{Composition, Package},
    parser::{
        SspParser,
        package::handle_pkg,
        ast::Identifier,
    },
    gamehops::{equivalence, GameHop},
    project::{
        error::{Error, Result},
        Project,
        load,
        GAMES_DIR,
        PACKAGES_DIR,
        THEOREM_DIR,
    },
    theorem::Theorem,
};



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

    pub fn load(files: &'a Files) -> Result<DirectoryProject<'a>> {
        //let root_dir = find_project_root()?;

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

        let theorems = load::theorems(&files.theorems, packages.to_owned(), games.to_owned())?;

        let project = DirectoryProject {
            root_dir: PathBuf::new(),
            games,
            theorems,
        };

        Ok(project)
    }

    fn get_root_dir(&self) -> PathBuf {
        self.root_dir.clone()
    }

    
}

impl<'a> Project for DirectoryProject<'a> {

    fn theorems(&self) -> impl Iterator<Item = &String> {
        self.theorems.keys()
    }
    
    fn get_theorem<'b>(&'b self, name: &str) -> Option<&Theorem> {
        self.theorems.get(name)
    }

    fn games(&self) -> impl Iterator<Item = &String> {
        self.games.keys()
    }

    fn get_game(&self, name: &str) -> Option<&Composition> {
        self.games.get(name)
    }

    fn get_output_file(&self, extension: String)  -> std::io::Result<impl Write + Send + Sync + 'static> {
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
    

}

#[derive(Debug)]
pub struct Files {
    theorems: Vec<(String, String)>,
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
            theorems: load_files(root.join(THEOREM_DIR))?,
            games: load_files(root.join(GAMES_DIR))?,
            packages: load_files(root.join(PACKAGES_DIR))?,
        })
    }

    pub fn load_zip(reader: impl Read + Seek) -> Result<Self> {
        let mut zip = zip::ZipArchive::new(reader)?;
        let mut theorems = Vec::new();
        let mut games = Vec::new();
        let mut packages = Vec::new();

        for i in 0..zip.len() {
            let file = zip.by_index(i)?;
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

        Ok(Self {
            theorems,
            games,
            packages,
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
