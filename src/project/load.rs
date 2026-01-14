// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashMap;

use super::*;
use error::Result;

use crate::package::{Composition, Package};
use crate::parser::{composition::handle_composition, theorem::handle_theorem, SspParser};
use crate::theorem::Theorem;

pub(crate) fn games(
    files: &[(String, String)],
    pkgs: &HashMap<String, Package>,
) -> Result<HashMap<String, Composition>> {
    let mut games = HashMap::new();

    for (file_name, file_content) in files {
        let mut ast =
            SspParser::parse_composition(file_content).map_err(|err| (file_name.as_str(), err))?;

        let comp = handle_composition(file_name, file_content, ast.next().unwrap(), pkgs)?;
        let comp_name = comp.name.clone();

        games.insert(comp_name, comp);
    }

    Ok(games)
}

pub(crate) fn theorems(
    files: &[(String, String)],
    pkgs: HashMap<String, Package>,
    games: HashMap<String, Composition>,
) -> Result<HashMap<String, Theorem<'_>>> {
    let mut theorems = HashMap::new();

    for (file_name, file_content) in files {
        let parse_result =
            SspParser::parse_theorem(file_content).map_err(|err| (file_name.as_str(), err))?;

        let mut ast = parse_result;
        let theorem = handle_theorem(
            file_name,
            file_content,
            ast.next().unwrap(),
            pkgs.clone(),
            games.clone(),
        )?;
        let theorem_name = theorem.name.to_string();

        theorems.insert(theorem_name, theorem);
    }

    Ok(theorems)
}

pub(crate) fn packages(files: &[(String, String)]) -> Result<HashMap<String, Package>> {
    let mut packages = HashMap::new();
    let mut filenames: HashMap<String, &String> = HashMap::new();

    for (file_name, file_content) in files {
        let mut ast =
            SspParser::parse_package(file_content).map_err(|e| (file_name.as_str(), e))?;

        let (pkg_name, pkg) = handle_pkg(file_name, file_content, ast.next().unwrap())?;
        //.map_err(Error::ParsePackage)?;

        if let Some(other_filename) = filenames.insert(pkg_name.clone(), file_name) {
            return Err(Error::RedefinedPackage(
                pkg_name,
                file_name.to_string(),
                other_filename.to_string(),
            ));
        }
        packages.insert(pkg_name, pkg);
    }
    Ok(packages)
}
