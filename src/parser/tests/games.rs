// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{collections::HashMap, iter::FromIterator as _};

use crate::{
    package::{Composition, Package},
    parser::{
        composition::{handle_composition, ParseGameError},
        tests::TESTDATA_SSPCODE_PATH,
        SspParser,
    },
};

pub fn parse(code: &str, name: &str, pkg_map: &HashMap<String, Package>) -> Composition {
    let mut game_pairs = SspParser::parse_composition(code).unwrap();
    handle_composition(name, code, game_pairs.next().unwrap(), pkg_map).unwrap_or_else(|err| {
        let err_str = format!("{err:?}");
        panic!(
            "handle error for game in {name}:\n\t{err}\n\n{diag:?}",
            err = err_str,
            diag = miette::Report::new(err)
        )
    })
}

pub fn parse_fails(code: &str, name: &str, pkg_map: &HashMap<String, Package>) -> ParseGameError {
    // any test game should adhere to the grammar
    let mut game_pairs = SspParser::parse_composition(code).unwrap();

    handle_composition(name, code, game_pairs.next().unwrap(), pkg_map).expect_err(&format!(
        "expected an error when parsing {name}, but it succeeded"
    ))
}

pub fn parse_file(file_name: &str, pkgs: &HashMap<String, Package>) -> Composition {
    let file = std::fs::File::open(format!("{TESTDATA_SSPCODE_PATH}/games/{file_name}"))
        .unwrap_or_else(|_| panic!("error opening test code game {file_name}"));

    let contents = std::io::read_to_string(file)
        .unwrap_or_else(|_| panic!("error reading test code game {file_name}"));

    parse(&contents, file_name, pkgs)
}

pub fn parse_files(
    file_names: &[&str],
    pkgs: &HashMap<String, Package>,
) -> HashMap<String, Composition> {
    HashMap::from_iter(file_names.iter().cloned().map(|name| {
        let game = parse_file(name, pkgs);
        (game.name.clone(), game)
    }))
}

pub fn parse_file_fails(
    file_name: &'static str,
    pkg_map: &HashMap<String, Package>,
) -> ParseGameError {
    let file = std::fs::File::open(format!("{TESTDATA_SSPCODE_PATH}/games/{file_name}"))
        .unwrap_or_else(|_| panic!("error opening test code game {file_name}"));

    let contents = std::io::read_to_string(file)
        .unwrap_or_else(|_| panic!("error reading test code game {file_name}"));

    parse_fails(&contents, file_name, pkg_map)
}
