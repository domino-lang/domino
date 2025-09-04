use std::collections::HashMap;

use crate::{
    package::{Composition, Package},
    parser::{
        theorem::{handle_theorem, ParseTheoremError},
        tests::TESTDATA_SSPCODE_PATH,
        SspParser,
    },
    theorem::Theorem,
};
pub fn parse<'a>(
    code: &'a str,
    name: &'a str,
    pkgs: &'a HashMap<String, Package>,
    games: &'a HashMap<String, Composition>,
) -> Theorem<'a> {
    let mut theorem_pairs = SspParser::parse_theorem(code).unwrap();
    handle_theorem(
        name,
        code,
        theorem_pairs.next().unwrap(),
        pkgs.clone(),
        games.clone(),
    )
    .unwrap_or_else(|err| panic!("handle error: {err}"))
}

pub fn parse_fails(
    code: &str,
    name: &str,
    pkgs: &HashMap<String, Package>,
    games: &HashMap<String, Composition>,
) -> ParseTheoremError {
    // any test game should adhere to the grammar
    let mut theorem_pairs = SspParser::parse_theorem(code).unwrap();

    let Err(err) = handle_theorem(
        name,
        code,
        theorem_pairs.next().unwrap(),
        pkgs.clone(),
        games.clone(),
    ) else {
        panic!("expected an error when parsing {name}, but it succeeded")
    };

    err
}

pub fn read_file(file_name: &'static str) -> String {
    std::fs::read_to_string(format!("{TESTDATA_SSPCODE_PATH}/proofs/{file_name}"))
        .unwrap_or_else(|_| panic!("error reading test code proof {file_name}"))
}

pub fn parse_file_fails(
    file_name: &'static str,
    pkgs: &HashMap<String, Package>,
    games: &HashMap<String, Composition>,
) -> ParseTheoremError {
    let file = std::fs::File::open(format!("{TESTDATA_SSPCODE_PATH}/proofs/{file_name}"))
        .unwrap_or_else(|_| panic!("error opening test code proof {file_name}"));

    let contents = std::io::read_to_string(file)
        .unwrap_or_else(|_| panic!("error reading test code proof {file_name}"));

    parse_fails(&contents, file_name, pkgs, games)
}
