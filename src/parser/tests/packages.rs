// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{collections::HashMap, iter::FromIterator as _};

use crate::{
    package::Package,
    parser::{
        package::{handle_pkg, ParsePackageError},
        tests::TESTDATA_SSPCODE_PATH,
        SspParser,
    },
};

pub fn parse(code: &str, file_name: &str) -> (String, Package) {
    let mut pkg_pairs = SspParser::parse_package(code)
        .unwrap_or_else(|err| panic!("error parsing package {file_name} (in call to pest): {err}"));
    handle_pkg(file_name, code, pkg_pairs.next().unwrap())
        .map_err(|err| {
            println!("Error: {err:?}");
            miette::Report::new(err)
        })
        .unwrap()
}

pub fn parse_fails(code: &str, name: &str) -> ParsePackageError {
    // any test game should adhere to the grammar
    let mut pkg_pairs = SspParser::parse_package(code)
        .unwrap_or_else(|err| panic!("error parsing package {name} (in call to pest): {err}"));

    handle_pkg(name, code, pkg_pairs.next().unwrap()).expect_err(&format!(
        "expected an error when parsing {name}, but it succeeded"
    ))
}

pub fn parse_file(file_name: &str) -> (String, Package) {
    let file = std::fs::File::open(format!("{TESTDATA_SSPCODE_PATH}/packages/{file_name}"))
        .unwrap_or_else(|_| panic!("error opening test code package {file_name}"));

    let contents = std::io::read_to_string(file)
        .unwrap_or_else(|_| panic!("error reading test code package {file_name}"));

    parse(&contents, file_name)
}

pub fn parse_files(file_names: &[&str]) -> HashMap<String, Package> {
    HashMap::from_iter(file_names.iter().cloned().map(parse_file))
}

pub fn parse_file_fails(file_name: &str) -> ParsePackageError {
    let file = std::fs::File::open(format!("{TESTDATA_SSPCODE_PATH}/packages/{file_name}"))
        .unwrap_or_else(|_| panic!("error opening test code package {file_name}"));

    let contents = std::io::read_to_string(file)
        .unwrap_or_else(|_| panic!("error reading test code package {file_name}"));

    parse_fails(&contents, file_name)
}
