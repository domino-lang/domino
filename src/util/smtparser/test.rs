use super::parse_model;
use crate::assert_matches;

#[test]
fn parse_model_files() {
    let file = std::fs::File::open("src/util/smtparser/testdata/model.smt2").unwrap();
    let content = std::io::read_to_string(file).unwrap();

    let (model, length) = parse_model(&content).unwrap();
    dbg!(&model);

    assert_eq!(length, 3209);
    assert_eq!(
        model.get_value_as_int("randctr-small_composition-0"),
        Some(0)
    );
    assert_eq!(model.get_value_as_bool("<equal-aborts>"), Some(true));
}

#[test]
fn only_parses_one_model() {
    let file = std::fs::File::open("src/util/smtparser/testdata/model_double.smt2").unwrap();
    let content = std::io::read_to_string(file).unwrap();

    let (_model, length) = parse_model(&content).unwrap();

    assert_eq!(length, 3209);
}

#[test]
fn parsing_half_model_fails() {
    let file = std::fs::File::open("src/util/smtparser/testdata/model_half.smt2").unwrap();
    let content = std::io::read_to_string(file).unwrap();

    assert_matches!(parse_model(&content), Err(_));
}
