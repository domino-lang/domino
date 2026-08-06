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

#[test]
fn parse_model_captures_function_args() {
    let content = r#"(
        (define-fun <<func-mac>> ((_arg_1 Bits_n) (_arg_2 Int)) Bits_n (as @Bits_n_0 Bits_n))
        (define-fun <domino-model-info-theorem> () String "Full4WHS")
    )"#;

    let (model, _len) = parse_model(content).unwrap();

    let entry = model.get_value("<<func-mac>>").unwrap();
    assert_eq!(
        entry.args(),
        &[
            ("_arg_1".to_string(), "Bits_n".to_string()),
            ("_arg_2".to_string(), "Int".to_string()),
        ]
    );

    assert_eq!(
        model.get_value_as_string("<domino-model-info-theorem>"),
        Some("Full4WHS".to_string())
    );
}
