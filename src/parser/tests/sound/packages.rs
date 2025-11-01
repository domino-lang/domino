// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    parser::{
        common::HandleTypeError,
        error::{
            NoSuchTypeError, TypeMismatchError, UndefinedIdentifierError,
            WrongArgumentCountInInvocationError,
        },
        package::{ParseExpressionError, ParsePackageError},
        tests::{packages, slice_source_span},
    },
    types::{CountSpec, Type},
};

#[test]
fn undefined_type_in_pkg_params() {
    let err = packages::parse_file_fails("bad_param_type.ssp");
    assert!(
        matches!(err, ParsePackageError::HandleType(HandleTypeError::NoSuchType(NoSuchTypeError {
                type_name,
                ..
            }))
            if &type_name == "ThisTypeDoesNotExist"
        )
    )
}

#[test]
fn undefined_type_in_pkg_state() {
    let err = packages::parse_file_fails("bad_state_type.ssp");
    assert!(
        matches!(err, ParsePackageError::HandleType(HandleTypeError::NoSuchType(NoSuchTypeError {
                type_name,
                ..
            }))
            if &type_name == "ThisTypeDoesNotExist"
        )
    )
}

#[test]
fn type_mismatch_in_assignment_to_statevar() {
    let err = packages::parse_file_fails("state_assignment_type_mismatch.ssp");

    match err {
        ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
            TypeMismatchError {
                at,
                expected,
                got,
                source_code,
            },
        )) => {
            assert_eq!(expected, Type::Integer);
            assert_eq!(got, Type::Boolean);
            assert_eq!(slice_source_span(&source_code, &at), "false");
        }
        other => {
            let msg = format!("expected a different error; got {other:?}");
            let report = miette::Report::new(other);
            panic!("{msg}, which looks like this:\n{report:?}")
        }
    };
}

#[test]
fn wrong_return_type_fails() {
    let err = packages::parse_file_fails("tiny_bad1.ssp");

    assert!(
        matches!(
            err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                TypeMismatchError {
                    expected: Type::String,
                    got: Type::Integer,
                    ..
                }
            ))
        ),
        "expected a different error, got {err:#?}"
    )
}

#[test]
fn missing_identifier_fails() {
    let err = packages::parse_file_fails("tiny_bad2.ssp");

    assert!(matches!(
        err,
        ParsePackageError::ParseExpression(ParseExpressionError::UndefinedIdentifier(
                UndefinedIdentifierError { ref ident_name, .. }
        )) if ident_name.as_str() == "n"

    ));

    println!("{:?}", miette::Report::new(err));
}

#[test]
fn bad_add_fails_1() {
    let err = packages::parse_file_fails("tiny_bad3.ssp");

    assert!(
        matches!(
            err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                    TypeMismatchError {
                        expected: Type::Integer,
                        got: Type::Boolean,
                        ref at,
                        ref source_code,
                    }
                )) if slice_source_span(source_code, at) == "true"
        ),
        "got: {err:#?}"
    );

    println!("{:?}", miette::Report::new(err));
}

#[test]
fn bad_add_fails_2() {
    let err = packages::parse_file_fails("tiny_bad4.ssp");

    assert!(
        matches!(
            err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                    TypeMismatchError {
                        expected: Type::Integer,
                        got: Type::Boolean,
                        ref at,
                        ref source_code,
                    }
            )) if slice_source_span(source_code, at) == "true"
        ),
        "got: {err:#?}"
    );

    println!("{:?}", miette::Report::new(err));
}

#[test]
fn bad_add_fails_3() {
    let err = packages::parse_file_fails("tiny_bad5.ssp");

    assert!(
        matches!(
            err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                    TypeMismatchError {
                        expected: Type::Integer,
                        got: Type::Boolean,
                        ref at,
                        ref source_code,
                    }
            )) if slice_source_span(source_code, at) == "true"
        ),
        "got: {err:#?}"
    );

    println!("{:?}", miette::Report::new(err));
}

#[test]
fn bad_add_fails_4() {
    let err = packages::parse_file_fails("tiny_bad6.ssp");

    assert!(
        matches!(
            err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                    TypeMismatchError {
                        expected: Type::Boolean,
                        got: Type::Integer,
                        ref at,
                        ref source_code,
                    },
            )) if slice_source_span(source_code, at) == "(3 + 2)"
        ),
        "got: {err:#?}"
    );

    println!("{:?}", miette::Report::new(err));
}

#[test]
fn loop_start_non_integer_fails() {
    let err = packages::parse_file_fails("EmptyLoopStartNonIntegerFails.pkg.ssp");

    assert!(matches!(
            &err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                TypeMismatchError {
                    expected: Type::Integer,
                    got: Type::Bits(countspec),
                    ..
                }
            )) if matches!(&**countspec, CountSpec::Identifier(ident) if ident.ident_ref() == "n")));
}

#[test]
fn loop_end_non_integer_fails() {
    let err = packages::parse_file_fails("EmptyLoopEndNonIntegerFails.pkg.ssp");

    assert!(matches!(
            &err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                TypeMismatchError {
                    expected: Type::Integer,
                    got: Type::Bits(countspec),
                    ..
                }
            )) if matches!(&**countspec, CountSpec::Identifier(ident) if ident.ident_ref() == "n")));
}

#[test]
fn invoke_wrong_argument_types() {
    let err = packages::parse_file_fails("InvokeWrongArgumentTypes.ssp");

    assert!(
        matches!(
            &err,
            ParsePackageError::ParseExpression(ParseExpressionError::TypeMismatch(
                TypeMismatchError {
                    expected: Type::Integer,
                    got: Type::Bits(_),
                    ..
                }
            ))
        ),
        "{:?}",
        miette::Report::new(err)
    );
}

#[test]
fn invoke_wrong_argument_count() {
    let err = packages::parse_file_fails("InvokeWrongArgumentCount.ssp");

    assert!(
        matches!(
            &err,
            ParsePackageError::WrongArgumentCountInInvocation(
                WrongArgumentCountInInvocationError {
                    expected_num: 2,
                    got_num: 1,
                    ..
                }
            )
        ),
        "{:?}",
        miette::Report::new(err)
    );
}
