// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::parser::{
    error::{
        AssumptionAdversaryExportsNotSufficientError, AssumptionExportsNotSufficientError,
        AssumptionMappingContainsDifferentPackagesError, MissingGameParameterDefinitionError,
        ReductionPackageInstanceParameterMismatchError,
    },
    tests::{games, packages, slice_source_span, theorems},
    theorem::ParseTheoremError,
};

use std::collections::HashMap;

#[test]
fn context_oracle_mismatch_precedes_later_reduction_error() {
    let pkgs = packages::parse_files(&[
        "reduction-context-oracle/Context.pkg.ssp",
        "reduction-context-oracle/Choices.pkg.ssp",
    ]);
    let games = games::parse_files(
        &[
            "reduction-context-oracle/Assumption.comp.ssp",
            "reduction-context-oracle/Left.comp.ssp",
            "reduction-context-oracle/Right.comp.ssp",
        ],
        &pkgs,
    );
    let source = theorems::read_file("reduction-context-oracle.ssp");
    let source = source.replace(
        "    }\n}",
        "        reduction left right {
            assumption Missing
            map a0 left { x: x }
            map a1 right { x: x }
        }
    }\n}",
    );
    assert!(matches!(
        theorems::parse_fails(&source, "priority.ssp", &pkgs, &games),
        ParseTheoremError::ReductionContextOracleMismatch(_)
    ));
}

#[test]
fn reduction_context_preserves_destination_oracles() {
    let pkgs = packages::parse_files(&[
        "reduction-context-oracle/Context.pkg.ssp",
        "reduction-context-oracle/Choices.pkg.ssp",
    ]);
    for (right, valid) in [
        ("reduction-context-oracle/Right.comp.ssp", false),
        ("reduction-context-oracle/Right-control.comp.ssp", true),
    ] {
        let games = games::parse_files(
            &[
                "reduction-context-oracle/Assumption.comp.ssp",
                "reduction-context-oracle/Left.comp.ssp",
                right,
            ],
            &pkgs,
        );
        let file = "reduction-context-oracle.ssp";
        if valid {
            theorems::parse(&theorems::read_file(file), file, &pkgs, &games);
        } else {
            let error = theorems::parse_file_fails(file, &pkgs, &games);
            let ParseTheoremError::ReductionContextOracleMismatch(error) = error else {
                panic!("expected a context oracle mismatch, got {error:?}");
            };
            assert_eq!(error.import_name, "f");
            assert_eq!(error.left_oracle_name, "O1");
            assert_eq!(error.right_oracle_name, "O2");
            assert_eq!(error.left_signature, "oracle () -> Integer");
            assert_eq!(error.right_signature, "oracle () -> Integer");
            assert!(
                slice_source_span(&error.source_code, &error.at).starts_with("assumption Identity")
            );
        }
    }
}

#[test]
fn reduction_requires_matching_exports() {
    let pkgs = packages::parse_files(&["reduction-context-oracle/Choices.pkg.ssp"]);
    for (right, valid) in [
        ("reduction-exports/Right.comp.ssp", false),
        ("reduction-exports/Right-control.comp.ssp", true),
    ] {
        let games = games::parse_files(
            &[
                "reduction-context-oracle/Assumption.comp.ssp",
                "reduction-exports/Left.comp.ssp",
                right,
            ],
            &pkgs,
        );
        for file in [
            "reduction-context-oracle.ssp",
            "reduction-exports-reversed.ssp",
        ] {
            if valid {
                theorems::parse(&theorems::read_file(file), file, &pkgs, &games);
            } else {
                let error = theorems::parse_file_fails(file, &pkgs, &games);
                match error {
                    ParseTheoremError::ReductionExportMismatch(error) => {
                        assert_eq!(error.oracle_name, "O2");
                        assert_eq!(error.left_signature, "not exported");
                        assert_eq!(error.right_signature, "oracle () -> Integer");
                        assert!(slice_source_span(&error.source_code, &error.at)
                            .starts_with("assumption Identity"));
                    }
                    ParseTheoremError::ReductionMissingExport(error) => {
                        assert_eq!(error.game_inst_name, "left");
                        assert_eq!(error.oracle_name, "O2");
                    }
                    error => panic!("expected an export mismatch, got {error:?}"),
                }
            }
        }
    }
}

#[test]
fn reduction_requires_matching_export_signatures() {
    let pkgs = packages::parse_files(&["BitLeaf.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "reduction-exports/Bits.comp.ssp",
            "reduction-exports/Literal-bits.comp.ssp",
        ],
        &pkgs,
    );
    let file = "reduction-export-signatures-control.ssp";
    theorems::parse(&theorems::read_file(file), file, &pkgs, &games);
    let error = theorems::parse_file_fails("reduction-export-signatures.ssp", &pkgs, &games);
    let ParseTheoremError::ReductionExportMismatch(error) = error else {
        panic!("expected an export signature mismatch, got {error:?}");
    };
    assert_eq!(error.oracle_name, "Eval");
    assert_eq!(error.left_game_inst_name, "left");
    assert_eq!(error.right_game_inst_name, "right");
}

#[test]
fn missing_game_instance_params_block() {
    let games = games::parse_files(&["tiny.ssp"], &HashMap::new());
    let err = theorems::parse_file_fails("empty-params.ssp", &HashMap::new(), &games);

    assert!(
        matches!(
            &err,
            ParseTheoremError::MissingGameParameterDefinition( MissingGameParameterDefinitionError {
                game_name,
                game_inst_name,
                missing_params_vec,
                missing_params,
                ..
            }) if game_inst_name == "inst"
                    && game_name == "TinyGame"
                    && missing_params == "n"
                    && missing_params_vec.len() == 1
                    && missing_params_vec[0] == "n"
        ),
        "got instead:\n{err:?}",
        //err = err,
        err = miette::Report::new(err)
    );

    let report = miette::Report::new(err);
    println!("{report:?}");
}

#[test]
fn reduction_context_preserves_instance_sharing() {
    let pkgs = packages::parse_files(&[
        "reduction-context-instances/Context.pkg.ssp",
        "reduction-context-instances/Cell.pkg.ssp",
        "reduction-context-instances/Anchor.pkg.ssp",
    ]);
    for (left, right, valid) in [
        (
            "reduction-context-instances/Left.comp.ssp",
            "reduction-context-instances/Right.comp.ssp",
            false,
        ),
        (
            "reduction-context-instances/Left.comp.ssp",
            "reduction-context-instances/Right-control.comp.ssp",
            true,
        ),
        (
            "reduction-context-instances/Left-exports.comp.ssp",
            "reduction-context-instances/Right-exports.comp.ssp",
            false,
        ),
    ] {
        let games = games::parse_files(
            &[
                "reduction-context-instances/Assumption.comp.ssp",
                left,
                right,
            ],
            &pkgs,
        );
        for file in [
            "reduction-context-instances.ssp",
            "reduction-context-instances-reversed.ssp",
        ] {
            if valid {
                theorems::parse(&theorems::read_file(file), file, &pkgs, &games);
            } else {
                let error = theorems::parse_file_fails(file, &pkgs, &games);
                let ParseTheoremError::ReductionContextInstanceMismatch(error) = error else {
                    panic!("expected an instance sharing mismatch, got {error:?}");
                };
                assert_eq!(error.game_inst_name, "left");
                assert_eq!(error.pkg_inst_name, "x");
                assert_eq!(error.other_game_inst_name, "right");
                assert_eq!(error.previous_partner_name, "x");
                assert_eq!(error.partner_name, "y");
                assert!(slice_source_span(&error.source_code, &error.at)
                    .starts_with("assumption Identity"));
            }
        }
    }
}
#[test]
fn fail_reduction_assumption_is_second() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionReal.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails("reduction-assumption-2nd-should-fail.ssp", &pkgs, &games);

    let crate::parser::theorem::ParseTheoremError::AssumptionMappingRightGameInstanceIsFromAssumption(
        err,
    ) = err
    else {
        panic!("expected a different error. got error {err}")
    };

    let at = slice_source_span(&err.source_code, &err.at);
    assert_eq!(at, "assumptionreal");
}

#[test]
fn fail_reduction_construction_is_first() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionReal.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err =
        theorems::parse_file_fails("reduction-construction-1st-should-fail.ssp", &pkgs, &games);

    let crate::parser::theorem::ParseTheoremError::AssumptionMappingLeftGameInstanceIsNotFromAssumption(
        err,
    ) = err
    else {
        panic!("expected a different error. got error {err}")
    };

    let at = slice_source_span(&err.source_code, &err.at);
    assert_eq!(at, "constructionreal");
}

#[test]
fn fail_reduction_construction_game_inst_not_defined() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionReal.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-missing-1st-construction-game-instance-should-fail.ssp",
        &pkgs,
        &games,
    );

    let crate::parser::theorem::ParseTheoremError::UndefinedGameInstance(err) = err else {
        panic!("expected a different error. got error {err}")
    };

    let at = slice_source_span(&err.source_code, &err.at);
    assert_eq!(at, "constructionreal");
}

#[test]
fn fail_reduction_construction_game_inst_not_defined2() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionReal.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-missing-2nd-construction-game-instance-should-fail.ssp",
        &pkgs,
        &games,
    );

    let crate::parser::theorem::ParseTheoremError::UndefinedGameInstance(err) = err else {
        panic!("expected a different error. got error {err}")
    };

    let at = slice_source_span(&err.source_code, &err.at);
    assert_eq!(at, "constructionideal");
}

#[test]
fn fail_reduction_assumption_not_defined() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionReal.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-missing-assumption-should-fail.ssp",
        &pkgs,
        &games,
    );

    let crate::parser::theorem::ParseTheoremError::UndefinedAssumption(err) = err else {
        panic!("expected a different error. got error {err}")
    };

    let at = slice_source_span(&err.source_code, &err.at);
    assert_eq!(at, "Assumption");
}

#[test]
// this is a bit tricky.
// the test thinks it tests that the assumptions don't apply because one expose more than the
// others
// but the reason we fail is that the inner packages also do not match.
// so we should probably make the two match but then not expose all of them in one of the two games
fn fail_reduction_assumption_exposes_less() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionIdealWeak.comp.ssp",
            "AssumptionReal.comp.ssp",
            "AssumptionRealWeak.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-assumption-exposes-less-should-fail.ssp",
        &pkgs,
        &games,
    );

    let ParseTheoremError::AssumptionExportsNotSufficient(inner_err) = &err else {
        panic!("expected a different error. got {err}")
    };
    let AssumptionExportsNotSufficientError {
        source_code,
        assumption_at,
        construction_at,
        assumption_pkg_inst_name,
        construction_pkg_inst_name,
        oracle_name,
    } = inner_err.clone();

    let assumption_game_inst_name = slice_source_span(&source_code, &assumption_at);
    let construction_game_inst_name = slice_source_span(&source_code, &construction_at);

    let report = miette::Report::new(err);
    println!("the error prints like this:\n{report:?}");

    assert_eq!(assumption_pkg_inst_name, "key");
    assert_eq!(construction_pkg_inst_name, "key");
    assert_eq!(oracle_name, "Get");
    assert_eq!(assumption_game_inst_name, "key");
    assert_eq!(construction_game_inst_name, "key");
}

#[test]
fn fail_reduction_inconsistent_wiring_less() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionIdealWeak.comp.ssp",
            "AssumptionReal.comp.ssp",
            "AssumptionRealWeak.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionReal-badwiring.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-inconsistent-wiring-should-fail.ssp",
        &pkgs,
        &games,
    );

    let ParseTheoremError::AssumptionExportsNotSufficient(AssumptionExportsNotSufficientError {
        source_code,
        assumption_at,
        construction_at,
        assumption_pkg_inst_name,
        construction_pkg_inst_name,
        oracle_name,
    }) = &err
    else {
        panic!("expected a different error. got {err}")
    };

    let assumption_game_inst_name = slice_source_span(source_code, assumption_at);
    let construction_game_inst_name = slice_source_span(source_code, construction_at);

    assert_eq!(assumption_pkg_inst_name, "Prf");
    assert_eq!(construction_pkg_inst_name, "Prf");
    assert_eq!(oracle_name, "Get");
    assert_eq!(assumption_game_inst_name, "Prf");
    assert_eq!(construction_game_inst_name, "Prf");

    let report = miette::Report::new(err);
    println!("the error prints like this:\n{report:?}")
}

#[test]
fn fail_reduction_construction_exports_assumption_oracle() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdealWeak.comp.ssp",
            "AssumptionRealWeak.comp.ssp",
            "ConstructionReal-directexport.comp.ssp",
            "ConstructionIdeal-directexport.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-construction-exports-assumption-oracle-should-fail.ssp",
        &pkgs,
        &games,
    );

    let ParseTheoremError::AssumptionAdversaryExportsNotSufficient(
        AssumptionAdversaryExportsNotSufficientError {
            source_code,
            assumption_at,
            construction_at,
            assumption_pkg_inst_name,
            construction_pkg_inst_name,
            oracle_name,
        },
    ) = &err
    else {
        panic!("expected a different error. got {err}")
    };

    let assumption_game_inst_name = slice_source_span(source_code, assumption_at);
    let construction_game_inst_name = slice_source_span(source_code, construction_at);

    assert_eq!(assumption_pkg_inst_name, "key");
    assert_eq!(construction_pkg_inst_name, "key");
    assert_eq!(oracle_name, "Get");
    assert_eq!(assumption_game_inst_name, "key");
    assert_eq!(construction_game_inst_name, "key");

    let report = miette::Report::new(err);
    println!("the error prints like this:\n{report:?}")
}

#[test]
fn fail_reduction_non_matching_package_fail() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionIdealWeak.comp.ssp",
            "AssumptionReal.comp.ssp",
            "AssumptionRealWeak.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionRealWrongPackage.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-non-matching-package-should-fail.ssp",
        &pkgs,
        &games,
    );

    let ParseTheoremError::AssumptionMappingContainsDifferentPackages(
        AssumptionMappingContainsDifferentPackagesError {
            assumption_pkg_inst_name,
            construction_pkg_inst_name,

            assumption_pkg_name,
            construction_pkg_name,
            ..
        },
    ) = &err
    else {
        panic!("expected a different error. got {err}")
    };

    assert_eq!(assumption_pkg_inst_name, "key");
    assert_eq!(construction_pkg_inst_name, "key");
    assert_eq!(assumption_pkg_name, "KeyReal");
    assert_eq!(construction_pkg_name, "KeyIdeal");

    let report = miette::Report::new(err);
    println!("the error prints like this:\n{report:?}")
}

#[test]
#[ignore]
// TODO: we still have to implement this check
fn fail_reduction_changes_fail() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "Encnocall.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionReal.comp.ssp",
            "ConstructionReal-morebadwiring.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let _err = theorems::parse_file_fails("reduction-changes-should-fail.ssp", &pkgs, &games);

    //    let ParseTheoremError::InconsistentReductions(
    //        InconsistentReductions {
    //            construction_pkg_inst_name,
    //
    //            construction_pkg_name
    //        },
    //    ) = &err
    //    else {
    //      panic!("expected a different error. got {}", err)
    //    };
    //
    //    assert_eq!(construction_pkg_inst_name, "key");
    //    assert_eq!(construction_pkg_name, "KeyIdeal");

    //    let report = miette::Report::new(err);
    //    println!("the error prints like this:\n{:?}", report)
}

#[test]
fn fail_wrong_params_in_reduction_should_fail() {
    let pkgs = packages::parse_files(&[
        "Enc.pkg.ssp",
        "KeyIdeal.pkg.ssp",
        "KeyReal.pkg.ssp",
        "PRF.pkg.ssp",
    ]);

    let games = games::parse_files(
        &[
            "AssumptionIdeal.comp.ssp",
            "AssumptionIdealWeak.comp.ssp",
            "AssumptionReal.comp.ssp",
            "AssumptionRealWeak.comp.ssp",
            "ConstructionReal.comp.ssp",
            "ConstructionReal-badwiring.comp.ssp",
            "ConstructionIdeal.comp.ssp",
        ],
        &pkgs,
    );

    let err = theorems::parse_file_fails(
        "reduction-wrong-package-params-should-fail.ssp",
        &pkgs,
        &games,
    );

    let ParseTheoremError::ReductionPackageInstanceParameterMismatch(
        ReductionPackageInstanceParameterMismatchError {
            left_pkg_inst_name,
            right_pkg_inst_name,
            param_names,
            ..
        },
    ) = &err
    else {
        let err_str = format!("{err:#?}");
        let report = miette::Report::new(err);

        panic!("expected a different error. got {err_str}:\n{report:?}")
    };

    assert_eq!(left_pkg_inst_name, "Enc");
    assert_eq!(right_pkg_inst_name, "Enc");
    assert_eq!(param_names, "enc, m");

    let report = miette::Report::new(err);
    println!("the error prints like this:\n{report:?}")
}

#[test]
fn fail_reduction_missing_context_export() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-leaf.comp.ssp",
            "LeftGame-extra-export.comp.ssp",
            "RightGame-leaf.comp.ssp",
        ],
        &pkgs,
    );
    let error = theorems::parse_file_fails("reduction-context.ssp", &pkgs, &games);
    let ParseTheoremError::ReductionMissingExport(error) = error else {
        panic!("expected a missing export diagnostic, got {error:?}");
    };
    assert_eq!(error.game_inst_name, "c1");
    assert_eq!(error.oracle_name, "Extra");
    assert_eq!(
        slice_source_span(&error.source_code, &error.at),
        "assumption Basic
            map a0 c0 { leaf: leaf }
            map a1 c1 { leaf: leaf }"
    );
}

#[test]
fn fail_reduction_same_game_instance() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(&["Game-leaf.comp.ssp"], &pkgs);
    for (file, role, name, reduction) in [
        (
            "reduction-same-assumption-should-fail.ssp",
            "assumption",
            "a0",
            "assumption Basic
            map a0 c0 { leaf: leaf }
            map a0 c1 { leaf: leaf }",
        ),
        (
            "reduction-same-construction-should-fail.ssp",
            "construction",
            "c0",
            "assumption Basic
            map a0 c0 { leaf: leaf }
            map a1 c0 { leaf: leaf }",
        ),
    ] {
        let error = theorems::parse_file_fails(file, &pkgs, &games);
        let ParseTheoremError::ReductionSameGameInstance(error) = error else {
            panic!("expected a repeated game instance diagnostic, got {error:?}");
        };
        assert_eq!(error.role, role);
        assert_eq!(error.name, name);
        assert_eq!(slice_source_span(&error.source_code, &error.at), reduction);
    }
}

#[test]
fn fail_reduction_hybrid_mapping_without_bit() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(&["Game-leaf.comp.ssp"], &pkgs);
    let error = theorems::parse_file_fails(
        "reduction-hybrid-without-bit-should-fail.ssp",
        &pkgs,
        &games,
    );
    let ParseTheoremError::ReductionInvalidHybridMapping(error) = error else {
        panic!("expected a hybrid mapping diagnostic, got {error:?}");
    };
    assert_eq!(slice_source_span(&error.source_code, &error.at), "h");
}

#[test]
fn fail_reduction_mapped_wire_leaves_assumption() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "Router.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-wires-x-x.comp.ssp",
            "ConstructionGame-wires-outside-x.comp.ssp",
        ],
        &pkgs,
    );
    let error = theorems::parse_file_fails("reduction-router-mapping.ssp", &pkgs, &games);
    let ParseTheoremError::AssumptionMappingUnmappedDestination(error) = error else {
        panic!("expected an unmapped wire destination diagnostic, got {error:?}");
    };
    assert_eq!(error.from_pkg_inst_name, "router");
    assert_eq!(error.to_pkg_inst_name, "outside");
    assert_eq!(error.oracle_name, "Eval");
    assert_eq!(error.import_name, "A");
    let message = error.to_string();
    assert!(message.contains("imports A"), "{message}");
    assert!(message.contains("oracle Eval"), "{message}");
    assert_eq!(
        slice_source_span(&error.source_code, &error.at),
        "map a0 c0 { router: router x: x y: y }"
    );
}

#[test]
fn fail_reduction_construction_wiring_mismatch() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "Router.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-wires-x-x.comp.ssp",
            "ConstructionGame-wires-y-x.comp.ssp",
        ],
        &pkgs,
    );
    let error = theorems::parse_file_fails("reduction-router-mapping.ssp", &pkgs, &games);
    let ParseTheoremError::AssumptionMappingWiringMismatch(error) = error else {
        panic!("expected a construction wiring diagnostic, got {error:?}");
    };
    assert_eq!(error.direction, "construction to assumption");
    assert_eq!(error.assumption_game_name, "AssumptionGame");
    assert_eq!(error.construction_game_name, "ConstructionGame");
    assert_eq!(error.from_pkg_inst_name, "router");
    assert_eq!(error.to_pkg_inst_name, "y");
    assert_eq!(error.oracle_name, "Eval");
    assert_eq!(error.import_name, "A");
    let message = error.to_string();
    assert!(message.contains("imports A"), "{message}");
    assert!(message.contains("oracle Eval"), "{message}");
    assert_eq!(
        slice_source_span(&error.source_code, &error.at),
        "map a0 c0 { router: router x: x y: y }"
    );
    assert_eq!(error.oracle_signature, "oracle () -> Boolean");
}

#[test]
fn reduction_mapping_preserves_oracle_wiring() {
    let pkgs = packages::parse_files(&[
        "reduction-mapped-wiring/Router.pkg.ssp",
        "reduction-context-oracle/Choices.pkg.ssp",
    ]);
    for (right, valid) in [
        ("reduction-mapped-wiring/Right.comp.ssp", false),
        ("reduction-mapped-wiring/Right-control.comp.ssp", true),
    ] {
        let games = games::parse_files(
            &[
                "reduction-mapped-wiring/Assumption.comp.ssp",
                "reduction-mapped-wiring/Left.comp.ssp",
                right,
            ],
            &pkgs,
        );
        let file = "reduction-mapped-wiring.ssp";
        if valid {
            theorems::parse(&theorems::read_file(file), file, &pkgs, &games);
        } else {
            let error = theorems::parse_file_fails(file, &pkgs, &games);
            let ParseTheoremError::AssumptionMappingWiringMismatch(error) = error else {
                panic!("expected an internal oracle wiring mismatch, got {error:?}");
            };
            assert_eq!(error.reason, "import or destination oracle name differs");
            assert_eq!(error.direction, "construction to assumption");
            assert_eq!(error.from_pkg_inst_name, "router");
            assert_eq!(error.to_pkg_inst_name, "x");
            assert_eq!(error.import_name, "f");
            assert_eq!(error.oracle_name, "O2");
            assert_eq!(
                slice_source_span(&error.source_code, &error.at),
                "map a1 right { router: router x: x }"
            );
        }
    }
}

#[test]
fn reduction_checks_reverse_wires_before_the_next_package() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "Router.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-wiring-priority.comp.ssp",
            "ConstructionGame-wiring-priority.comp.ssp",
        ],
        &pkgs,
    );
    // The first package's reverse mismatch must precede the second package's
    // forward unmapped destination, even though both mappings are invalid.
    let error =
        theorems::parse_file_fails("reduction-wiring-priority-should-fail.ssp", &pkgs, &games);
    let ParseTheoremError::AssumptionMappingWiringMismatch(error) = error else {
        panic!("expected the first package's reverse mismatch, got {error:?}");
    };
    assert_eq!(error.direction, "assumption to construction");
    assert_eq!(error.from_pkg_inst_name, "first");
    assert_eq!(error.to_pkg_inst_name, "y");
    assert_eq!(error.assumption_game_name, "AssumptionGame");
    assert_eq!(error.construction_game_name, "ConstructionGame");
    assert_eq!(error.oracle_name, "Eval");
    assert_eq!(error.import_name, "B");
    assert_eq!(error.oracle_signature, "oracle () -> Boolean");
    let message = error.to_string();
    assert!(message.contains("imports B"), "{message}");
    assert!(message.contains("oracle Eval"), "{message}");
    assert_eq!(
        slice_source_span(&error.source_code, &error.at),
        "map a0 c0 { first: first second: second x: x y: y }"
    );
}

#[test]
fn fail_reduction_package_parameter_count_mismatch() {
    let pkgs = packages::parse_files(&["ParamLeaf.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-param-leaf.comp.ssp",
            "ConstructionGame-repeated-params.comp.ssp",
        ],
        &pkgs,
    );
    let error = theorems::parse_file_fails("reduction-leaf-mapping.ssp", &pkgs, &games);
    let ParseTheoremError::ReductionPackageParameterCountMismatch(error) = error else {
        panic!("expected a parameter count diagnostic, got {error:?}");
    };
    assert_eq!(error.left_count, 1);
    assert_eq!(error.right_count, 2);
    assert_eq!(
        slice_source_span(&error.source_code, &error.at),
        "map a0 c0 { leaf: leaf }"
    );
}

#[test]
fn fail_reduction_incoming_parameter_mismatch() {
    let pkgs = packages::parse_files(&["ParamLeaf.pkg.ssp", "Router.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-repeated-params.comp.ssp",
            "ConstructionGame-incoming-params.comp.ssp",
        ],
        &pkgs,
    );
    // Mapping comparison visits both assumption values against the first
    // construction value. The incoming-wire check compares in reverse order.
    let error = theorems::parse_file_fails("reduction-leaf-mapping.ssp", &pkgs, &games);
    let ParseTheoremError::AssumptionMappingParameterMismatch(error) = error else {
        panic!("expected an incoming parameter mismatch diagnostic, got {error:?}");
    };
    assert_eq!(error.assumption_pkg_inst_name, "leaf");
    assert_eq!(error.construction_pkg_inst_name, "leaf");
    assert_eq!(error.param_names, "flag");
    assert_eq!(
        slice_source_span(&error.source_code, &error.at_assumption),
        "leaf"
    );
    assert_eq!(
        slice_source_span(&error.source_code, &error.at_construction),
        "leaf"
    );
}

#[test]
fn reduction_incoming_signature_respects_build_mode() {
    let pkgs = packages::parse_files(&["BitLeaf.pkg.ssp", "BitRouter.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-bit-leaf.comp.ssp",
            "ConstructionGame-bit-router.comp.ssp",
        ],
        &pkgs,
    );
    #[cfg(debug_assertions)]
    {
        let error = theorems::parse_file_fails("reduction-incoming-signature.ssp", &pkgs, &games);
        let ParseTheoremError::AssumptionMappingOracleSignatureMismatch(error) = error else {
            panic!("expected an incoming signature mismatch diagnostic, got {error:?}");
        };
        assert_eq!(error.oracle_name, "Eval");
        assert!(error.assumption_signature.starts_with("oracle (Bits("));
        // As on main, the construction side is rewritten with game constants only,
        // so the router's package parameter is still symbolic here.
        assert_eq!(error.construction_signature, "oracle (Bits(n)) -> Bits(n)");
        assert_eq!(error.assumption_game_name, "AssumptionGame");
        assert_eq!(error.construction_game_name, "ConstructionGame");
        assert_eq!(
            slice_source_span(&error.source_code, &error.at),
            "map a0 c0 { leaf: leaf }"
        );
    }
    #[cfg(not(debug_assertions))]
    theorems::parse(
        &theorems::read_file("reduction-incoming-signature.ssp"),
        "reduction-incoming-signature.ssp",
        &pkgs,
        &games,
    );
}

#[test]
fn reduction_context_reports_first_declared_import() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "ParamLeaf.pkg.ssp", "Router.pkg.ssp"]);
    let mut games = games::parse_files(
        &[
            "AssumptionGame-leaf.comp.ssp",
            "LeftGame-import-order.comp.ssp",
            "RightGame-import-order.comp.ssp",
        ],
        &pkgs,
    );
    // Reproduce either order that the package parser's HashMap can produce.
    // Both imports fail, with different error kinds; declaration A must win.
    for reverse in [false, true] {
        for game in games.values_mut() {
            for instance in &mut game.pkgs {
                instance.pkg.imports.sort_by_key(|(_, span)| span.offset());
                if reverse {
                    instance.pkg.imports.reverse();
                }
            }
        }
        let error = theorems::parse_file_fails("reduction-context.ssp", &pkgs, &games);
        assert!(
            matches!(
                &error,
                ParseTheoremError::ReductionInconsistentAssumptionBoundary(_)
            ),
            "got instead:\n{error:?}",
            error = miette::Report::new(error)
        );
    }
}

#[test]
fn reduction_context_compares_both_members_of_a_pair() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "ParamLeaf.pkg.ssp", "Router.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-leaf.comp.ssp",
            "LeftGame-shared-pair.comp.ssp",
            "RightGame-distinct-pairs.comp.ssp",
        ],
        &pkgs,
    );
    for (file, expected_left, expected_right) in [
        ("reduction-context.ssp", "shared", "second"),
        ("reduction-context-reversed.ssp", "second", "shared"),
    ] {
        let error = theorems::parse_file_fails(file, &pkgs, &games);
        let ParseTheoremError::ReductionContainsDifferentPackages(error) = error else {
            panic!("expected a package mismatch for the second pair, got {error:?}");
        };
        assert_eq!(error.left_pkg_inst_name, expected_left);
        assert_eq!(error.right_pkg_inst_name, expected_right);
    }
}

#[test]
fn fail_reduction_cyclic_context() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "Router.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-leaf.comp.ssp",
            "ConstructionGame-cyclic-context.comp.ssp",
        ],
        &pkgs,
    );
    let error = theorems::parse_file_fails("reduction-leaf-mapping.ssp", &pkgs, &games);
    let ParseTheoremError::ReductionCyclicContext(error) = error else {
        panic!("expected a cyclic context diagnostic, got {error:?}");
    };
    assert_eq!(error.left_pkg_inst_name, "router");
    assert_eq!(error.right_pkg_inst_name, "router");
    assert_eq!(
        slice_source_span(&error.source_code, &error.at),
        "assumption Basic
            map a0 c0 { leaf: leaf }
            map a1 c1 { leaf: leaf }"
    );
}

#[test]
fn reduction_requires_complete_assumption_coverage_in_both_maps() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(&["Game-spare-leaf.comp.ssp"], &pkgs);
    for (file, short_map) in [
        (
            "reduction-missing-a0-coverage-should-fail.ssp",
            "map a0 c0 { leaf: leaf }",
        ),
        (
            "reduction-missing-a1-coverage-should-fail.ssp",
            "map a1 c1 { leaf: leaf }",
        ),
    ] {
        let error = theorems::parse_file_fails(file, &pkgs, &games);
        let ParseTheoremError::AssumptionMappingMissesPackageInstance(error) = error else {
            panic!("expected missing assumption coverage, got {error:?}");
        };
        assert_eq!(error.pkg_inst_name, "spare");
        assert_eq!(slice_source_span(&error.source_code, &error.at), short_map);
    }
}

#[test]
fn reduction_duplicate_assignment_names_the_duplicated_side() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-renamed-packages.comp.ssp",
            "ConstructionGame-renamed-packages.comp.ssp",
        ],
        &pkgs,
    );
    for (file, expected) in [
        (
            "reduction-duplicate-construction-package-should-fail.ssp",
            "x",
        ),
        (
            "reduction-duplicate-assumption-package-should-fail.ssp",
            "a",
        ),
        ("reduction-duplicate-both-package-should-fail.ssp", "a"),
    ] {
        let error = theorems::parse_file_fails(file, &pkgs, &games);
        let ParseTheoremError::AssumptionMappingDuplicatePackageInstance(error) = error else {
            panic!("expected a duplicate mapping diagnostic, got {error:?}");
        };
        assert_eq!(error.pkg_inst_name, expected);
        assert_eq!(
            slice_source_span(&error.source_code, &error.at_this),
            expected
        );
        assert_eq!(
            slice_source_span(&error.source_code, &error.at_prev),
            expected
        );
    }
}

#[test]
fn reduction_undefined_assignment_names_the_missing_side() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-renamed-packages.comp.ssp",
            "ConstructionGame-renamed-packages.comp.ssp",
        ],
        &pkgs,
    );
    for (file, expected, game) in [
        (
            "reduction-undefined-construction-package-should-fail.ssp",
            "absent",
            "ConstructionGame",
        ),
        (
            "reduction-undefined-assumption-package-should-fail.ssp",
            "missing",
            "AssumptionGame",
        ),
        (
            "reduction-undefined-both-package-should-fail.ssp",
            "missing",
            "AssumptionGame",
        ),
    ] {
        let error = theorems::parse_file_fails(file, &pkgs, &games);
        let ParseTheoremError::UndefinedPackageInstance(error) = error else {
            panic!("expected an undefined package diagnostic, got {error:?}");
        };
        assert_eq!(error.pkg_inst_name, expected);
        assert_eq!(error.in_game, game);
        assert_eq!(slice_source_span(&error.source_code, &error.at), expected);
    }
}
