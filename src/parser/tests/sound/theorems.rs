use crate::parser::{
    error::{
        AssumptionExportsNotSufficientError, AssumptionMappingContainsDifferentPackagesError,
        ReductionPackageInstanceParameterMismatchError,
    },
    theorem::ParseTheoremError,
    tests::{games, packages, theorems, slice_source_span},
};

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

    let err = theorems::parse_file_fails("reduction-construction-1st-should-fail.ssp", &pkgs, &games);

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

    assert_eq!(assumption_pkg_inst_name, "prf");
    assert_eq!(construction_pkg_inst_name, "prf");
    assert_eq!(oracle_name, "Get");
    assert_eq!(assumption_game_inst_name, "prf");
    assert_eq!(construction_game_inst_name, "prf");

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

    assert_eq!(left_pkg_inst_name, "enc");
    assert_eq!(right_pkg_inst_name, "enc");
    assert_eq!(param_names, "enc, m");

    let report = miette::Report::new(err);
    println!("the error prints like this:\n{report:?}")
}
