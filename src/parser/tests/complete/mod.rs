// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    games,
    packages::{self, *},
    slice_source_span, theorems,
};
use crate::{
    expressions::{Expression, ExpressionKind},
    gamehops::{equivalence, GameHop},
    identifier::{
        game_ident::{GameConstIdentifier, GameIdentifier},
        Identifier,
    },
    parser::theorem::ParseTheoremError,
    statement::Statement,
    theorem::Claim,
    transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform},
    types::{CountSpec, Type, TypeKind},
    util::smtsolver::process::{ProcessSmtSolverBackend, SolverVariant},
    writers::smt::contexts::EquivalenceContext,
};
use std::{
    collections::HashMap,
    fmt::Display,
    iter::FromIterator as _,
    sync::{Arc, RwLock},
};

use crate::ui::mock::TestUI;

#[test]
fn empty_param_section_is_fine() {
    let file_name = "test_file_name.ssp";
    let file_content = r#"package testpkg {
            params {}
        }
        "#;

    parse(file_content, file_name);
}

#[test]
fn reduction_context_matches_assumption_export_aliases() {
    let root = std::path::PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/test-projects/test-reduction-context-export-alias"
    ));
    let read_file = |file| std::fs::read_to_string(root.join(file)).unwrap();
    let pkgs = [
        "packages/Context.pkg.ssp",
        "packages/Real.pkg.ssp",
        "packages/Ideal.pkg.ssp",
    ]
    .into_iter()
    .map(|file| packages::parse(&read_file(file), file))
    .collect();
    let games = [
        "games/AssumptionReal.comp.ssp",
        "games/AssumptionIdeal.comp.ssp",
        "games/Left.comp.ssp",
        "games/Right.comp.ssp",
    ]
    .into_iter()
    .map(|file| {
        let game = games::parse(&read_file(file), file, &pkgs);
        (game.name.clone(), game)
    })
    .collect();
    let file = "theorem/proof.ssp";
    let source = read_file(file);
    let theorem = theorems::parse(&source, file, &pkgs, &games);
    assert_eq!(theorem.name, "ContextExportAlias");
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
            assert_eq!(error.left_signature.to_string(), "oracle () -> Integer");
            assert_eq!(error.right_signature.to_string(), "oracle () -> Integer");
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
                        assert_eq!(error.right_signature.to_string(), "oracle () -> Integer");
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
fn reduction_context_resolves_signature_parameters() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "BitLeaf.pkg.ssp", "BitRouter.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-leaf.comp.ssp",
            "reduction-context-oracle/Left-bits.comp.ssp",
            "reduction-context-oracle/Right-bits.comp.ssp",
        ],
        &pkgs,
    );
    let file = "reduction-context-oracle-bits.ssp";
    theorems::parse(&theorems::read_file(file), file, &pkgs, &games);
}

#[test]
fn disjoint_imports_across_compose_blocks() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "Router.pkg.ssp"]);
    let source = "composition Game {
        instance leaf = Leaf {}
        instance router = Router {}
        instance other = Router {}
        compose {
            router: { A: Eval of leaf }
            other: { A: Eval of leaf }
        }
        compose {
            router: { B: Eval of leaf }
            other: { B: Eval of leaf }
        }
    }";
    let game = games::parse(source, "disjoint-imports.ssp", &pkgs);
    assert_eq!(game.edges.len(), 4);
}

#[test]
fn empty_state_section_is_fine() {
    let file_name = "test_file_name.ssp";
    let file_content = r#"package testpkg {
            state {}
        }
        "#;

    parse(file_content, file_name);
}

#[test]
fn reduction_mapping_uses_first_parameter_assignment() {
    let pkgs = packages::parse_files(&["ParamLeaf.pkg.ssp"]);
    let games = games::parse_files(
        &[
            "AssumptionGame-repeated-params.comp.ssp",
            "ConstructionGame-first-parameter.comp.ssp",
        ],
        &pkgs,
    );
    let source = theorems::read_file("reduction-leaf-mapping.ssp");
    theorems::parse(&source, "reduction-leaf-mapping.ssp", &pkgs, &games);
}

#[test]
fn reduction_accepts_reversed_mapping_order() {
    let pkgs = packages::parse_files(&["Leaf.pkg.ssp"]);
    let games = games::parse_files(&["Game-leaf.comp.ssp"], &pkgs);
    // Reverse the header to exercise alignment with the first map on the right.
    let source = theorems::read_file("reduction-mapping-order.ssp");
    theorems::parse(&source, "reduction-mapping-order.ssp", &pkgs, &games);
}

#[test]
fn tiny_game_without_packages() {
    let game = games::parse_file("tiny.ssp", &HashMap::default());

    assert_eq!(game.name, "TinyGame");
    assert_eq!(game.consts[0].0, "n");
    assert_eq!(game.consts[0].1, Type::integer());
    assert_eq!(game.consts.len(), 1);
    assert!(game.pkgs.is_empty());
}

#[test]
fn tiny_package() {
    let (name, pkg) = parse_file("tiny.ssp");

    assert_eq!(name, "TinyPkg");
    assert_eq!(pkg.params.len(), 1);
    assert_eq!(pkg.params[0].0, "n");
    assert_eq!(pkg.params[0].1, Type::integer());
    assert_eq!(pkg.oracles.len(), 1);
    assert_eq!(pkg.oracles[0].sig.name, "N");
    assert_eq!(pkg.oracles[0].sig.ty, Type::integer());
    assert!(pkg.oracles[0].sig.args.is_empty());
    assert!(pkg.imports.is_empty());
}

#[test]
fn small_game() {
    let (name, pkg) = parse_file("tiny.ssp");
    let pkg_map = HashMap::from_iter(vec![(name, pkg.clone())]);
    let game = games::parse_file("small.ssp", &pkg_map);

    assert_eq!(game.name, "SmallGame");
    assert_eq!(game.consts.len(), 1);
    assert_eq!(game.consts[0].0, "n");
    assert_eq!(game.consts[0].1, Type::integer());
    assert_eq!(game.pkgs.len(), 1);
    assert_eq!(game.pkgs[0].name, "tiny_instance");
    assert_eq!(game.pkgs[0].params.len(), 1);
    assert_eq!(game.pkgs[0].params[0].0.ident_ref(), "n");
    assert_eq!(
        game.pkgs[0].params[0].1,
        Expression::from_kind(ExpressionKind::Identifier(Identifier::GameIdentifier(
            GameIdentifier::Const(GameConstIdentifier {
                name: "n".to_string(),
                ty: Type::integer(),
                game_name: "SmallGame".to_string(),
                game_inst_name: None,
                theorem_name: None,
                assigned_value: None,
                inst_info: None,
            })
        )))
    );
}

#[test]
fn small_for_package() {
    let (name, pkg) = parse_file("small_for.ssp");

    assert_eq!(name, "SmallForPkg");
    assert_eq!(pkg.params.len(), 1);
    assert_eq!(pkg.params[0].0, "n");
    assert_eq!(pkg.params[0].1, Type::integer());
    assert_eq!(pkg.oracles.len(), 1);
    assert_eq!(pkg.oracles[0].sig.name, "Sum");
    assert_eq!(pkg.oracles[0].sig.ty, Type::integer());
    assert!(pkg.oracles[0].sig.args.is_empty());
}

#[test]
fn untyped_none_type_inference_works() {
    let (_name, _pkg) = parse_file("none_inference_return.ssp");
}

#[test]
fn equivalence_parses() {
    let packages = parse_files(&["tiny.ssp"]);
    let games = games::parse_files(&["small.ssp"], &packages);
    let theorem_file = theorems::read_file("equivalence-small-small.ssp");
    let theorem = theorems::parse(
        &theorem_file,
        "equivalence-small-small.ssp",
        &packages,
        &games,
    );

    let eq = theorem
        .game_hops
        .iter()
        .find_map(|hop| match hop {
            GameHop::Equivalence(eq) => Some(eq),
            _ => None,
        })
        .unwrap();

    assert_eq!(eq.left_name, "smallA");
    assert_eq!(eq.right_name, "smallB");
    assert_eq!(eq.invariants, vec!["./invariant.smt".to_string()]);
    assert_eq!(
        eq.trees,
        vec![(
            "N".into(),
            vec![
                Claim {
                    name: "invariant".into(),
                    dependencies: vec![],
                    admitted: false
                },
                Claim {
                    name: "equal-aborts".into(),
                    dependencies: vec![],
                    admitted: false
                },
                Claim {
                    name: "same-output".into(),
                    dependencies: vec![],
                    admitted: false
                },
                Claim {
                    name: "smt_ident".into(),
                    dependencies: vec![],
                    admitted: false
                },
            ]
        )]
    );
}

#[test]
#[ignore]
fn equivalence_gamehome_generates_code() {
    let packages = parse_files(&["tiny.ssp"]);
    let games = games::parse_files(&["small.ssp"], &packages);
    let theorem_file = theorems::read_file("equivalence-small-small.ssp");
    let theorem = theorems::parse(
        &theorem_file,
        "equivalence-small-small.ssp",
        &packages,
        &games,
    );

    let eq = theorem
        .game_hops
        .iter()
        .find_map(|hop| match hop {
            GameHop::Equivalence(eq) => Some(eq),
            _ => None,
        })
        .unwrap();

    let backend = ProcessSmtSolverBackend::new(SolverVariant::Cvc5);
    let transcript = SharedVecWriter::default();
    let project = crate::project::DirectoryProject::empty();

    let (theorem, auxs) = EquivalenceTransform.transform_theorem(&theorem).unwrap();

    let mut eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
    eqctx
        .load_invariants(&project)
        .unwrap_or_else(|err| panic!("got error {err}.\n\ntranscript:\n{transcript}"));

    let mut driver = equivalence::EquivalenceSmtDriver::new(
        &eqctx, &project, &backend, false, None, None, 1, false, false,
    );
    driver
        .verify(TestUI::new())
        .unwrap_or_else(|err| panic!("got error {err}.\n\ntranscript:\n{transcript}"));
}

#[test]
fn game_instantiating_with_literal_works() {
    let pkgs = packages::parse_files(&["PRF.pkg.ssp", "KeyReal.pkg.ssp", "Enc.pkg.ssp"]);
    let game = games::parse_file("Game-instantiating-with-literal-works.comp.ssp", &pkgs);

    assert_eq!(game.name, "ConstructionReal");
    let prf = game
        .pkgs
        .iter()
        .find(|pkg_inst| pkg_inst.name == "Prf")
        .unwrap();

    assert_eq!(
        prf.params
            .iter()
            .find(|(id, _expr)| id.name == "n")
            .unwrap()
            .1,
        Expression::from_kind(ExpressionKind::Identifier(Identifier::GameIdentifier(
            GameIdentifier::Const(GameConstIdentifier {
                game_name: "ConstructionReal".to_string(),
                name: "n".to_string(),
                ty: Type::integer(),
                game_inst_name: None,
                theorem_name: None,
                inst_info: None,
                assigned_value: None
            })
        )))
    );
}

#[test]
fn package_empty_loop_works() {
    let (name, pkg) = parse_file("EmptyLoop.pkg.ssp");
    let k = "k".to_string();
    let h = "h".to_string();
    assert_eq!(name, "EmptyLoop");
    assert_eq!(pkg.params.len(), 1);
    assert_eq!(pkg.params[0].0, "n");
    assert_eq!(pkg.params[0].1, Type::integer());
    assert_eq!(pkg.oracles.len(), 2);
    assert_eq!(pkg.oracles[0].sig.name, "Set");
    assert_eq!(pkg.oracles[0].sig.ty, Type::empty());

    let (name, ty) = &pkg.oracles[0].sig.args[0];
    assert_eq!(name, &k);
    assert!(matches!(
    ty.kind(),
            TypeKind::Bits(bitlen) if matches!(bitlen, CountSpec::Identifier(bitlen) if bitlen.ident() == "n") ));

    let (name, ty) = &pkg.oracles[0].sig.args[1];
    assert_eq!(name, &h);
    assert!(matches!(
    ty.kind(),
            TypeKind::Bits(bitlen) if matches!(bitlen, CountSpec::Identifier(bitlen) if bitlen.ident() == "n") ));

    assert!(pkg.imports.is_empty());
    assert!(
        matches!(&pkg.oracles[0].code.0[0], Statement::For(i, start, end , _,_)
                if i.ident() == "i" && matches!(start.kind(), ExpressionKind::IntegerLiteral(1)) && matches!(end.kind(), ExpressionKind::Identifier(n) if n.ident() == "n"  )
        )
    );
    match &pkg.oracles[0].code.0[0] {
        Statement::For(i, start, end, _, _) => {
            assert!(matches!(start.kind(), ExpressionKind::IntegerLiteral(1)));
            assert_eq!(i.ident(), "i");
            let ExpressionKind::Identifier(n) = end.kind() else {
                panic!("expected identifier in loop end expression, got {end:?}")
            };
            assert_eq!(n.ident(), "n")
        }
        other => panic!("expected For, got {other:?}"),
    }
}

/// When instantiating a pacakge instance in a game, the name of the assigned constant must be
/// allowed to be different from the parameter.
///
#[test]
fn game_const_rename() {
    let pkgs = packages::parse_files(&["KeyRealMoreParams.pkg.ssp"]);
    let _games = games::parse_files(&["ConstRename.ssp", "ConstRename2.ssp"], &pkgs);
}

#[test]
fn theorem_const_rename() {
    let pkgs = packages::parse_files(&["KeyRealMoreParams.pkg.ssp"]);
    let games = games::parse_files(&["ConstRename.ssp", "ConstRename2.ssp"], &pkgs);

    dbg!(&pkgs);
    dbg!(&games);

    let _theorem = theorems::parse(
        &theorems::read_file("ConstRename.ssp"),
        "ConstRename.ssp",
        &pkgs,
        &games,
    );
}

/// This is a helper for transcripts. It can be cloned, and what is written in one clone can be
/// read in all others. It is concurrency-safe. This can be passed into the Communicator, a simple
/// `&mut Vec<u8>` can't. a `Vec<u8>` can, but then we lose access to it. This solves that problem.
#[derive(Clone, Default)]
struct SharedVecWriter(Arc<RwLock<Vec<u8>>>);

impl Display for SharedVecWriter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vec_guard = self.0.read().unwrap();
        let vec_ref: &Vec<u8> = vec_guard.as_ref();
        let string = String::from_utf8(vec_ref.to_vec()).unwrap();

        write!(f, "{string}")
    }
}

impl std::io::Write for SharedVecWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.write().as_mut().unwrap().write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.0.write().as_mut().unwrap().flush()
    }
}
