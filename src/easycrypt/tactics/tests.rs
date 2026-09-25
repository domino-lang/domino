// SPDX-License-Identifier: MIT OR Apache-2.0

use super::driver::{pair_view, Part};
use super::*;
use crate::debug::driver::{TerminalView, Verdict};
use crate::debug::lockstep::{PairRecord, PairSide, RelationVerdict};

fn pair_view_for_tests(p: &PairRecord, part: &Part) -> &'static str {
    pair_view(p, part).slug()
}

fn side(is_abort: bool) -> PairSide {
    PairSide {
        steps: vec![],
        terminal: TerminalView {
            label: 1,
            line: String::new(),
            is_abort,
        },
        lines: vec![],
        effect: None,
    }
}

fn pair(
    equal_output: Verdict,
    invariant: Verdict,
    relations: &[(&str, Verdict)],
    aborts: bool,
) -> PairRecord {
    PairRecord {
        id: "J1".into(),
        node: 0,
        left: side(aborts),
        right: side(false),
        equal_output,
        invariant,
        relations: relations
            .iter()
            .map(|(name, verdict)| RelationVerdict {
                name: name.to_string(),
                verdict: verdict.clone(),
            })
            .collect(),
    }
}

fn fails() -> Verdict {
    Verdict::GoalFails { model: "m".into() }
}

#[test]
fn smt_hints_come_from_the_easycrypt_table_of_ssp_toml() {
    assert_eq!(parse_smt_hints("").unwrap(), Vec::<String>::new());
    assert_eq!(
        parse_smt_hints("[other]\nx = 1\n").unwrap(),
        Vec::<String>::new()
    );
    assert_eq!(
        parse_smt_hints("[easycrypt]\nsmt_hints = [\"get_set_sameE\", \"Foo.bar_1\"]\n").unwrap(),
        vec!["get_set_sameE".to_string(), "Foo.bar_1".to_string()]
    );
    // a hint ends up in a tactic: only lemma names are accepted
    assert!(parse_smt_hints("[easycrypt]\nsmt_hints = [\"a). admit\"]\n").is_err());
    assert!(parse_smt_hints("[easycrypt]\nsmt_hints = \"x\"\n").is_err());
    assert!(parse_smt_hints("[easycrypt]\nsmt_hints = [1]\n").is_err());
    assert!(parse_smt_hints("not toml [").is_err());
}

#[test]
fn a_missing_ssp_toml_means_no_hints() {
    let dir = tempfile::tempdir().unwrap();
    assert!(read_smt_hints(dir.path()).unwrap().is_empty());
    std::fs::write(
        dir.path().join("ssp.toml"),
        "[easycrypt]\nsmt_hints = [\"mem_set\"]\n",
    )
    .unwrap();
    assert_eq!(
        read_smt_hints(dir.path()).unwrap(),
        vec!["mem_set".to_string()]
    );
}

#[test]
fn an_admit_label_names_the_id_the_claim_the_reason_and_dominos_verdict() {
    let admit = Admit {
        reason: AdmitReason::DominoVerifiedEcFailed,
        id: "J7".into(),
        claim: "invariant/Domino_rel_keys".into(),
        domino: DominoView::Verified,
        goal: String::new(),
    };
    assert_eq!(
        admit.label(),
        "(* domino: J7 invariant/Domino_rel_keys; reason: domino-verified-ec-failed; Domino: verified *)"
    );
    // a sentence with such a comment is still one sentence for the session
    let sentences = split_sentences(&format!("admit. {}\nauto.", admit.label()));
    assert_eq!(sentences, vec!["admit.", "auto."]);
    // every slug is distinct
    let mut slugs: Vec<_> = AdmitReason::ALL.iter().map(|r| r.slug()).collect();
    slugs.sort_unstable();
    slugs.dedup();
    assert_eq!(slugs.len(), AdmitReason::ALL.len());
}

#[test]
fn dominos_verdicts_steer_per_claim_and_per_relation() {
    // equal-output fails, the invariant holds
    let p = pair(fails(), Verdict::Verified, &[], false);
    assert_eq!(pair_view_for_tests(&p, &Part::EqualOutput), "fails");
    assert_eq!(pair_view_for_tests(&p, &Part::Invariant), "verified");
    assert_eq!(pair_view_for_tests(&p, &Part::Whole), "fails");

    // one relation fails: only it does
    let p = pair(
        Verdict::Verified,
        fails(),
        &[("a", Verdict::Verified), ("b", fails())],
        false,
    );
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("a".into())),
        "verified"
    );
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("b".into())),
        "fails"
    );
    // a relation the sub-verdicts do not list falls back to the invariant's verdict
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("c".into())),
        "fails"
    );

    // unreachable pairs count as verified; inconclusive stays inconclusive
    let p = pair(
        Verdict::Unreachable,
        Verdict::Inconclusive { model: None },
        &[],
        false,
    );
    assert_eq!(pair_view_for_tests(&p, &Part::EqualOutput), "verified");
    assert_eq!(pair_view_for_tests(&p, &Part::Invariant), "inconclusive");
}

#[test]
fn an_invariant_failure_where_a_side_aborts_is_not_held_against_easycrypt() {
    // story 23: Domino's invariant verdict is stricter than EasyCrypt's `inv` at abort pairs
    let p = pair(Verdict::Verified, fails(), &[("a", fails())], true);
    assert_eq!(pair_view_for_tests(&p, &Part::Invariant), "inconclusive");
    assert_eq!(
        pair_view_for_tests(&p, &Part::Relation("a".into())),
        "inconclusive"
    );
    // equal-output has no such exemption
    let p = pair(fails(), Verdict::Verified, &[], true);
    assert_eq!(pair_view_for_tests(&p, &Part::EqualOutput), "fails");
}

fn oracle_with(admits: Vec<Admit>) -> OracleTactics {
    OracleTactics {
        oracle: "O".into(),
        problem: None,
        stats: OracleStats {
            closed: 4,
            admits,
            fallbacks: 0,
            attempts_undone: 2,
        },
        alignment_mismatches: vec![],
        joint_paths: 2,
        nodes: 7,
        stuck_points: 1,
        lockstep_time: Duration::from_millis(100),
        easycrypt_time: Duration::from_secs(3),
        script: String::new(),
        reverted: false,
    }
}

fn admit(reason: AdmitReason, id: &str) -> Admit {
    Admit {
        reason,
        id: id.into(),
        claim: "equal-output".into(),
        domino: DominoView::Verified,
        goal: "x = y".into(),
    }
}

#[test]
fn the_report_counts_admits_by_reason_and_lists_the_verified_ones_with_their_goal() {
    let o = oracle_with(vec![
        admit(AdmitReason::Stuck, "S1"),
        admit(AdmitReason::DominoVerifiedEcFailed, "J2"),
        admit(AdmitReason::DominoVerifiedEcFailed, "J3"),
    ]);
    assert_eq!(
        o.admits_by_reason(),
        vec![
            (AdmitReason::Stuck, 1),
            (AdmitReason::DominoVerifiedEcFailed, 2)
        ]
    );
    let eq = EquivalenceTactics {
        proofstep: 0,
        proof_file: "Eq_A_B.ec".into(),
        left: "A".into(),
        right: "B".into(),
        oracles: vec![o],
        base_case_admitted: false,
        elapsed: Duration::from_secs(4),
        report_file: "Eq_A_B.report.txt".into(),
    };
    let report = eq.render();
    assert!(
        report.contains("3 admits (stuck 1, domino-verified-ec-failed 2)"),
        "{report}"
    );
    assert!(report.contains("goals closed: 4"), "{report}");
    assert!(
        report.contains("admit J2 equal-output [domino-verified-ec-failed]"),
        "{report}"
    );
    // only that class carries the goal text
    assert_eq!(report.matches("goal: x = y").count(), 2, "{report}");
    assert!(
        report.contains("1 oracles, 4 goals closed, 3 admits"),
        "{report}"
    );
}

/// The `admit` sentences of a proof file with their labels' reasons.
fn labelled_admits(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|line| {
            let (_, label) = line.split_once("admit. (* domino: ")?;
            let reason = label.split_once("reason: ")?.1;
            Some(reason.split([';', ' ']).next().unwrap().to_string())
        })
        .collect()
}

#[test]
fn labels_are_read_back_from_the_file() {
    let text = "  + admit. (* domino: J1 invariant; reason: stuck; Domino: verified *)\n\
                  admit. (* domino: N4 program; reason: program-mismatch; Domino: inconclusive *)\n\
                + proc; inline. admit.\n";
    assert_eq!(labelled_admits(text), vec!["stuck", "program-mismatch"]);
}

#[cfg(feature = "cvc5-lib")]
mod live {
    use std::path::PathBuf;

    use super::*;
    use crate::easycrypt::check::{ok_or_reject, sentences_until_call};
    use crate::easycrypt::session::{json_binary_configured, split_sentences, Session};
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::cvc5lib::Cvc5LibBackend;
    use crate::writers::easycrypt::export::{export_theorem, write_files};

    fn run(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
    ) -> Option<(TheoremTactics, tempfile::TempDir)> {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return None;
        }
        let dir = PathBuf::from(dir);
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem(theorem).unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();
        let result = run_tactics(
            theorem,
            &project,
            &exported,
            out.path(),
            &Cvc5LibBackend::new(true, None),
            options,
        )
        .unwrap();
        Some((result, out))
    }

    fn proof_file(result: &TheoremTactics, out: &Path) -> String {
        std::fs::read_to_string(out.join(&result.equivalences[0].proof_file)).unwrap()
    }

    #[test]
    fn hello_world_useful_oracle_closes_with_no_admit_and_compiles() {
        let Some((result, out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions::default(),
        ) else {
            return;
        };
        let oracle = &result.equivalences[0].oracles[0];
        assert_eq!(oracle.oracle, "UsefulOracle");
        assert!(oracle.problem.is_none());
        assert!(oracle.stats.admits.is_empty(), "{}", result.render());
        assert!(!oracle.reverted);
        let text = proof_file(&result, out.path());
        assert!(!text.contains("admit"), "{text}");
        assert!(compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &result.equivalences[0].proof_file
        )
        .is_ok());
        // the report is written next to the file and is what stdout shows
        let report =
            std::fs::read_to_string(out.path().join(&result.equivalences[0].report_file)).unwrap();
        assert_eq!(report, result.equivalences[0].render());
        assert!(report.contains("no admit"));
        // the transcript holds every sentence with EasyCrypt's answer
        let transcript = std::fs::read_to_string(&result.transcript).unwrap();
        assert!(transcript.lines().count() >= oracle.stats.closed);
        assert!(transcript.contains("\"sentence\":\"proc; inline.\""));
        // every sentence of the walk says which oracle and node it belongs to
        assert!(transcript.contains("\"ctx\":\"UsefulOracle N0 sampling-synchronized\""));
        for line in transcript.lines() {
            let v: serde_json::Value = serde_json::from_str(line).unwrap();
            assert!(v["response"]["version"] == "domino-json/1");
        }
    }

    #[test]
    fn the_walk_of_the_joint_tree_alone_closes_hello_world_too() {
        // rung 0 closes hello-world in one step: turn it off to see the tactics per node
        let Some((result, out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions {
                rung0: false,
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let oracle = &result.equivalences[0].oracles[0];
        assert!(oracle.stats.admits.is_empty(), "{}", result.render());
        assert_eq!(oracle.stats.fallbacks, 0);
        let text = proof_file(&result, out.path());
        // the router prelude, a synchronized sampling, a determined branch, the leaf
        for tactic in [
            "sp 1 1.",
            "if.",
            "seq 1 1 : (#pre /\\ rand{1} = rand{2}); 1: auto => />.",
            "rcondt{1} ^if; 1: auto => /#.",
            "auto => /> &1 &2 *; smt().",
        ] {
            assert!(text.contains(tactic), "missing `{tactic}` in\n{text}");
        }
        // no position from our listing: every `sp` count comes from EasyCrypt's JSON, and no
        // subgoal is picked by a number but the `1:` of a side goal
        assert!(!text.contains("swap"));
        assert!(compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &result.equivalences[0].proof_file
        )
        .is_ok());
    }

    /// A session on hello-world's `UsefulOracle` goal, and the theorem's names for it.
    fn hello_world_oracle_goal(out: &Path) -> (Session, crate::debug::lockstep::LockstepOutcome) {
        let dir = PathBuf::from("example-projects/hello-world");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        write_files(out, &exported.files).unwrap();
        let file = &exported.equivalences[0].proof_file;
        let mut session = Session::start(out).unwrap();
        let source = &exported.files[Path::new(file)];
        for sentence in sentences_until_call(file, source).unwrap() {
            ok_or_reject(session.send(&sentence).unwrap(), file, &sentence).unwrap();
        }
        // the base case, then the oracle's goal is in front
        let base = &split_sentences(source)[sentences_until_call(file, source).unwrap().len()];
        assert_eq!(
            session.send(base).unwrap().status,
            crate::easycrypt::json::Status::Ok
        );
        assert!(session.goals()[0].concl.kind == "equivF");
        let empty = crate::debug::lockstep::LockstepOutcome {
            tree: Default::default(),
            pairs: vec![],
            stuck: vec![],
            stop_reason: crate::debug::driver::StopReason::Completed,
        };
        (session, empty)
    }

    #[test]
    fn the_fallback_proves_an_oracle_without_the_joint_tree() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let out = tempfile::tempdir().unwrap();
        let (mut session, empty) = hello_world_oracle_goal(out.path());
        let tree = super::driver::OracleTree::new(&empty);
        let mut prover = super::driver::Prover {
            session: &mut session,
            script: Default::default(),
            tree: &tree,
            hints: &[],
            unfold_ops: &["inv".to_string(), "params_inv".to_string()],
            timeouts: Timeouts {
                general: Duration::from_secs(60),
                rung0: Duration::from_secs(2),
            },
            rung0: false,
            oracle: "UsefulOracle",
            leaf_budget: Duration::from_secs(60),
            deadline: None,
            stats: OracleStats::default(),
            live: None,
        };
        // an alignment mismatch sends the whole oracle down the fallback
        let mismatches = prover
            .oracle(|_| vec!["kind-differs at top level".to_string()])
            .unwrap();
        assert_eq!(mismatches.len(), 1);
        assert_eq!(prover.stats.fallbacks, 1);
        assert!(prover.stats.admits.is_empty(), "{:?}", prover.stats.admits);
        let script = prover.script.render();
        // the PDF's trial procedure: a decided condition, then the sampling, then the leaf
        assert!(script.contains("rcondt{1} ^if; 1: auto => /#."), "{script}");
        assert!(
            script.contains("seq 1 1 : (#pre /\\ rand{1} = rand{2}); 1: auto => /#."),
            "{script}"
        );
        assert_eq!(prover.script.admit_count(), 0);
        assert!(session.goals().is_empty(), "the oracle's goal is closed");
    }

    #[test]
    fn two_runs_on_an_unchanged_project_write_the_same_file() {
        let options = TacticsOptions {
            rung0: false,
            ..TacticsOptions::default()
        };
        let Some((a, out_a)) = run("example-projects/hello-world", "Proof", &options) else {
            return;
        };
        let (b, out_b) = run("example-projects/hello-world", "Proof", &options).unwrap();
        assert_eq!(proof_file(&a, out_a.path()), proof_file(&b, out_b.path()));
        // and the same final page, but for its timings (story 28)
        let page = |out: &tempfile::TempDir| {
            std::fs::read_to_string(out.path().join("progress/index.html")).unwrap()
        };
        let (page_a, page_b) = (page(&out_a), page(&out_b));
        assert!(page_a.contains("id=\"timings\""));
        assert_eq!(strip_timings(&page_a), strip_timings(&page_b));
    }

    /// Story 31: the capped transcript is smaller and the page cannot tell the difference.
    #[test]
    fn the_page_is_the_same_under_a_capped_and_a_full_transcript() {
        let with = |ec_transcript| TacticsOptions {
            rung0: false,
            ec_transcript,
            ..TacticsOptions::default()
        };
        let Some((capped, out_capped)) = run(
            "example-projects/hello-world",
            "Proof",
            &with(EcTranscriptMode::Capped),
        ) else {
            return;
        };
        let (full, out_full) =
            run("example-projects/hello-world", "Proof", &with(EcTranscriptMode::Full)).unwrap();
        let page = |out: &tempfile::TempDir| {
            strip_timings(&std::fs::read_to_string(out.path().join("progress/index.html")).unwrap())
        };
        assert_eq!(page(&out_capped), page(&out_full));
        let size = |t: &TheoremTactics| std::fs::metadata(&t.transcript).unwrap().len();
        assert!(size(&capped) < size(&full), "{} vs {}", size(&capped), size(&full));
        let text = std::fs::read_to_string(&capped.transcript).unwrap();
        assert!(text.contains("\"goals_dropped\":"));
        assert!(!std::fs::read_to_string(&full.transcript).unwrap().contains("\"goals_dropped\":"));
    }

    #[test]
    fn the_live_page_shows_the_oracle_its_goals_and_ends_without_a_refresh_tag() {
        let Some((result, out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions {
                rung0: false,
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let page = std::fs::read_to_string(out.path().join("progress/index.html")).unwrap();
        assert!(!page.contains("http-equiv"), "the final page does not refresh");
        assert!(page.contains("tactics (done)"));
        assert!(page.contains("UsefulOracle") && page.contains("router prelude"));
        // the goals of the walk, with their sentences, and the lockstep page they belong to
        assert!(page.contains("sp 1 1."));
        assert!(page.contains("proc; inline."));
        assert!(page.contains("lockstep page of this oracle"));
        assert!(page.contains("/easycrypt/index.html#n=") || page.contains("index.html#n="));
        assert!(page.contains("0 admit(s)"), "the summary counts admits");
        // the last step of a goal has its goal text embedded, straight from EasyCrypt
        assert!(page.contains("Type variables"), "goal text is embedded");
        let _ = result;
    }

    #[test]
    fn an_oracle_that_was_not_asked_for_keeps_its_admit() {
        let Some((result, out)) = run(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            &TacticsOptions {
                oracle: Some("PKGEN".into()),
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let text = proof_file(&result, out.path());
        // only PKGEN got tactics; PKENC and PKDEC keep `+ proc; inline. admit.`
        assert_eq!(text.matches("+ proc; inline. admit.").count(), 2, "{text}");
        assert_eq!(result.equivalences[0].oracles.len(), 1);
        // the report's counts are the labelled admits of the file
        let labelled = labelled_admits(&text);
        assert_eq!(labelled.len(), result.admit_count(), "{}", result.render());
    }
}
