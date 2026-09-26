// SPDX-License-Identifier: MIT OR Apache-2.0

use super::driver::{pair_view, Part};
use super::*;
use crate::debug::driver::{ClaimVerdict, TerminalView, Verdict};
use crate::debug::lockstep::{PairRecord, PairSide, RelationVerdict, EQUAL_OUTPUT};

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
        claims: vec![
            ClaimVerdict {
                claim: EQUAL_OUTPUT.into(),
                verdict: equal_output,
                relations: Vec::new(),
            },
            ClaimVerdict {
                claim: "invariant".into(),
                verdict: invariant,
                relations: relations
                    .iter()
                    .map(|(name, verdict)| RelationVerdict {
                        name: name.to_string(),
                        verdict: verdict.clone(),
                    })
                    .collect(),
            },
        ],
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
        Verdict::pair_infeasible(),
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
        node_scripts: vec![],
        resumed: false,
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
        interrupted: None,
        transcript: PathBuf::from("progress/Eq_A_B/ec-transcript.jsonl"),
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

#[test]
fn the_admits_of_a_seal_have_their_own_reason_in_the_report() {
    assert_eq!(AdmitReason::ALL.last(), Some(&AdmitReason::Interrupted));
    assert_eq!(AdmitReason::Interrupted.slug(), "interrupted");
    let sealed = Admit {
        reason: AdmitReason::Interrupted,
        id: "N3".into(),
        claim: "open-goal".into(),
        domino: DominoView::NotApplicable,
        goal: String::new(),
    };
    assert_eq!(
        sealed.label(),
        "(* domino: N3 open-goal; reason: interrupted; Domino: n/a *)"
    );
    let o = oracle_with(vec![
        admit(AdmitReason::Stuck, "S1"),
        sealed.clone(),
        sealed,
    ]);
    let eq = EquivalenceTactics {
        proofstep: 0,
        proof_file: "Eq_A_B.ec".into(),
        left: "A".into(),
        right: "B".into(),
        oracles: vec![o],
        base_case_admitted: false,
        elapsed: Duration::from_secs(4),
        report_file: "Eq_A_B.report.txt".into(),
        interrupted: None,
        transcript: PathBuf::from("progress/Eq_A_B/ec-transcript.jsonl"),
    };
    let report = eq.render();
    assert!(
        report.contains("3 admits (stuck 1, interrupted 2)"),
        "{report}"
    );
    assert!(
        report.contains("admit N3 open-goal [interrupted] Domino: n/a"),
        "{report}"
    );
}

#[test]
fn an_interrupted_report_names_what_was_sealed() {
    let sealed = |oracle: &str| Interrupted::Sealed {
        oracle: oracle.into(),
        admits: 5,
        node: "N4".into(),
    };
    assert_eq!(
        sealed("PKENC").to_string(),
        "sealed PKENC with 5 admits at node N4"
    );
    assert_eq!(
        Interrupted::Lockstep {
            oracle: "PKDEC".into()
        }
        .to_string(),
        "during lockstep execution of PKDEC, nothing sealed"
    );
    let mut eq = EquivalenceTactics {
        proofstep: 0,
        proof_file: "Eq_A_B.ec".into(),
        left: "A".into(),
        right: "B".into(),
        oracles: vec![oracle_with(vec![])],
        base_case_admitted: false,
        elapsed: Duration::from_secs(4),
        report_file: "Eq_A_B.report.txt".into(),
        interrupted: None,
        transcript: PathBuf::from("progress/Eq_A_B/ec-transcript.jsonl"),
    };
    assert!(!eq.render().contains("interrupted"));
    eq.interrupted = Some(sealed("PKENC"));
    let report = eq.render();
    assert!(
        report.contains("\ninterrupted: sealed PKENC with 5 admits at node N4\n"),
        "{report}"
    );
    let theorem = TheoremTactics {
        theorem: "T".into(),
        equivalences: vec![eq],
        elapsed: Duration::from_secs(4),
    };
    assert_eq!(theorem.interrupted(), Some(&sealed("PKENC")));
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

// ----------------------------------------------------------------------
// Story 37: what a proof job does with a session record
// ----------------------------------------------------------------------

fn eq_report() -> EquivalenceReport {
    EquivalenceReport {
        proofstep: 0,
        left_name: "L".into(),
        right_name: "R".into(),
        invariants_file: "Invariants.ec".into(),
        proof_file: "Eq_L_R.ec".into(),
        oracle_count: 3,
        admit_count: 0,
        oracle_set_mismatch: None,
    }
}

fn done(name: &str) -> OracleRecord {
    let mut o = OracleRecord::new(name, OracleStatus::Done);
    o.script = Some(format!("+ proc; inline.\n  auto. (* {name} *)\n"));
    o
}

/// Writes a record of oracles A (done), B (interrupted), C (pending) and plans a job on it.
fn plan_of(oracles: Vec<OracleRecord>, options: &TacticsOptions) -> (JobPlan, tempfile::TempDir) {
    let out = tempfile::tempdir().unwrap();
    let record = SessionRecord::new("T", "L", "R", oracles);
    std::fs::write(out.path().join("Eq_L_R.session.json"), record.to_json()).unwrap();
    let plan = plan_job(&eq_report(), out.path(), options).unwrap();
    (plan, out)
}

fn partial() -> Vec<OracleRecord> {
    vec![
        done("A"),
        OracleRecord::new("B", OracleStatus::Interrupted),
        OracleRecord::new("C", OracleStatus::Pending),
    ]
}

fn oracle_option(name: &str, force: bool) -> TacticsOptions {
    TacticsOptions {
        oracle: Some(name.into()),
        force,
        ..TacticsOptions::default()
    }
}

fn prior(plan: JobPlan) -> Option<SessionRecord> {
    match plan {
        JobPlan::Prove { prior } => prior,
        JobPlan::Skip => panic!("expected a job that proves"),
    }
}

#[test]
fn without_a_record_a_job_proves_everything() {
    let out = tempfile::tempdir().unwrap();
    let plan = plan_job(&eq_report(), out.path(), &TacticsOptions::default()).unwrap();
    assert!(prior(plan).is_none());
}

#[test]
fn a_partial_record_is_resumed_with_its_entries() {
    let (plan, _out) = plan_of(partial(), &TacticsOptions::default());
    let record = prior(plan).expect("resumed");
    assert_eq!(record.oracles.len(), 3);
    assert!(OracleTactics::from_record(record.oracle("A").unwrap()).unwrap().resumed);
    assert!(OracleTactics::from_record(record.oracle("B").unwrap()).is_none());
}

#[test]
fn a_complete_record_skips_and_force_proves_from_scratch_and_deletes_it() {
    let all = vec![done("A"), done("B"), done("C")];
    let (skipped, _out) = plan_of(all.clone(), &TacticsOptions::default());
    assert!(matches!(skipped, JobPlan::Skip));
    let forced = TacticsOptions {
        force: true,
        ..TacticsOptions::default()
    };
    let (plan, out) = plan_of(all, &forced);
    assert!(prior(plan).is_none());
    assert!(!out.path().join("Eq_L_R.session.json").exists());
}

#[test]
fn force_discards_a_partial_record_too() {
    let forced = TacticsOptions {
        force: true,
        ..TacticsOptions::default()
    };
    let (plan, _out) = plan_of(partial(), &forced);
    assert!(prior(plan).is_none());
}

#[test]
fn an_oracle_that_is_done_is_skipped_and_one_that_is_not_is_proved() {
    let (skipped, _out) = plan_of(partial(), &oracle_option("A", false));
    assert!(matches!(skipped, JobPlan::Skip));
    let (plan, _out) = plan_of(partial(), &oracle_option("B", false));
    let record = prior(plan).expect("the others keep their entries");
    assert!(record.oracle("A").unwrap().is_resumable());
    // a complete record with `--oracle O` skips as well
    let all = vec![done("A"), done("B"), done("C")];
    let (skipped, _out) = plan_of(all, &oracle_option("C", false));
    assert!(matches!(skipped, JobPlan::Skip));
}

#[test]
fn force_with_an_oracle_reproves_that_oracle_alone_and_keeps_the_rest() {
    let all = vec![done("A"), done("B"), done("C")];
    let (plan, out) = plan_of(all, &oracle_option("B", true));
    let record = prior(plan).expect("kept");
    assert_eq!(record.oracle("B").unwrap().status, OracleStatus::Pending);
    assert!(record.oracle("A").unwrap().is_resumable());
    assert!(record.oracle("C").unwrap().is_resumable());
    assert!(!record.complete);
    // the record on disk stays until the job's first checkpoint replaces it
    assert!(out.path().join("Eq_L_R.session.json").exists());
}

#[test]
fn a_version_1_record_cannot_be_resumed_from() {
    let out = tempfile::tempdir().unwrap();
    std::fs::write(
        out.path().join("Eq_L_R.session.json"),
        r#"{"version": 1, "theorem": "T", "left": "L", "right": "R", "complete": false,
            "oracles": [{"name": "A", "status": "done"}, {"name": "B", "status": "pending"}]}"#,
    )
    .unwrap();
    let plan = plan_job(&eq_report(), out.path(), &TacticsOptions::default()).unwrap();
    let record = prior(plan).expect("read");
    assert_eq!(record.version, 1);
    assert!(OracleTactics::from_record(record.oracle("A").unwrap()).is_none());
    // a done oracle without a script is not skipped by `--oracle` either: it is proved again
    let plan = plan_job(&eq_report(), out.path(), &oracle_option("A", false)).unwrap();
    assert!(prior(plan).is_some());
}

#[test]
fn a_resumed_oracle_reads_back_its_admits_and_lockstep() {
    let mut record = done("A");
    record.admits = vec![AdmitRecord {
        node: "N7".into(),
        reason: "stuck".into(),
        claim: "invariant".into(),
        domino: "inconclusive".into(),
    }];
    record.lockstep = Some(LockstepRecord {
        joint_paths: 23,
        ms: 41200,
    });
    let o = OracleTactics::from_record(&record).unwrap();
    assert!(o.resumed);
    assert_eq!(o.admits_by_reason(), vec![(AdmitReason::Stuck, 1)]);
    assert_eq!(o.joint_paths, 23);
    assert_eq!(o.lockstep_time, Duration::from_millis(41200));
    assert_eq!(o.to_record().admits, record.admits);
    assert_eq!(o.to_record().script, record.script);
    // a reason this version does not know: not resumable, so proved again
    record.admits[0].reason = "from-the-future".into();
    assert!(OracleTactics::from_record(&record).is_none());
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

    /// The most `easycrypt compile` of one written file may take.
    const COMPILE_TIMEOUT: Duration = Duration::from_secs(30 * 60);

    /// `easycrypt compile -I <dir> <file>`; `Err` carries the tail of its output. Only tests
    /// compile: a tactics run never does (ADR 0005).
    fn compile(binary: &Path, dir: &Path, file: &str) -> Result<(), String> {
        use std::process::Command;
        let stderr = tempfile::tempfile().map_err(|e| e.to_string())?;
        let mut child = Command::new(binary)
            .args(["compile", "-I"])
            .arg(dir)
            .arg(file)
            .current_dir(dir)
            .stdout(std::process::Stdio::null())
            .stderr(stderr.try_clone().map_err(|e| e.to_string())?)
            .spawn()
            .map_err(|e| e.to_string())?;
        let began = Instant::now();
        let status = loop {
            match child.try_wait().map_err(|e| e.to_string())? {
                Some(status) => break status,
                None if began.elapsed() > COMPILE_TIMEOUT => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!("timed out after {}s", COMPILE_TIMEOUT.as_secs()));
                }
                None => std::thread::sleep(Duration::from_millis(200)),
            }
        };
        if status.success() {
            return Ok(());
        }
        use std::io::{Read, Seek};
        let mut text = String::new();
        let mut stderr = stderr;
        let _ = stderr.rewind();
        let _ = stderr.read_to_string(&mut text);
        let tail: Vec<&str> = text.lines().rev().take(8).collect();
        Err(tail.into_iter().rev().collect::<Vec<_>>().join("\n"))
    }

    fn run(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
    ) -> Option<(TheoremTactics, tempfile::TempDir)> {
        run_captured(dir, theorem, options).map(|(result, out, _)| (result, out))
    }

    /// The proof file and its report as they were on disk when the run reported an event.
    #[derive(Debug, Clone)]
    struct Capture {
        /// `item 2` (an oracle started), `goal N3` (a joint node's goal done), `finished`.
        event: String,
        ec: String,
        report: Option<String>,
    }

    /// Reads the first equivalence's proof file and report at every tactics event: what a
    /// reader of the files sees while the run goes on.
    struct Capturing {
        ec: PathBuf,
        report: PathBuf,
        captures: std::rc::Rc<std::cell::RefCell<Vec<Capture>>>,
        /// Sets the flag at the first event whose name starts so, as a Ctrl-C would (story 34).
        stop_at: Option<(String, Arc<AtomicBool>)>,
    }

    impl ExportObserver for Capturing {
        fn on_event(&mut self, event: &crate::writers::easycrypt::progress::ExportEvent<'_>) {
            use crate::writers::easycrypt::progress::ExportEvent;
            let event = match event {
                ExportEvent::ItemStarted { index, .. } => format!("item {index}"),
                ExportEvent::GoalFinished { goal, .. } => format!("goal {goal}"),
                ExportEvent::PhaseFinished { .. } => "finished".to_string(),
                _ => return,
            };
            if let Some((at, stop)) = &self.stop_at {
                if event.starts_with(at.as_str()) {
                    stop.store(true, Ordering::Relaxed);
                }
            }
            self.captures.borrow_mut().push(Capture {
                event,
                ec: std::fs::read_to_string(&self.ec).unwrap(),
                report: std::fs::read_to_string(&self.report).ok(),
            });
        }
    }

    /// [`run`], capturing the first equivalence's files at every event.
    fn run_captured(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
    ) -> Option<(TheoremTactics, tempfile::TempDir, Vec<Capture>)> {
        run_stopped_at(dir, theorem, options, None)
    }

    /// [`run_captured`], and the run is asked to stop at the first event whose name starts with
    /// `stop_at`.
    fn run_stopped_at(
        dir: &str,
        theorem: &str,
        options: &TacticsOptions,
        stop_at: Option<&str>,
    ) -> Option<(TheoremTactics, tempfile::TempDir, Vec<Capture>)> {
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
        let proof_file = &exported.equivalences[0].proof_file;
        let captures = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let mut observer: Option<Box<dyn ExportObserver>> = Some(Box::new(Capturing {
            ec: out.path().join(proof_file),
            report: out
                .path()
                .join(proof_file.trim_end_matches(".ec").to_string() + ".report.txt"),
            captures: captures.clone(),
            stop_at: stop_at.map(|at| {
                let stop = options.stop.clone().expect("a run to stop has a stop flag");
                (at.to_string(), stop)
            }),
        }));
        let result = run_tactics_observed(
            theorem,
            &project,
            &exported,
            out.path(),
            &Cvc5LibBackend::new(true, None),
            options,
            &mut || {
                observer
                    .take()
                    .unwrap_or_else(|| Box::new(NopExportObserver))
            },
        )
        .unwrap();
        let captures = captures.borrow().clone();
        Some((result, out, captures))
    }

    /// The live page of the first equivalence: beside its transcript (story 36).
    fn page_path(result: &TheoremTactics) -> PathBuf {
        result.equivalences[0]
            .transcript
            .with_file_name("index.html")
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
        let transcript = std::fs::read_to_string(&result.equivalences[0].transcript).unwrap();
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
            checkpoint: None,
            node: None,
            mismatches: vec![],
            stopped: None,
        };
        // an alignment mismatch sends the whole oracle down the fallback
        prover
            .oracle(|_| vec!["kind-differs at top level".to_string()])
            .unwrap();
        assert_eq!(prover.mismatches.len(), 1);
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
        let page = |t: &TheoremTactics| std::fs::read_to_string(page_path(t)).unwrap();
        let (page_a, page_b) = (page(&a), page(&b));
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
        let Some((capped, _out_capped)) = run(
            "example-projects/hello-world",
            "Proof",
            &with(EcTranscriptMode::Capped),
        ) else {
            return;
        };
        let (full, _out_full) = run(
            "example-projects/hello-world",
            "Proof",
            &with(EcTranscriptMode::Full),
        )
        .unwrap();
        let page =
            |t: &TheoremTactics| strip_timings(&std::fs::read_to_string(page_path(t)).unwrap());
        assert_eq!(page(&capped), page(&full));
        let size = |t: &TheoremTactics| {
            std::fs::metadata(&t.equivalences[0].transcript)
                .unwrap()
                .len()
        };
        assert!(
            size(&capped) < size(&full),
            "{} vs {}",
            size(&capped),
            size(&full)
        );
        let text = std::fs::read_to_string(&capped.equivalences[0].transcript).unwrap();
        assert!(text.contains("\"goals_dropped\":"));
        assert!(!std::fs::read_to_string(&full.equivalences[0].transcript)
            .unwrap()
            .contains("\"goals_dropped\":"));
    }

    #[test]
    fn the_live_page_shows_the_oracle_its_goals_and_ends_without_a_refresh_tag() {
        let Some((result, _out)) = run(
            "example-projects/hello-world",
            "Proof",
            &TacticsOptions {
                rung0: false,
                ..TacticsOptions::default()
            },
        ) else {
            return;
        };
        let page = std::fs::read_to_string(page_path(&result)).unwrap();
        assert!(
            !page.contains("http-equiv"),
            "the final page does not refresh"
        );
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
    // ------------------------------------------------------------------
    // Story 33: the file on disk is what is proved
    // ------------------------------------------------------------------

    /// Two oracles, one with a `domino-fails` admit; a few seconds.
    const TWO_ORACLES: &str = "example-projects/hello-world-oracle-rename-new";

    fn walk(write_granularity: WriteGranularity) -> TacticsOptions {
        TacticsOptions {
            rung0: false,
            write_granularity,
            ..TacticsOptions::default()
        }
    }

    const UNTOUCHED: &str = "+ proc; inline. admit.";

    /// `admit.` sentences of a proof file (outside comments).
    fn admit_sentences(text: &str) -> usize {
        text.lines()
            .filter(|l| {
                let code = l.split("(*").next().unwrap_or("");
                code.split(|c: char| c.is_whitespace() || c == ';')
                    .any(|w| w == "admit.")
            })
            .count()
    }

    /// The report's total of admits, and of those labelled `interrupted`.
    fn report_admits(report: &str) -> (usize, usize) {
        let total_line = report
            .lines()
            .find(|l| l.contains(" oracles, "))
            .expect("the report's last line");
        let total = total_line
            .split(", ")
            .find_map(|part| part.strip_suffix(" admits"))
            .expect("an admit count")
            .parse()
            .unwrap();
        let interrupted = report
            .lines()
            .filter_map(|l| l.split("interrupted ").nth(1))
            .filter_map(|n| n.split([',', ')']).next()?.parse::<usize>().ok())
            .sum();
        (total, interrupted)
    }

    fn sentences(transcript: &Path) -> Vec<String> {
        std::fs::read_to_string(transcript)
            .unwrap()
            .lines()
            .map(|line| {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                v["sentence"].as_str().unwrap().to_string()
            })
            .collect()
    }

    #[test]
    fn each_oracle_is_on_disk_as_soon_as_it_is_proved() {
        let Some((result, _out, captures)) =
            run_captured(TWO_ORACLES, "Proof", &walk(WriteGranularity::Oracle))
        else {
            return;
        };
        let oracles = &result.equivalences[0].oracles;
        assert_eq!(oracles.len(), 2);
        let second_started = captures
            .iter()
            .position(|c| c.event == "item 2")
            .expect("the second oracle started");
        // while the first oracle runs, nothing is written: no node writes at this granularity
        for c in &captures[..second_started] {
            assert_eq!(c.ec.matches(UNTOUCHED).count(), 2, "{}: {}", c.event, c.ec);
            assert!(c.report.is_none(), "{}", c.event);
        }
        // between the oracles: the first one's script is on disk, and its report with it
        let between = &captures[second_started];
        let written: Vec<&OracleTactics> = oracles
            .iter()
            .filter(|o| between.ec.contains(o.script.trim_end()))
            .collect();
        assert_eq!(written.len(), 1, "{}", between.ec);
        assert_eq!(between.ec.matches(UNTOUCHED).count(), 1, "{}", between.ec);
        let report = between
            .report
            .as_deref()
            .expect("a report next to the file");
        let other = oracles
            .iter()
            .find(|o| o.oracle != written[0].oracle)
            .unwrap();
        assert!(
            report.contains(&format!("  {}: lockstep", written[0].oracle)),
            "{report}"
        );
        assert!(!report.contains(&other.oracle), "{report}");
        assert_eq!(report_admits(report).0, labelled_admits(&between.ec).len());
        assert!(!between.ec.contains("interrupted"));
    }

    #[test]
    fn at_node_granularity_every_write_is_a_complete_sealed_proof_and_its_report() {
        let Some((result, out, captures)) =
            run_captured(TWO_ORACLES, "Proof", &walk(WriteGranularity::Node))
        else {
            return;
        };
        let file = &result.equivalences[0].proof_file;
        let mid_oracle: Vec<&Capture> = captures
            .iter()
            .filter(|c| c.event.starts_with("goal "))
            .collect();
        assert!(mid_oracle.len() >= 4, "{captures:?}");
        let mut sealed = Vec::new();
        for c in &mid_oracle {
            // the full bullet structure: both oracle bullets, then `qed.`
            let progress = crate::writers::easycrypt::overwrite::proof_progress(&c.ec);
            assert_eq!(progress.total, 2, "{}: {}", c.event, c.ec);
            assert!(c.ec.contains("\nqed."));
            // every admit is labelled, but an untouched oracle's
            let labelled = labelled_admits(&c.ec);
            assert_eq!(
                admit_sentences(&c.ec),
                labelled.len() + c.ec.matches(UNTOUCHED).count(),
                "{}: {}",
                c.event,
                c.ec
            );
            // the report next to it describes it, the interrupted admits too
            let report = c.report.as_deref().expect("a report with every write");
            let interrupted = labelled.iter().filter(|r| *r == "interrupted").count();
            assert_eq!(
                report_admits(report),
                (labelled.len(), interrupted),
                "{}: {report}\n{}",
                c.event,
                c.ec
            );
            if interrupted > 0 {
                sealed.push(c.ec.clone());
            }
        }
        assert!(!sealed.is_empty(), "some write sealed an oracle part way");
        // a sealed file compiles (the test compiles, never the run: ADR 0005)
        let binary = crate::easycrypt::session::locate_binary();
        for text in [sealed.first().unwrap(), sealed.last().unwrap()] {
            std::fs::write(out.path().join(file), text).unwrap();
            if let Err(e) = compile(&binary, out.path(), file) {
                panic!("a sealed file does not compile: {e}\n{text}");
            }
        }
    }

    #[test]
    fn sealing_sends_nothing_and_the_final_file_does_not_depend_on_the_granularity() {
        let Some((by_oracle, out_oracle)) =
            run(TWO_ORACLES, "Proof", &walk(WriteGranularity::Oracle))
        else {
            return;
        };
        let (by_node, out_node) = run(TWO_ORACLES, "Proof", &walk(WriteGranularity::Node)).unwrap();
        // the same sentences, in the same order: no `admit.` and no `undo` of a seal
        assert_eq!(
            sentences(&by_oracle.equivalences[0].transcript),
            sentences(&by_node.equivalences[0].transcript)
        );
        let final_file = proof_file(&by_node, out_node.path());
        assert_eq!(proof_file(&by_oracle, out_oracle.path()), final_file);
        assert!(!final_file.contains("interrupted"), "{final_file}");
        // nothing a run writes is left behind but in its `progress/Eq_<L>_<R>/`, and the lock
        // is gone (story 36)
        let names: Vec<String> =
            std::fs::read_dir(by_node.equivalences[0].transcript.parent().unwrap())
                .unwrap()
                .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
                .collect();
        assert!(
            !names.iter().any(|n| n.ends_with(".tmp") || n == "lock"),
            "{names:?}"
        );
        assert!(
            names.contains(&"index.html".to_string())
                && names.contains(&"ec-transcript.jsonl".to_string())
        );
    }

    // ------------------------------------------------------------------
    // Story 34: Ctrl-C stops a tactics run and leaves a partial proof
    // ------------------------------------------------------------------

    fn stoppable(write_granularity: WriteGranularity) -> TacticsOptions {
        TacticsOptions {
            stop: Some(Arc::new(AtomicBool::new(false))),
            ..walk(write_granularity)
        }
    }

    #[test]
    fn a_stop_in_the_walk_seals_the_oracle_where_it_stands_and_the_file_compiles() {
        // the first joint node of the first oracle is done: the walk stops at its next sentence
        let Some((result, out, captures)) = run_stopped_at(
            TWO_ORACLES,
            "Proof",
            &stoppable(WriteGranularity::Oracle),
            Some("goal N"),
        ) else {
            return;
        };
        assert!(
            captures.iter().any(|c| c.event.starts_with("goal N")),
            "{captures:?}"
        );
        let eq = &result.equivalences[0];
        let Some(Interrupted::Sealed {
            oracle,
            admits,
            node,
        }) = &eq.interrupted
        else {
            panic!("sealed: {:?}\n{}", eq.interrupted, eq.render());
        };
        assert_eq!(result.interrupted(), eq.interrupted.as_ref());
        // the oracle in flight is the only one in the report; the other is not reached
        assert_eq!(eq.oracles.len(), 1);
        assert_eq!(&eq.oracles[0].oracle, oracle);
        let text = proof_file(&result, out.path());
        assert_eq!(text.matches(UNTOUCHED).count(), 1, "{text}");
        // its open goals are admitted `interrupted`, at the node the walk was in
        let labelled = labelled_admits(&text);
        let interrupted = labelled.iter().filter(|r| *r == "interrupted").count();
        assert!(*admits > 0 && interrupted == *admits, "{text}");
        assert!(
            text.contains(&format!("admit. (* domino: {node} open-goal; reason: interrupted")),
            "{text}"
        );
        // the report names what was sealed, and its admit counts are the file's
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert_eq!(report, eq.render());
        assert!(
            report.contains(&format!(
                "interrupted: sealed {oracle} with {admits} admits at node {node}"
            )),
            "{report}"
        );
        assert_eq!(report_admits(&report), (labelled.len(), interrupted));
        // the page says interrupted, not failed
        let page = std::fs::read_to_string(page_path(&result)).unwrap();
        assert!(page.contains("tactics (interrupted)"));
        assert!(!page.contains("http-equiv"));
        // and the partial proof compiles
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the partial proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn a_stop_during_lockstep_execution_keeps_the_earlier_oracles_work() {
        // the second oracle has started: its lockstep execution sees the stop
        let Some((result, out, _)) = run_stopped_at(
            TWO_ORACLES,
            "Proof",
            &stoppable(WriteGranularity::Oracle),
            Some("item 2"),
        ) else {
            return;
        };
        let eq = &result.equivalences[0];
        let [first] = eq.oracles.as_slice() else {
            panic!("one oracle finished: {}", eq.render());
        };
        let Some(Interrupted::Lockstep { oracle }) = &eq.interrupted else {
            panic!("stopped in lockstep execution: {:?}", eq.interrupted);
        };
        assert_ne!(oracle, &first.oracle);
        // the finished oracle keeps its script, the stopped one its unlabelled admit
        let text = proof_file(&result, out.path());
        assert!(text.contains(first.script.trim_end()), "{text}");
        assert_eq!(text.matches(UNTOUCHED).count(), 1, "{text}");
        assert!(!text.contains("interrupted"), "{text}");
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains(&format!(
                "interrupted: during lockstep execution of {oracle}, nothing sealed"
            )),
            "{report}"
        );
        // nothing was sent for the stopped oracle: one `proc; inline.` after the `call`
        let sent = sentences(&result.equivalences[0].transcript);
        let call = sent.iter().position(|s| s.starts_with("call (")).unwrap();
        assert_eq!(
            sent[call..].iter().filter(|s| *s == "proc; inline.").count(),
            1,
            "{sent:?}"
        );
    }

    // ------------------------------------------------------------------
    // Story 37: a session record lets a proof job resume an equivalence
    // ------------------------------------------------------------------

    /// Another proof job on the export in `out`, as `prove` starts one.
    fn run_again(out: &Path, options: &TacticsOptions) -> TheoremTactics {
        let dir = PathBuf::from(TWO_ORACLES);
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        run_tactics_observed(
            theorem,
            &project,
            &exported,
            out,
            &Cvc5LibBackend::new(true, None),
            options,
            &mut || Box::new(NopExportObserver),
        )
        .unwrap()
    }

    fn record_path(result: &TheoremTactics, out: &Path) -> PathBuf {
        let file = &result.equivalences[0].proof_file;
        out.join(session_record_name(file))
    }

    fn read_record(path: &Path) -> SessionRecord {
        SessionRecord::read(path).unwrap().expect("a record")
    }

    /// The first oracle proved, the second stopped in lockstep execution, as by Ctrl-C.
    fn stopped_after_the_first_oracle() -> Option<(TheoremTactics, tempfile::TempDir)> {
        let (result, out, _) = run_stopped_at(
            TWO_ORACLES,
            "Proof",
            &stoppable(WriteGranularity::Oracle),
            Some("item 2"),
        )?;
        Some((result, out))
    }

    #[test]
    fn a_resumed_job_does_not_walk_the_oracles_the_record_holds() {
        let Some((first_run, out)) = stopped_after_the_first_oracle() else {
            return;
        };
        let stopped = &first_run.equivalences[0];
        let first = stopped.oracles[0].clone();
        let path = record_path(&first_run, out.path());
        let record = read_record(&path);
        assert!(!record.complete);
        assert_eq!(record.done(), 1);
        let entry = record.oracle(&first.oracle).unwrap();
        assert_eq!(entry.script.as_deref(), Some(first.script.as_str()));
        assert!(!entry.nodes.is_empty());
        assert_eq!(entry.lockstep.unwrap().joint_paths, first.joint_paths);
        let before = proof_file(&first_run, out.path());

        let result = run_again(out.path(), &walk(WriteGranularity::Oracle));
        let eq = &result.equivalences[0];
        assert!(eq.interrupted.is_none());
        let [a, b] = eq.oracles.as_slice() else {
            panic!("two oracles: {}", eq.render());
        };
        let (resumed, proved) = if a.oracle == first.oracle { (a, b) } else { (b, a) };
        assert!(resumed.resumed && !proved.resumed, "{}", eq.render());
        assert_eq!(resumed.script, first.script);
        assert_eq!(resumed.admits_by_reason().len(), first.admits_by_reason().len());
        // not walked: one `proc; inline.` after the call (the other oracle's), the resumed
        // oracle's goal only got `admit.`
        let sent = sentences(&eq.transcript);
        let call = sent.iter().position(|s| s.starts_with("call (")).unwrap();
        assert_eq!(
            sent[call..].iter().filter(|s| *s == "proc; inline.").count(),
            1,
            "{sent:?}"
        );
        // the file holds the first script byte for byte, and is complete now
        let text = proof_file(&result, out.path());
        assert!(before.contains(first.script.trim_end()));
        assert!(text.contains(first.script.trim_end()), "{text}");
        assert!(text.contains(proved.script.trim_end()), "{text}");
        assert_eq!(text.matches(UNTOUCHED).count(), 0, "{text}");
        // the report and the page say which oracle is not this run's
        let report = std::fs::read_to_string(out.path().join(&eq.report_file)).unwrap();
        assert!(
            report.contains(&format!("  {}: resumed from session record", first.oracle)),
            "{report}"
        );
        assert!(!report.contains(&format!("  {}: resumed", proved.oracle)), "{report}");
        let page = std::fs::read_to_string(page_path(&result)).unwrap();
        assert!(page.contains("resumed from session record"));
        // the record is complete and still holds both scripts
        let record = read_record(&path);
        assert!(record.complete);
        assert!(record.oracles.iter().all(OracleRecord::is_resumable));
        assert_eq!(
            record.oracle(&first.oracle).unwrap().script.as_deref(),
            Some(first.script.as_str())
        );
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the resumed proof does not compile: {e}\n{text}");
        }

        // complete: skipped, and nothing changes
        let again = run_again(out.path(), &walk(WriteGranularity::Oracle));
        assert!(again.equivalences.is_empty());
        assert_eq!(proof_file(&result, out.path()), text);
        // --oracle O --force: only O is proved again, the other comes from the record
        let only = TacticsOptions {
            oracle: Some(proved.oracle.clone()),
            force: true,
            ..walk(WriteGranularity::Oracle)
        };
        let again = run_again(out.path(), &only);
        let eq = &again.equivalences[0];
        assert_eq!(eq.oracles.len(), 2, "{}", eq.render());
        for o in &eq.oracles {
            assert_eq!(o.resumed, o.oracle == first.oracle, "{}", eq.render());
        }
        assert_eq!(proof_file(&again, out.path()), text);
        assert!(read_record(&path).complete);
        // --force: from scratch, nothing resumed
        let forced = TacticsOptions {
            force: true,
            ..walk(WriteGranularity::Oracle)
        };
        let again = run_again(out.path(), &forced);
        assert!(again.equivalences[0].oracles.iter().all(|o| !o.resumed));
        assert_eq!(proof_file(&again, out.path()), text);
    }

    #[test]
    fn a_file_written_without_its_record_is_proved_again_from_the_skeleton() {
        // a kill between the file's write and the record's leaves the file ahead of the record
        let Some((first_run, out)) = stopped_after_the_first_oracle() else {
            return;
        };
        std::fs::remove_file(record_path(&first_run, out.path())).unwrap();
        assert_eq!(proof_file(&first_run, out.path()).matches(UNTOUCHED).count(), 1);
        let result = run_again(out.path(), &walk(WriteGranularity::Oracle));
        let eq = &result.equivalences[0];
        assert!(eq.oracles.iter().all(|o| !o.resumed));
        let text = proof_file(&result, out.path());
        assert_eq!(text.matches(UNTOUCHED).count(), 0, "{text}");
        assert!(read_record(&record_path(&result, out.path())).complete);
        if let Err(e) = compile(
            &crate::easycrypt::session::locate_binary(),
            out.path(),
            &eq.proof_file,
        ) {
            panic!("the proof does not compile: {e}\n{text}");
        }
    }

    #[test]
    fn a_version_1_record_re_proves_its_done_oracles() {
        let Some((first_run, out)) = stopped_after_the_first_oracle() else {
            return;
        };
        let path = record_path(&first_run, out.path());
        let record = read_record(&path);
        let statuses: Vec<String> = record
            .oracles
            .iter()
            .map(|o| format!(r#"{{"name": "{}", "status": "{:?}"}}"#, o.name, o.status).to_lowercase())
            .collect();
        std::fs::write(
            &path,
            format!(
                r#"{{"version": 1, "theorem": "Proof", "left": "{}", "right": "{}", "complete": false, "oracles": [{}]}}"#,
                record.left,
                record.right,
                statuses.join(",")
            ),
        )
        .unwrap();
        let result = run_again(out.path(), &walk(WriteGranularity::Oracle));
        let eq = &result.equivalences[0];
        assert_eq!(eq.oracles.len(), 2);
        assert!(eq.oracles.iter().all(|o| !o.resumed), "{}", eq.render());
        let record = read_record(&path);
        assert_eq!(record.version, 2);
        assert!(record.complete);
    }
}
