// SPDX-License-Identifier: MIT OR Apache-2.0

use std::io::Write;
use std::time::Duration;

use super::*;
use crate::easycrypt::json::parse_response;
use crate::writers::easycrypt::progress::NopExportObserver;

/// A live model over a temporary directory, fed hand-made session events.
struct Rig {
    dir: tempfile::TempDir,
    live: LiveHandle,
    observer: Box<dyn FnMut(&SessionEvent<'_>)>,
    transcript: std::fs::File,
    state: u64,
}

impl Rig {
    fn new() -> Rig {
        let dir = tempfile::tempdir().unwrap();
        let transcript_path = dir.path().join("ec-transcript.jsonl");
        let transcript = std::fs::File::create(&transcript_path).unwrap();
        let live = LiveHandle::new(LiveConfig {
            theorem: "T".into(),
            page: Some(dir.path().join("index.html")),
            transcript: transcript_path,
            phases: vec![("types", 2), ("write", 5)],
            progress: Box::new(NopExportObserver),
        });
        live.0.borrow_mut().flush_gap = Duration::ZERO;
        let observer = live.session_observer();
        Rig {
            dir,
            live,
            observer,
            transcript,
            state: 0,
        }
    }

    fn page(&self) -> String {
        std::fs::read_to_string(self.dir.path().join("index.html")).unwrap()
    }

    fn sending(&mut self, sentence: &str) {
        (self.observer)(&SessionEvent::Sending { sentence });
    }

    /// Answers `sentence`: `status` is `ok`/`error`/`interrupted`, `goals` the texts of the goals
    /// it left. The record goes to the transcript like the session's.
    fn answer(
        &mut self,
        sentence: &str,
        status: &str,
        error: Option<&str>,
        goals: &[&str],
        ms: u64,
    ) {
        if status == "ok" {
            self.state = match sentence.strip_prefix("undo ") {
                Some(n) => n.trim_end_matches('.').parse().unwrap(),
                None => self.state + 1,
            };
        }
        let goal_json: Vec<String> = goals
            .iter()
            .enumerate()
            .map(|(i, text)| {
                format!(
                    "{{\"id\":{},\"concl\":{{\"kind\":\"app\",\"pp\":\"c\"}},\"text\":{}}}",
                    i + 1,
                    serde_json::Value::from(*text)
                )
            })
            .collect();
        let response = format!(
            "{{\"version\":\"domino-json/1\",\"state\":{},\"status\":\"{status}\",{}\"messages\":[],\"proof\":{{\"goals\":[{}]}}}}",
            self.state,
            error.map_or(String::new(), |e| format!(
                "\"error\":{{\"msg\":{}}},",
                serde_json::Value::from(e)
            )),
            goal_json.join(",")
        );
        let record = format!(
            "{{\"file\":\"f\",\"ctx\":\"\",\"sentence\":{},\"ms\":{ms},\"response\":{response}}}\n",
            serde_json::Value::from(sentence)
        );
        self.transcript.write_all(record.as_bytes()).unwrap();
        let parsed = parse_response(&response).unwrap();
        (self.observer)(&SessionEvent::Answered {
            sentence,
            response: &parsed,
            elapsed: Duration::from_millis(ms),
            record_bytes: Some(record.len()),
        });
    }

    fn one_oracle(&self) {
        self.live
            .equivalence_started("Eq_A_B.ec", 0, "A", "B", &["PKENC".to_string()]);
        self.live.oracle_started("PKENC");
    }
}

fn admit() -> Admit {
    use super::super::driver::{AdmitReason, DominoView};
    Admit {
        reason: AdmitReason::DominoVerifiedEcFailed,
        id: "J3".into(),
        claim: "invariant".into(),
        domino: DominoView::Verified,
        goal: "g".into(),
    }
}

#[test]
fn a_pending_sentence_is_on_the_page_and_the_page_refreshes() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live
        .node_entered("N0", "synchronized", vec!["J1".into()], Some(0));
    rig.sending("smt(get_setE mem_set).");
    let page = rig.page();
    assert!(page.contains("http-equiv=\"refresh\""));
    assert!(page.contains("waiting for EasyCrypt"));
    assert!(page.contains("smt(get_setE mem_set)."));
    assert!(page.contains("PKENC"));
}

#[test]
fn the_final_write_drops_the_refresh_tag_and_the_pending_command() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.sending("sp 1 1.");
    rig.live.finish();
    let page = rig.page();
    assert!(!page.contains("http-equiv"));
    assert!(!page.contains("waiting for EasyCrypt"));
    assert!(page.contains("tactics (done)"));
    // the export phases that ran before are listed
    assert!(page.contains("types (2)") && page.contains("write (5)"));
}

#[test]
fn a_failed_run_says_so_and_stops_refreshing() {
    let rig = Rig::new();
    rig.live.fail("EasyCrypt closed its output");
    let page = rig.page();
    assert!(!page.contains("http-equiv"));
    assert!(page.contains("the run stopped: EasyCrypt closed its output"));
}

#[test]
fn steps_are_attributed_to_their_goal_with_status_and_error_text() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered(
        "N0",
        "synchronized",
        vec!["J1".into(), "J2".into()],
        Some(0),
    );
    rig.answer("sp 1 1.", "ok", None, &["goal after sp"], 10);
    rig.answer(
        "smt().",
        "error",
        Some("cannot prove goal (strict)"),
        &["goal after sp"],
        4300,
    );
    rig.answer("smt(foo).", "interrupted", None, &["goal after sp"], 60000);
    rig.live.admitted(&admit());
    rig.answer("admit.", "ok", None, &[], 5);
    rig.live.node_left();
    rig.live.finish();
    let page = rig.page();
    assert!(page.contains("b-accepted\">accepted"));
    assert!(page.contains("b-failed\">failed"));
    assert!(page.contains("cannot prove goal (strict)"));
    assert!(page.contains("b-timeout\">timed out"));
    assert!(page.contains("[J1 J2]"));
    assert!(page.contains(
        "(* domino: J3 invariant; reason: domino-verified-ec-failed; Domino: verified *)"
    ));
    assert!(page.contains("st-admitted\">admitted"));
    // the summary lists the admit with its reason
    assert!(page.contains("<td>J3</td><td>domino-verified-ec-failed</td>"));
}

#[test]
fn an_undo_marks_the_sentences_after_that_depth_as_undone() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.answer("sp 1 1.", "ok", None, &["g"], 1); // depth 1
    rig.answer("rcondt{1} ^if.", "ok", None, &["g"], 1); // depth 2
    rig.answer("auto.", "ok", None, &["g"], 1); // depth 3
    rig.answer("undo 1.", "ok", None, &["g"], 1);
    rig.answer("if.", "ok", None, &["g"], 1); // depth 2 again
    rig.live.finish();
    {
        let live = rig.live.0.borrow();
        let undone: Vec<(&str, bool)> = live
            .steps
            .iter()
            .filter(|s| !s.is_undo)
            .map(|s| (s.sentence.as_str(), s.undone))
            .collect();
        assert_eq!(
            undone,
            [
                ("sp 1 1.", false),
                ("rcondt{1} ^if.", true),
                ("auto.", true),
                ("if.", false)
            ]
        );
        // the undo itself is not a step of the goal
        assert_eq!(live.eqs[0].oracles[0].nodes[0].steps.len(), 4);
    }
    assert!(rig.page().contains("b-undone\">undone"));
}

#[test]
fn only_the_last_step_of_a_goal_has_its_goal_text_embedded() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.answer("sp 1 1.", "ok", None, &["FIRST-GOAL-TEXT"], 1);
    rig.answer("if.", "ok", None, &["LAST-GOAL-TEXT"], 1);
    rig.live.node_left();
    rig.live.finish();
    let page = rig.page();
    assert!(page.contains("LAST-GOAL-TEXT"));
    assert!(
        !page.contains("FIRST-GOAL-TEXT"),
        "earlier steps are only in the transcript"
    );
    assert!(page.contains("goal text not embedded"));
}

#[test]
fn while_running_the_goal_being_worked_on_is_embedded() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.answer("sp 1 1.", "ok", None, &["GOAL-AFTER-SP"], 1);
    rig.answer("if.", "ok", None, &["GOAL-AFTER-IF"], 1);
    rig.sending("smt().");
    let page = rig.page();
    assert!(page.contains("GOAL-AFTER-SP") && page.contains("GOAL-AFTER-IF"));
}

#[test]
fn goal_text_is_cut_and_the_cut_points_at_the_transcript() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    let long = "x".repeat(GOAL_TEXT_CAP + 500);
    let many: Vec<&str> = vec![long.as_str(); GOALS_PER_STEP + 2];
    rig.answer("sp 1 1.", "ok", None, &many, 1);
    rig.live.node_left();
    rig.live.finish();
    let page = rig.page();
    assert_eq!(
        page.matches(&"x".repeat(GOAL_TEXT_CAP)).count(),
        GOALS_PER_STEP
    );
    assert!(!page.contains(&"x".repeat(GOAL_TEXT_CAP + 1)));
    assert!(page.contains("500 more characters, see transcript record 0"));
    assert!(page.contains("2 more goal(s), see transcript record 0"));
    assert!(page.len() < 100_000, "page is {} bytes", page.len());
}

#[test]
fn timings_are_in_one_element_and_stripping_it_makes_runs_equal() {
    let run = |ms: u64, wait: u64| {
        let mut rig = Rig::new();
        rig.one_oracle();
        rig.live.node_entered("N0", "determined", vec![], Some(0));
        rig.answer("sp 1 1.", "ok", None, &["g"], ms);
        rig.answer("smt().", "error", Some("no"), &["g"], wait);
        rig.live.node_left();
        rig.live.finish();
        rig.page()
    };
    let (a, b) = (run(3, 4000), run(30, 4200));
    assert_ne!(a, b, "the timings differ");
    assert!(a.contains("<script id=\"timings\""));
    let (a, b) = (strip_timings(&a), strip_timings(&b));
    assert!(!a.contains("id=\"timings\""));
    assert_eq!(a, b);
}

#[test]
fn html_in_sentences_and_goals_is_escaped() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.answer(
        "have h : 1 < 2 /\\ true.",
        "ok",
        None,
        &["<b id=\"evil\">x</b>"],
        1,
    );
    rig.live.node_left();
    rig.live.finish();
    let page = rig.page();
    assert!(!page.contains("<b id=\"evil\">"));
    assert!(page.contains("&lt;b id=&quot;evil&quot;&gt;x&lt;/b&gt;"));
    assert!(page.contains("1 &lt; 2"));
}

#[test]
fn rungs_are_shown_on_the_goal_and_the_last_one_wins() {
    let rig = Rig::new();
    rig.one_oracle();
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.live.rung("0: auto => /#");
    rig.live.rung("ladder: smt()");
    rig.live.node_left();
    rig.live.finish();
    assert!(rig.page().contains("rung: ladder: smt()"));
}

#[test]
fn relative_links_climb_out_of_the_progress_directory() {
    let dir = tempfile::tempdir().unwrap();
    let progress = dir.path().join("easycrypt/T/progress");
    let lockstep = dir.path().join("debug/T/PKENC/easycrypt");
    std::fs::create_dir_all(&progress).unwrap();
    std::fs::create_dir_all(&lockstep).unwrap();
    assert_eq!(
        relative_href(&progress, &lockstep.join("index.html")).as_deref(),
        Some("../../../debug/T/PKENC/easycrypt/index.html")
    );
}

#[test]
fn writes_are_throttled_but_the_final_write_always_happens() {
    let mut rig = Rig::new();
    rig.one_oracle();
    rig.live.0.borrow_mut().flush_gap = Duration::from_secs(3600);
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.live.0.borrow_mut().touch(true);
    rig.answer("SENTENCE-ONE.", "ok", None, &["g"], 1);
    rig.sending("SENTENCE-TWO.");
    assert!(!rig.page().contains("SENTENCE-ONE."), "throttled");
    rig.live.finish();
    let page = rig.page();
    assert!(
        page.contains("SENTENCE-ONE."),
        "the final page has everything"
    );
    assert!(!page.contains("http-equiv"));
}

#[test]
fn the_header_says_what_the_run_is_doing_when_no_goal_is_in_front() {
    let rig = Rig::new();
    rig.one_oracle();
    rig.live.activity("lockstep execution");
    assert!(rig.page().contains("PKENC &rsaquo; lockstep execution"));
    rig.live.node_entered("N0", "determined", vec![], Some(0));
    rig.live.0.borrow_mut().touch(true);
    let page = rig.page();
    assert!(page.contains("N0 determined") && !page.contains("&rsaquo; lockstep execution"));
}
