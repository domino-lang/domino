// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 34: Ctrl-C stops a tactics run and leaves a partial proof. These run the binary and
//! send it `SIGINT`, with a stand-in EasyCrypt, so no real one is needed. They need the
//! `cvc5-lib` build (lockstep execution runs for real).
#![cfg(all(feature = "cvc5-lib", unix))]

use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn scratch(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("domino-ec-ctrl-c-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// hello-world's oracle goal after `call (…); last first.`, as EasyCrypt's JSON has it: enough
/// for the run to find its oracle.
const ORACLE_GOAL: &str = r#"{"id":1,"concl":{"kind":"equivF","pp":"equiv[d_UsefulOracle]","left":{"proc":{"path":"Top.Comp_MediumComposition.Game_MediumComposition./d_UsefulOracle","top":"Top.Comp_MediumComposition.Game_MediumComposition","name":"d_UsefulOracle"}},"right":{"proc":{"path":"Top.Comp_SmallComposition.Game_SmallComposition./d_UsefulOracle","top":"Top.Comp_SmallComposition.Game_SmallComposition","name":"d_UsefulOracle"}}},"text":"the oracle goal"}"#;

/// A stand-in `easycrypt cli -json`: every sentence is accepted and leaves hello-world's oracle
/// goal, except `admit.`, which the walk sends first on it (the goal is not a program, so the
/// walk falls back and admits). That one runs until a `SIGINT` (answered `interrupted`), or,
/// with `ignore_sigint`, for 20 s. When it starts, the file `admitting` appears in `dir`.
fn stand_in(dir: &Path, ignore_sigint: bool) -> PathBuf {
    let answer = |status: &str| {
        format!(
            r#"{{"version":"domino-json/1","state":1,"status":"{status}","messages":[],"proof":{{"goals":[{ORACLE_GOAL}]}}}}"#
        )
    };
    std::fs::write(dir.join("ok.json"), answer("ok") + "\n").unwrap();
    std::fs::write(dir.join("interrupted.json"), answer("interrupted") + "\n").unwrap();
    let on_int = if ignore_sigint { "''" } else { "'int=1'" };
    let script = dir.join("ec.native");
    std::fs::write(
        &script,
        format!(
            r#"#!/bin/sh
cd '{dir}'
int=0
trap {on_int} INT
while IFS= read -r line; do
  case "$line" in
    admit.*)
      : > admitting
      n=0
      while [ $int = 0 ] && [ $n -lt 200 ]; do sleep 0.1; n=$((n+1)); done
      if [ $int = 1 ]; then cat interrupted.json; else cat ok.json; fi
      int=0;;
    *) cat ok.json;;
  esac
done
"#,
            dir = dir.display()
        ),
    )
    .unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
    script
}

/// `domino easycrypt --tactics` on hello-world, with `easycrypt` as its EasyCrypt.
fn tactics(out: &Path, easycrypt: &Path) -> Child {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "--tactics", "--progress", "none", "--project"])
        .arg(workspace().join("example-projects/hello-world"))
        .arg("--out")
        .arg(out)
        .env("DOMINO_EASYCRYPT", easycrypt)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap()
}

/// Waits until `path` exists, or fails the test if the run ends first.
fn wait_for(path: &Path, child: &mut Child) {
    let began = Instant::now();
    while !path.exists() {
        if let Some(status) = child.try_wait().unwrap() {
            panic!("the run ended ({status}) before {}", path.display());
        }
        assert!(
            began.elapsed() < Duration::from_secs(120),
            "no {}",
            path.display()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn sigint(child: &Child) {
    let status = Command::new("kill")
        .args(["-INT", &child.id().to_string()])
        .status()
        .unwrap();
    assert!(status.success());
}

/// Waits for the run to end, at most `limit`; returns its status and how long it took.
fn wait_at_most(child: &mut Child, limit: Duration) -> (ExitStatus, Duration) {
    let began = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            return (status, began.elapsed());
        }
        if began.elapsed() > limit {
            let _ = child.kill();
            panic!("the run did not end within {limit:?} of the Ctrl-C");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn read_pipe(pipe: Option<impl std::io::Read>) -> String {
    let mut text = String::new();
    if let Some(mut pipe) = pipe {
        let _ = pipe.read_to_string(&mut text);
    }
    text
}

#[test]
fn ctrl_c_interrupts_the_running_sentence_seals_the_oracle_and_exits_130() {
    let dir = scratch("once");
    let easycrypt = stand_in(&dir, false);
    let theorem = dir.join("out/Proof");
    let mut child = tactics(&dir.join("out"), &easycrypt);
    wait_for(&dir.join("admitting"), &mut child);
    sigint(&child);
    let (status, took) = wait_at_most(&mut child, Duration::from_secs(10));
    let stdout = read_pipe(child.stdout.take());
    let stderr = read_pipe(child.stderr.take());
    assert_eq!(status.code(), Some(130), "{stderr}");
    assert!(took < Duration::from_secs(3), "{took:?}");
    assert!(
        stderr.contains("stopping the current EasyCrypt sentence"),
        "{stderr}"
    );

    // the oracle in flight is sealed: what was accepted, then its open goal admitted
    let text = std::fs::read_to_string(theorem.join("Eq_medium_composition_small_composition.ec"))
        .unwrap();
    assert!(
        text.contains(
            "(* d_UsefulOracle *)\n+ proc; inline.\n  admit. (* domino: router open-goal; \
             reason: interrupted; Domino: n/a *)\n"
        ),
        "{text}"
    );
    // the report names it, its counts are the file's, and the summary still prints
    let report =
        std::fs::read_to_string(theorem.join("Eq_medium_composition_small_composition.report.txt"))
            .unwrap();
    let line = "interrupted: sealed UsefulOracle with 1 admits at node router";
    assert!(report.contains(line), "{report}");
    assert!(report.contains("1 admits (interrupted 1)"), "{report}");
    assert!(
        report.contains("1 oracles, 0 goals closed, 1 admits"),
        "{report}"
    );
    assert!(stdout.contains(line), "{stdout}");
    // the page: an interrupted run, and the sentence the Ctrl-C interrupted
    let page = std::fs::read_to_string(theorem.join("progress/index.html")).unwrap();
    assert!(page.contains("tactics (interrupted)"), "{page}");
    assert!(!page.contains("tactics (failed)"));
    assert!(
        page.contains("b-interrupted\">interrupted</span><code>admit.</code>"),
        "{page}"
    );
    assert!(!page.contains("timed out"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_second_ctrl_c_exits_130_without_waiting_for_easycrypt() {
    let dir = scratch("twice");
    // an EasyCrypt that does not answer the interrupt: the first press alone would wait 30 s
    let easycrypt = stand_in(&dir, true);
    let mut child = tactics(&dir.join("out"), &easycrypt);
    wait_for(&dir.join("admitting"), &mut child);
    sigint(&child);
    std::thread::sleep(Duration::from_millis(300));
    sigint(&child);
    let (status, took) = wait_at_most(&mut child, Duration::from_secs(10));
    assert_eq!(status.code(), Some(130));
    assert!(took < Duration::from_secs(2), "{took:?}");
    let _ = std::fs::remove_dir_all(&dir);
}
