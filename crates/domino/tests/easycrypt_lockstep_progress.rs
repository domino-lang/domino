// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 39: path exploration has its own progress line. These run the binary against a real
//! EasyCrypt: they need the `cvc5-lib` build and `DOMINO_EASYCRYPT` (skipped without it).
//! Stderr here is a pipe, so the bar mode draws nothing; what the bars look like on a terminal
//! is checked by hand.
#![cfg(all(feature = "cvc5-lib", unix))]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Two oracles, so "per oracle" is more than one line.
const PROJECT: &str = "example-projects/hello-world-oracle-rename-new";

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn easycrypt_binary() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var_os("DOMINO_EASYCRYPT").filter(|v| !v.is_empty())?);
    Some(if path.is_relative() {
        workspace().join(path)
    } else {
        path
    })
}

fn prove(easycrypt: &Path, mode: &str) -> Output {
    let out = std::env::temp_dir().join(format!(
        "domino-ec-lockstep-progress-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&out);
    std::fs::create_dir_all(&out).unwrap();
    let project = workspace().join(PROJECT);
    let translated = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "--progress", "none", "--project"])
        .arg(&project)
        .arg("--out")
        .arg(&out)
        .env_remove("DOMINO_EASYCRYPT")
        .status()
        .unwrap();
    assert!(translated.success());
    let output = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "prove", "--theorem", "Proof", "--progress", mode, "--project"])
        .arg(&project)
        .arg("--out")
        .arg(&out)
        .env("DOMINO_EASYCRYPT", easycrypt)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let _ = std::fs::remove_dir_all(&out);
    output
}

fn lockstep_lines(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter(|l| l.contains("lockstep:"))
        .map(str::to_string)
        .collect()
}

/// stdout without the lines that carry the run's timings, which differ per run.
fn stable_stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|l| !l.starts_with("elapsed:") && !l.contains("goals closed") && !l.contains(": lockstep "))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn plain_prints_two_lockstep_lines_per_oracle_and_none_prints_none() {
    let Some(easycrypt) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let plain = prove(&easycrypt, "plain");
    let lines = lockstep_lines(&plain);
    assert!(!lines.is_empty() && lines.len().is_multiple_of(2), "{lines:#?}");
    for pair in lines.chunks(2) {
        assert!(pair[0].ends_with("lockstep: started"), "{pair:#?}");
        assert!(
            pair[1].contains("lockstep: ") && pair[1].contains(" joint path") && pair[1].contains(" stuck point"),
            "{pair:#?}"
        );
        assert!(pair[1].contains(" in ") && pair[1].ends_with('s'), "{pair:#?}");
        // the same oracle name on both lines
        assert_eq!(
            pair[0].split_whitespace().next(),
            pair[1].split_whitespace().next(),
            "{pair:#?}"
        );
    }
    // per-path debug lines would flood a log
    let stderr = String::from_utf8_lossy(&plain.stderr);
    assert!(!stderr.contains("debug:"), "{stderr}");

    let none = prove(&easycrypt, "none");
    assert!(lockstep_lines(&none).is_empty(), "{:#?}", lockstep_lines(&none));

    let bar = prove(&easycrypt, "bar");
    assert!(lockstep_lines(&bar).is_empty(), "no terminal, nothing drawn");
    assert_eq!(stable_stdout(&plain), stable_stdout(&none));
    assert_eq!(stable_stdout(&bar), stable_stdout(&none));
}
