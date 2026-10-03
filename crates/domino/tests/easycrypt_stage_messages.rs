// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 44: `easycrypt debug` and `easycrypt prove` say what they are doing. These run the
//! binary on the two-oracle project; `prove` needs a real EasyCrypt (`DOMINO_EASYCRYPT`, skipped
//! without it). Stderr is a pipe, so no bar is drawn; the bars are checked by hand.
#![cfg(all(feature = "cvc5-lib", unix))]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const PROJECT: &str = "hello-world-oracle-rename-new";

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

fn scratch(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("domino-ec-stages-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs the command; `debug` exits non-zero on this project (one of its oracles fails the
/// invariant), which is not what is tested here.
fn domino(out: &Path, easycrypt: Option<&Path>, args: &[&str]) -> Output {
    domino_on(PROJECT, out, easycrypt, args)
}

fn domino_on(project: &str, out: &Path, easycrypt: Option<&Path>, args: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_domino"));
    command
        .arg("easycrypt")
        .args(args)
        .arg("--project")
        .arg(workspace().join("example-projects").join(project))
        .arg("--out")
        .arg(out);
    match easycrypt {
        Some(path) => command.env("DOMINO_EASYCRYPT", path),
        None => command.env_remove("DOMINO_EASYCRYPT"),
    };
    let output = command.output().unwrap();
    assert!(
        output.status.success() || args[0] == "debug",
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

/// Stderr up to the error report `main` prints when a command fails.
fn stderr_lines(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .take_while(|l| !l.starts_with("Error:"))
        .map(str::to_string)
        .collect()
}

/// stdout without the lines that carry timings, and with the output directory factored out.
fn stable_stdout(output: &Output, out: &Path) -> String {
    String::from_utf8_lossy(&output.stdout)
        .replace(out.to_str().unwrap(), "<out>")
        .lines()
        .filter(|l| !l.starts_with("elapsed:") && !l.contains("goals closed") && !l.contains(": lockstep "))
        .collect::<Vec<_>>()
        .join("\n")
}

fn files_under(dir: &Path) -> BTreeSet<PathBuf> {
    let mut files = BTreeSet::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                files.insert(path.strip_prefix(dir).unwrap().to_path_buf());
            }
        }
    }
    files
}

#[test]
fn debug_announces_translation_in_memory_and_its_lockstep_runs() {
    let dir = scratch("debug");
    let debug = ["debug", "--theorem", "Proof", "--proofstep", "0"];
    let mut results = Vec::new();
    for mode in ["auto", "plain", "bar", "none"] {
        let out = dir.join(mode);
        let mut args = debug.to_vec();
        args.extend(["--progress", mode]);
        let output = domino(&out, None, &args);
        results.push((mode, out, output));
    }

    let (_, _, plain) = &results[1];
    let lines = stderr_lines(plain);
    let translating = lines
        .iter()
        .position(|l| {
            l == "easycrypt debug: translating Proof in memory (the export tree is not read or written)"
        })
        .unwrap_or_else(|| panic!("{lines:#?}"));
    let lockstep = lines
        .iter()
        .position(|l| l.starts_with("easycrypt debug: lockstep execution on 2 oracles of 1 equivalence → "))
        .unwrap_or_else(|| panic!("{lines:#?}"));
    assert!(translating < lockstep, "{lines:#?}");
    assert!(lines[lockstep].ends_with("/Proof/!debug!"), "{lines:#?}");
    // `domino debug`'s plain convention: one line per pair, after the stage line
    assert!(
        lines[lockstep + 1..].iter().any(|l| l.contains("debug:")),
        "{lines:#?}"
    );

    // `auto` on a pipe is `plain`; `bar` draws nothing without a terminal, but still speaks
    assert!(stderr_lines(&results[0].2).iter().any(|l| l.starts_with("easycrypt debug: lockstep")));
    assert!(stderr_lines(&results[2].2).iter().any(|l| l.starts_with("easycrypt debug: lockstep")));
    // `none` prints nothing new
    assert!(stderr_lines(&results[3].2).is_empty(), "{:#?}", stderr_lines(&results[3].2));

    let (_, out0, first) = &results[0];
    let stdout0 = stable_stdout(first, out0);
    let files0 = files_under(&out0.join("Proof"));
    assert!(files0.iter().all(|f| f.starts_with("!debug!")), "debug wrote outside !debug!: {files0:?}");
    for (mode, out, output) in &results {
        assert_eq!(stable_stdout(output, out), stdout0, "stdout differs in --progress {mode}");
        assert_eq!(files_under(&out.join("Proof")), files0, "files differ in --progress {mode}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn prove_says_what_it_wrote_for_each_equivalence_it_proves() {
    let Some(ec) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("prove");
    let prove = ["prove", "--theorem", "Proof", "--progress", "plain"];
    let fresh = domino(&dir, Some(&ec), &prove);
    let lines = stderr_lines(&fresh);
    assert!(lines.iter().any(|l| l == "easycrypt prove: translating Proof in memory"), "{lines:#?}");
    assert!(!lines.iter().any(|l| l.contains("missing from the translation")), "{lines:#?}");
    let wrote: Vec<&String> = lines
        .iter()
        .filter(|l| l.starts_with("easycrypt prove: Eq_") && l.contains("translation files"))
        .collect();
    assert!(!wrote.is_empty(), "{lines:#?}");
    // each equivalence is announced once; only the first one wrote the shared files
    let named = |l: &str| l.split("files: ").nth(1).map(|f| f.split(", ").count());
    for (i, line) in wrote.iter().enumerate() {
        assert!(line.contains("wrote") || line.contains("wrote missing translation files"), "{line}");
        if i == 0 {
            assert!(
                line.contains("Types.ec") || line.contains("missing translation files"),
                "the first equivalence writes the shared files: {line}"
            );
        } else {
            assert_eq!(named(line), Some(1), "a later one lists only its own file: {line}");
        }
    }

    // a complete session record skips the equivalence: no translation-files line for it
    let again = domino(&dir, Some(&ec), &prove);
    let lines = stderr_lines(&again);
    assert!(lines.iter().any(|l| l.contains("skipping Eq_")), "{lines:#?}");
    assert!(!lines.iter().any(|l| l.contains("translation files")), "{lines:#?}");

    // `--progress none` says nothing about it
    let none_dir = scratch("prove-none");
    let quiet = domino(&none_dir, Some(&ec), &["prove", "--theorem", "Proof", "--progress", "none"]);
    assert!(
        !stderr_lines(&quiet).iter().any(|l| l.contains("easycrypt prove:") || l.contains("translation files")),
        "{:#?}",
        stderr_lines(&quiet)
    );
    assert_eq!(stable_stdout(&fresh, &dir), stable_stdout(&quiet, &none_dir));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&none_dir);
}

/// Two equivalences, so "later ones list only their own file" can be seen. Over 6 files the
/// first line counts instead of naming, which is the rule too.
#[test]
fn prove_lists_the_shared_files_once_and_then_only_each_equivalences_own() {
    let Some(ec) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("two-equivalences");
    let output = domino_on(
        "simple-KEM-example",
        &dir,
        Some(&ec),
        &["prove", "--theorem", "KEM_Proof", "--progress", "plain"],
    );
    let lines = stderr_lines(&output);
    let wrote: Vec<&String> = lines
        .iter()
        .filter(|l| l.starts_with("easycrypt prove: Eq_") && l.contains("translation files"))
        .collect();
    assert_eq!(wrote.len(), 2, "{lines:#?}");
    assert!(
        wrote[0].starts_with("easycrypt prove: Eq_Prot_H1_kem_correctness_real — wrote ")
            && wrote[0].ends_with(" missing translation files"),
        "{}",
        wrote[0]
    );
    assert_eq!(
        wrote[1].as_str(),
        "easycrypt prove: Eq_H1_kem_correctness_ideal_H2 — wrote missing translation files: \
         Eq_H1_kem_correctness_ideal_H2.ec"
    );
    assert!(!lines.iter().any(|l| l.contains("missing from the translation")), "{lines:#?}");
    let _ = std::fs::remove_dir_all(&dir);
}
