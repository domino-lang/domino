// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 35: translation and proving are separate commands (ADR 0006). These run the binary
//! against a real EasyCrypt: they need the `cvc5-lib` build and `DOMINO_EASYCRYPT` (skipped
//! without it).
#![cfg(all(feature = "cvc5-lib", unix))]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

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
    let dir = std::env::temp_dir().join(format!("domino-ec-prove-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// `domino easycrypt <args>` on an example project, writing under `out`.
fn domino(project: &str, out: &Path, easycrypt: &Path, args: &[&str]) -> Output {
    // only translation and `prove` report progress
    let progress: &[&str] = match args.first() {
        Some(&"check-alignment" | &"debug") => &[],
        _ => &["--progress", "none"],
    };
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .arg("easycrypt")
        .args(args)
        .args(progress)
        .arg("--project")
        .arg(workspace().join("example-projects").join(project))
        .arg("--out")
        .arg(out)
        .env("DOMINO_EASYCRYPT", easycrypt)
        .output()
        .unwrap()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// Every file directly in `dir`, with its contents and modification time.
fn snapshot(dir: &Path) -> BTreeMap<String, (Vec<u8>, std::time::SystemTime)> {
    std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap())
        .filter(|e| e.path().is_file())
        .map(|e| {
            (
                e.file_name().to_string_lossy().into_owned(),
                (
                    std::fs::read(e.path()).unwrap(),
                    e.metadata().unwrap().modified().unwrap(),
                ),
            )
        })
        .collect()
}

const EQ: &str = "Eq_medium_composition_small_composition";

#[test]
fn a_proof_job_touches_only_its_own_files_skips_a_done_equivalence_and_recreates_what_is_missing() {
    let Some(ec) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("job");
    let theorem = dir.join("Proof");
    let out = domino("hello-world", &dir, &ec, &[]);
    assert!(out.status.success(), "{}", stderr(&out));
    let prove = ["prove", "--theorem", "Proof", "--proofstep", "0"];

    // proves without `--force`, and modifies only its own files
    let before = snapshot(&theorem);
    let out = domino("hello-world", &dir, &ec, &prove);
    assert!(out.status.success(), "{}", stderr(&out));
    let after = snapshot(&theorem);
    for (name, was) in &before {
        if [".ec", ".report.txt", ".session.json"]
            .iter()
            .any(|s| name == &format!("{EQ}{s}"))
        {
            continue;
        }
        assert_eq!(after.get(name), Some(was), "{name} was touched");
    }
    assert!(
        !String::from_utf8_lossy(&after[&format!("{EQ}.ec")].0).contains("+ proc; inline. admit.")
    );
    assert!(after.contains_key(&format!("{EQ}.session.json")));
    assert!(!stderr(&out).contains("created"), "{}", stderr(&out));
    // `--out` is honoured by lockstep output too
    assert!(theorem.join("!debug!").is_dir());

    // a second run skips, exit 0, and writes nothing
    let done = snapshot(&theorem);
    let out = domino("hello-world", &dir, &ec, &prove);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stderr(&out).contains(&format!("skipping {EQ}: already proved (1 of 1 oracles)")),
        "{}",
        stderr(&out)
    );
    assert_eq!(snapshot(&theorem), done);

    // `-f` proves it again, and a missing translation file is created, with a line about it
    std::fs::remove_file(theorem.join("Types.ec")).unwrap();
    let mut forced = prove.to_vec();
    forced.push("-f");
    let out = domino("hello-world", &dir, &ec, &forced);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("created Types.ec (missing from the translation)"),
        "{}",
        stderr(&out)
    );
    assert_eq!(
        std::fs::read(theorem.join("Types.ec")).unwrap(),
        before["Types.ec"].0
    );
    assert!(stdout(&out).contains("3 goals closed"), "{}", stdout(&out));

    // a file that exists is not read: garbage stays, and EasyCrypt's error is reported
    std::fs::write(theorem.join("Types.ec"), "garbage\n").unwrap();
    let out = domino("hello-world", &dir, &ec, &forced);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("parse error"), "{}", stderr(&out));
    assert_eq!(
        std::fs::read_to_string(theorem.join("Types.ec")).unwrap(),
        "garbage\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_proof_job_never_creates_another_equivalences_file() {
    let Some(ec) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("other");
    let theorem = dir.join("KEM_Proof");
    let out = domino("simple-KEM-example", &dir, &ec, &[]);
    assert!(out.status.success(), "{}", stderr(&out));
    let (mine, other) = (
        theorem.join("Eq_Prot_H1_kem_correctness_real.ec"),
        theorem.join("Eq_H1_kem_correctness_ideal_H2.ec"),
    );
    std::fs::remove_file(&mine).unwrap();
    std::fs::remove_file(&other).unwrap();
    std::fs::remove_file(theorem.join("Types.ec")).unwrap();

    // an oracle that does not exist ends the job before its own skeleton is written
    let out = domino(
        "simple-KEM-example",
        &dir,
        &ec,
        &[
            "prove",
            "--theorem",
            "KEM_Proof",
            "--proofstep",
            "0",
            "--oracle",
            "NoSuchOracle",
        ],
    );
    assert!(!out.status.success());
    assert!(
        theorem.join("Types.ec").exists(),
        "translation's file is created"
    );
    assert!(!mine.exists(), "a typo in `--oracle` writes no skeleton");
    assert!(!other.exists(), "another equivalence's file is not created");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn check_alignment_and_debug_are_subcommands_with_the_old_outputs() {
    let Some(ec) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("modes");
    let out = domino("hello-world", &dir, &ec, &[]);
    assert!(out.status.success(), "{}", stderr(&out));
    let theorem = dir.join("Proof");
    let eq = theorem.join(format!("{EQ}.ec"));
    let translated = std::fs::read(&eq).unwrap();

    let out = domino(
        "hello-world",
        &dir,
        &ec,
        &["check-alignment", "--theorem", "Proof"],
    );
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("1 oracles checked, 0 mismatches"),
        "{}",
        stdout(&out)
    );
    assert!(theorem.join("alignment.txt").exists());

    // `--project` and `--out` are accepted after the subcommand too
    let out = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "debug", "--theorem", "Proof", "--project"])
        .arg(workspace().join("example-projects/hello-world"))
        .arg("--out")
        .arg(&dir)
        .output()
        .unwrap();
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("UsefulOracle: 1 joint paths, ok"),
        "{}",
        stdout(&out)
    );
    assert!(theorem.join("!debug!").is_dir());
    assert_eq!(
        std::fs::read(&eq).unwrap(),
        translated,
        "neither rewrites the translation"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
