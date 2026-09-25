// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 32: `domino easycrypt` never overwrites the export tree without `--force`
//! (ADR 0004).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn project(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../example-projects")
        .join(rel)
}

fn scratch(test: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("domino-ec-overwrite-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

fn easycrypt(project: &Path, out: &Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "--progress", "none", "--project"])
        .arg(project)
        .arg("--out")
        .arg(out)
        .args(extra)
        .env_remove("DOMINO_EASYCRYPT")
        .output()
        .unwrap()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn read_tree(dir: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    let mut tree = BTreeMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(d) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                tree.insert(
                    path.strip_prefix(dir).unwrap().to_path_buf(),
                    std::fs::read(&path).unwrap(),
                );
            }
        }
    }
    tree
}

#[test]
fn a_second_run_refuses_and_lists_the_files_and_force_rewrites_them() {
    let hello = project("hello-world");
    let base = scratch("second-run");
    let (first, again) = (base.join("first"), base.join("again"));

    let out = easycrypt(&hello, &first, &[]);
    assert!(out.status.success(), "{}", stderr(&out));
    let written = read_tree(&first);
    assert!(written.contains_key(Path::new("Proof/Types.ec")));

    // a second run into the same directory: non-zero, every file listed, nothing touched
    std::fs::write(first.join("Proof/Types.ec"), "(* edited by hand *)\n").unwrap();
    let before = read_tree(&first);
    let out = easycrypt(&hello, &first, &[]);
    assert!(!out.status.success());
    let err = stderr(&out);
    for file in written.keys() {
        assert!(
            err.contains(&file.display().to_string()),
            "{file:?} not listed:\n{err}"
        );
    }
    assert!(err.contains("--force"), "{err}");
    assert!(
        out.stdout.is_empty(),
        "the export ran: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert_eq!(read_tree(&first), before);

    // `--force` rewrites, byte for byte what a run into an empty directory writes
    let out = easycrypt(&hello, &first, &["--force"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let out = easycrypt(&hello, &again, &[]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(read_tree(&first), read_tree(&again));
    assert_eq!(read_tree(&first), written);

    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn run_artifacts_do_not_block_and_a_missing_or_empty_directory_passes() {
    let hello = project("hello-world");
    let base = scratch("artifacts");

    // missing
    let out = easycrypt(&hello, &base.join("missing"), &[]);
    assert!(out.status.success(), "{}", stderr(&out));

    // empty, both the output directory and the theorem's directory
    std::fs::create_dir_all(base.join("empty")).unwrap();
    let out = easycrypt(&hello, &base.join("empty"), &[]);
    assert!(out.status.success(), "{}", stderr(&out));
    std::fs::create_dir_all(base.join("empty-theorem/Proof")).unwrap();
    let out = easycrypt(&hello, &base.join("empty-theorem"), &[]);
    assert!(out.status.success(), "{}", stderr(&out));

    // only what a tactics run leaves about itself
    let theorem = base.join("artifacts/Proof");
    for rel in [
        "progress/index.html",
        "progress/ec-transcript.jsonl",
        "!debug!/Eq_a_b/Oracle/joint.html",
        "Eq_medium_composition_small_composition.report.txt",
        "alignment.txt",
    ] {
        let path = theorem.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, "left by an earlier run\n").unwrap();
    }
    let out = easycrypt(&hello, &base.join("artifacts"), &[]);
    assert!(out.status.success(), "{}", stderr(&out));

    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn a_hand_written_development_at_the_output_directory_is_refused_and_untouched() {
    let hello = project("hello-world");
    let base = scratch("hand-written");
    // the shape of `example-projects/4WHS/ec4whs/full`: hand-written files right in `--out`
    std::fs::create_dir_all(&base).unwrap();
    std::fs::write(base.join("Prf.ec"), "(* hand-written *)\n").unwrap();
    std::fs::write(base.join("Invariants.ec"), "(* hand-written *)\n").unwrap();
    let before = read_tree(&base);

    let out = easycrypt(&hello, &base, &[]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("Prf.ec") && err.contains("Invariants.ec"),
        "{err}"
    );
    assert_eq!(read_tree(&base), before);
    assert!(!base.join("Proof").exists());

    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn one_dirty_theorem_directory_stops_every_theorem() {
    // 4WHS has two theorems; the check runs before any export work, so this is cheap
    let whs = project("4WHS");
    let base = scratch("multi");
    std::fs::create_dir_all(base.join("Full4WHS")).unwrap();
    std::fs::write(base.join("Full4WHS/notes.txt"), "mine\n").unwrap();

    let out = easycrypt(&whs, &base, &[]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(err.contains("Full4WHS/notes.txt"), "{err}");
    assert!(
        !base.join("Simple4WHS").exists(),
        "the clean theorem was written"
    );

    // both dirty: both reported in one run
    std::fs::create_dir_all(base.join("Simple4WHS")).unwrap();
    std::fs::write(base.join("Simple4WHS/Types.ec"), "mine\n").unwrap();
    let out = easycrypt(&whs, &base, &[]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("Full4WHS/notes.txt") && err.contains("Simple4WHS/Types.ec"),
        "{err}"
    );

    // a run on one theorem says nothing about the other's directory
    std::fs::remove_file(base.join("Simple4WHS/Types.ec")).unwrap();
    let out = easycrypt(&whs, &base, &["--theorem", "Simple4WHS"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(base.join("Simple4WHS/Types.ec").exists());

    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn the_overwrite_check_comes_before_the_easycrypt_probe() {
    let hello = project("hello-world");
    let base = scratch("probe");
    std::fs::create_dir_all(base.join("Proof")).unwrap();
    std::fs::write(base.join("Proof/Types.ec"), "mine\n").unwrap();

    // no `DOMINO_EASYCRYPT` (and, without `cvc5-lib`, no `--tactics` at all)
    let out = easycrypt(&hello, &base, &["--tactics"]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("Proof/Types.ec") && err.contains("--force"),
        "{err}"
    );

    let _ = std::fs::remove_dir_all(&base);
}
