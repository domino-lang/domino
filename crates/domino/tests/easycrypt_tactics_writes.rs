// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 33: the file on disk is what is proved. These run the binary, so the process can be
//! killed and its EasyCrypt replaced. They need the `cvc5-lib` build and `DOMINO_EASYCRYPT`
//! (skipped without it).
#![cfg(all(feature = "cvc5-lib", unix))]

use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The `easycrypt cli -json` binary of `DOMINO_EASYCRYPT`, a relative path taken from the
/// workspace root.
fn easycrypt_binary() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var_os("DOMINO_EASYCRYPT").filter(|v| !v.is_empty())?);
    Some(if path.is_relative() {
        workspace().join(path)
    } else {
        path
    })
}

fn scratch(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("domino-ec-writes-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// `domino easycrypt`: translation only, which `prove` runs against (story 35).
fn translate(project: &str, out: &Path) {
    let status = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "--progress", "none", "--project"])
        .arg(workspace().join("example-projects").join(project))
        .arg("--out")
        .arg(out)
        .env_remove("DOMINO_EASYCRYPT")
        .status()
        .unwrap();
    assert!(status.success());
}

/// `domino easycrypt prove` on an example project, with `easycrypt` as its EasyCrypt.
fn tactics(project: &str, out: &Path, easycrypt: &Path, extra: &[&str]) -> Child {
    translate(project, out);
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "prove", "--theorem", "Proof", "--progress", "none", "--project"])
        .arg(workspace().join("example-projects").join(project))
        .arg("--out")
        .arg(out)
        .args(extra)
        .env("DOMINO_EASYCRYPT", easycrypt)
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap()
}

#[test]
fn a_tactics_run_never_runs_easycrypt_compile() {
    let Some(real) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("no-compile");
    // an EasyCrypt that logs every invocation and fails every `compile`
    let log = dir.join("invocations.log");
    let wrapper = dir.join("ec.native");
    std::fs::write(
        &wrapper,
        format!(
            "#!/bin/sh\necho \"$1\" >> '{}'\nif [ \"$1\" = compile ]; then exit 1; fi\nexec '{}' \"$@\"\n",
            log.display(),
            real.display()
        ),
    )
    .unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();

    let out = tactics("hello-world", &dir.join("out"), &wrapper, &[])
        .wait_with_output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let invocations = std::fs::read_to_string(&log).unwrap();
    assert!(invocations.lines().any(|l| l == "cli"), "{invocations}");
    assert!(
        !invocations.lines().any(|l| l == "compile"),
        "{invocations}"
    );
    // the proof is written all the same, and no `.eco` cache next to it
    let proof =
        std::fs::read_to_string(dir.join("out/Proof/Eq_medium_composition_small_composition.ec"))
            .unwrap();
    assert!(!proof.contains("+ proc; inline. admit."), "{proof}");
    assert!(!dir
        .join("out/Proof/Eq_medium_composition_small_composition.eco")
        .exists());
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_run_killed_mid_oracle_leaves_its_last_write_intact() {
    let Some(easycrypt) = easycrypt_binary() else {
        eprintln!("DOMINO_EASYCRYPT not set, skipping");
        return;
    };
    let dir = scratch("sigkill");
    let theorem = dir.join("out/Proof");
    let file = theorem.join("Eq_medium_composition_small_composition.ec");
    let report = theorem.join("Eq_medium_composition_small_composition.report.txt");
    let mut child = tactics(
        "hello-world-oracle-rename-new",
        &dir.join("out"),
        &easycrypt,
        &["--write-granularity", "node", "--no-rung0"],
    );
    // wait for a write that sealed an oracle part way, then SIGKILL
    let began = Instant::now();
    loop {
        if let Ok(text) = std::fs::read_to_string(&file) {
            if text.contains("reason: interrupted") {
                break;
            }
        }
        if let Some(status) = child.try_wait().unwrap() {
            panic!("the run ended ({status}) before any sealed write");
        }
        assert!(
            began.elapsed() < Duration::from_secs(300),
            "no sealed write"
        );
        std::thread::sleep(Duration::from_millis(2));
    }
    child.kill().unwrap();
    let status = child.wait().unwrap();
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(status.signal(), Some(9), "killed, not finished");

    // what is on disk is a whole write, at least as far as the one seen: every oracle bullet,
    // closed by `qed.`, and the first oracle's work in it
    let text = std::fs::read_to_string(&file).unwrap();
    assert!(text.trim_end().ends_with("end section."), "{text}");
    assert!(text.contains("\nqed.\n"), "{text}");
    let progress = sspverif::writers::easycrypt::overwrite::proof_progress(&text);
    assert_eq!(progress.total, 2, "{text}");
    assert!(progress.partial + progress.proved >= 1, "{text}");
    // the report is written just before the file: whole, and at least as new as the file (a
    // kill between the two renames leaves it one write ahead)
    let report = std::fs::read_to_string(&report).unwrap();
    assert!(
        report.contains(" oracles, ") && report.contains(" admits, "),
        "{report}"
    );
    // nothing half-written outside `progress/`
    for entry in std::fs::read_dir(&theorem).unwrap() {
        let name = entry.unwrap().file_name().to_string_lossy().into_owned();
        assert!(!name.ends_with(".tmp"), "{name}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
