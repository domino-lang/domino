// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 19: `domino debug` runs all claims by default and sweeps every oracle.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn deps_project() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/story19/deps")
}

fn debug(extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["debug", "--progress", "none", "--path"])
        .arg(deps_project())
        .args(extra)
        .output()
        .unwrap()
}

#[test]
fn easycrypt_flag_is_gone_from_debug() {
    let out = debug(&["--easycrypt"]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("--easycrypt"));
}

#[test]
fn proofstep_without_proof_is_rejected() {
    let out = debug(&["--proofstep", "0"]);
    assert!(!out.status.success());
}

#[cfg(feature = "cvc5-lib")]
#[test]
fn sweep_prints_a_line_per_oracle_and_fails_on_a_failing_claim() {
    let out = debug(&["--lockstep"]);
    assert!(!out.status.success(), "AbortDiff fails, so the sweep must exit non-zero");
    let stdout = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    for oracle in ["Branch", "AbortDiff", "AbortBoth", "Admitted"] {
        assert!(stdout.contains(oracle), "missing {oracle}:\n{stdout}");
    }
    assert!(deps_project()
        .join("_build/debug/domino/index.html")
        .exists());
}

#[test]
fn easycrypt_debug_has_no_claim_flag() {
    let out = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "debug", "--theorem", "x", "--claim", "x", "--project"])
        .arg(deps_project())
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("--claim"));
}
