// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 21: `domino easycrypt --progress <mode>` changes stderr only.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

fn run(mode: &str, out: &Path) -> (String, String) {
    let project = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../example-projects/hello-world");
    let output = Command::new(env!("CARGO_BIN_EXE_domino"))
        .args(["easycrypt", "--project"])
        .arg(&project)
        .arg("--out")
        .arg(out)
        .args(["--progress", mode])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn read_tree(dir: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    let mut tree = BTreeMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(d).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else {
                tree.insert(path.strip_prefix(dir).unwrap().to_path_buf(), std::fs::read(&path).unwrap());
            }
        }
    }
    tree
}

#[test]
fn stdout_and_files_are_identical_in_every_progress_mode() {
    let base = std::env::temp_dir().join(format!("domino-ec-progress-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);

    let mut results = Vec::new();
    for mode in ["auto", "plain", "bar", "none"] {
        let out = base.join(mode);
        let (stdout, stderr) = run(mode, &out);
        // Stdout names the output directory, so compare it with that path factored out.
        let stdout = stdout.replace(out.to_str().unwrap(), "<out>");
        results.push((mode, stdout, stderr, read_tree(&out)));
    }

    let (_, ref stdout0, _, ref tree0) = results[0];
    assert!(!tree0.is_empty());
    for (mode, stdout, _, tree) in &results {
        assert_eq!(stdout, stdout0, "stdout differs in --progress {mode}");
        assert_eq!(tree, tree0, "files differ in --progress {mode}");
    }

    let stderr_of = |m: &str| results.iter().find(|r| r.0 == m).unwrap().2.clone();
    assert_eq!(stderr_of("none"), "");
    // Not a terminal here, so `auto` is `plain`, and `bar` draws nothing.
    assert_eq!(stderr_of("auto"), stderr_of("plain"));
    assert!(stderr_of("plain").contains("games 1/"), "{}", stderr_of("plain"));
    assert!(stderr_of("plain").trim_end().ends_with("file(s) written"));

    let _ = std::fs::remove_dir_all(&base);
}
