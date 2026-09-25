// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 32 (ADR 0004): `domino easycrypt` never overwrites the export tree without
//! `--force`.
//!
//! [`check_export_tree`] runs before anything else in the command. It needs only the output
//! directory and the theorem names, and looks at:
//!
//! - every `<out>/<theorem>/` this invocation will write. Any file there that is not a
//!   **run artifact** ([`is_run_artifact`]) stops the run. Other theorems' directories are not
//!   looked at, so theorems can be exported one at a time into the same `<out>`.
//! - the files directly in `<out>`. Domino never writes there. A file there means `<out>` is
//!   somebody's own development (`example-projects/4WHS/ec4whs/full` is one), not an export root.
//!
//! One offending file anywhere stops the whole invocation, and the error lists all of them.

use std::path::{Path, PathBuf};

use miette::Diagnostic;
use thiserror::Error;

/// Directories, directly in `<out>/<theorem>/`, whose whole subtree is run artifacts: the live
/// page and the EasyCrypt transcript (`progress/`), and lockstep output (`!debug!/`, not yet
/// written there; see `docs/stories/symbolic-execution/19-…`).
pub const RUN_ARTIFACT_DIRS: &[&str] = &["progress", "!debug!"];

/// File names that are run artifacts wherever they are: the per-equivalence report
/// (`*.report.txt`) and the alignment report (`alignment.txt`).
fn is_run_artifact_name(name: &str) -> bool {
    name.ends_with(".report.txt") || name == "alignment.txt"
}

/// Whether `rel` (relative to `<out>/<theorem>/`) is a **run artifact**: a file a tactics run
/// writes about itself, regenerated every run and never hand-edited (`CONTEXT.md`). Stated as
/// directories and patterns, not a list of paths, so new files in those places stay exempt.
pub fn is_run_artifact(rel: &Path) -> bool {
    let mut components = rel.components();
    let Some(first) = components.next() else {
        return false;
    };
    if components.clone().next().is_some()
        && RUN_ARTIFACT_DIRS.iter().any(|d| first.as_os_str() == *d)
    {
        return true;
    }
    rel.file_name()
        .and_then(|n| n.to_str())
        .is_some_and(is_run_artifact_name)
}

/// An existing proof file with proved or partial proved oracles.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofProgress {
    /// Relative to `<out>`.
    pub file: PathBuf,
    pub oracles: OracleCounts,
}

/// How many of a proof file's oracles are proved.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct OracleCounts {
    /// Oracle bullets without an `admit`.
    pub proved: usize,
    /// Oracle bullets holding tactics and an `admit` (a partial proof).
    pub partial: usize,
    /// Oracle bullets in the file.
    pub total: usize,
}

/// Counts the oracle bullets of an `Eq_*.ec`: a `(* <proc> *)` line followed by a `+ proc…`
/// bullet, as the export writes them. A bullet is proved when no `admit.` is left in it (outside
/// comments), and partial proved when it holds more than the export's `+ proc; inline. admit.`.
pub fn proof_progress(text: &str) -> OracleCounts {
    let lines: Vec<&str> = text.lines().collect();
    let is_marker = |i: usize| {
        let line = lines[i].trim();
        line.strip_prefix("(* ")
            .and_then(|l| l.strip_suffix(" *)"))
            .is_some_and(|name| !name.is_empty() && !name.contains(char::is_whitespace))
            && lines
                .get(i + 1)
                .is_some_and(|next| next.trim_start().starts_with("+ proc"))
    };
    let mut counts = OracleCounts::default();
    let mut i = 0;
    while i < lines.len() {
        if !is_marker(i) {
            i += 1;
            continue;
        }
        let start = i + 1;
        let mut end = start + 1;
        while end < lines.len() && !is_marker(end) && lines[end].trim() != "qed." {
            end += 1;
        }
        let bullet = &lines[start..end];
        let admits = bullet.iter().any(|l| {
            let code = l.split("(*").next().unwrap_or("");
            code.split(|c: char| c.is_whitespace() || c == ';')
                .any(|w| w == "admit.")
        });
        let scripted = bullet
            .iter()
            .filter(|l| !l.trim().is_empty())
            .map(|l| l.trim())
            .ne(["+ proc; inline. admit."]);
        counts.total += 1;
        if !admits {
            counts.proved += 1;
        } else if scripted {
            counts.partial += 1;
        }
        i = end;
    }
    counts
}

/// The export would write where files other than run artifacts already are.
#[derive(Debug, Error)]
#[error(
    "{} existing file(s) under {} are not run artifacts, so `domino easycrypt` wrote nothing:\n{}",
    files.len(),
    out.display(),
    files.iter().map(|f| format!("  {}", f.display())).collect::<Vec<_>>().join("\n")
)]
pub struct ExportTreeOccupied {
    /// The output directory (`--out`).
    pub out: PathBuf,
    /// Every offending file, relative to `out`, sorted.
    pub files: Vec<PathBuf>,
    /// The proof files among them, in a theorem's directory, that hold proved or partial
    /// proved oracles.
    pub proofs: Vec<ProofProgress>,
}

impl Diagnostic for ExportTreeOccupied {
    fn code<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new("easycrypt::export_tree_occupied"))
    }

    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        let mut help = String::new();
        for p in &self.proofs {
            help.push_str(&format!(
                "{}: {} of {} oracles already proved; --force discards them",
                p.file.display(),
                p.oracles.proved,
                p.oracles.total
            ));
            if p.oracles.partial > 0 {
                help.push_str(&format!(
                    " (and the partial proof of {} more; `--oracle` limits a run to one oracle)",
                    p.oracles.partial
                ));
            }
            help.push('\n');
        }
        help.push_str(
            "move them away, choose another `--out`, or pass `--force` to write anyway \
             (it overwrites what the export writes and leaves other files in place)",
        );
        Some(Box::new(help))
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ExportTreeError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Occupied(#[from] ExportTreeOccupied),
    #[error("could not read {} to check that the export overwrites nothing", path.display())]
    #[diagnostic(code(easycrypt::export_tree_unreadable))]
    Read {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

/// Refuses when writing `theorems` under `out` would overwrite a file that is not a run
/// artifact (see the module doc). A missing or empty `out` passes.
pub fn check_export_tree(out: &Path, mut theorems: &[&str]) -> Result<(), ExportTreeError> {
    let exists = |path: &Path| path.symlink_metadata().is_ok();
    let mut files = Vec::new();
    match read_dir(out)? {
        Some(entries) => files.extend(entries.into_iter().filter(|e| !e.is_dir).map(|e| e.path)),
        // `out` itself is a file, so no theorem directory can be under it
        None if exists(out) => files.push(out.to_path_buf()),
        None => {}
    }
    if !out.is_dir() {
        theorems = &[];
    }
    for theorem in theorems {
        let dir = out.join(theorem);
        // a file where the theorem's directory goes is already listed, as a file in `out`
        let Some(entries) = read_dir(&dir)? else {
            continue;
        };
        let mut stack = vec![entries];
        while let Some(entries) = stack.pop() {
            for Entry { path, is_dir } in entries {
                if is_dir {
                    stack.extend(read_dir(&path)?);
                } else if !is_run_artifact(path.strip_prefix(&dir).expect("under the theorem")) {
                    files.push(path);
                }
            }
        }
    }
    if files.is_empty() {
        return Ok(());
    }

    let mut files: Vec<PathBuf> = files
        .into_iter()
        .map(|f| match f.strip_prefix(out) {
            Ok(rel) if !rel.as_os_str().is_empty() => rel.to_path_buf(),
            _ => f,
        })
        .collect();
    files.sort();
    let proofs = files
        .iter()
        // in a theorem's directory: `--force` leaves files directly in `out` alone
        .filter(|f| f.components().count() == 2)
        .filter(|f| {
            f.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("Eq_") && n.ends_with(".ec"))
        })
        .filter_map(|f| {
            let text = std::fs::read_to_string(out.join(f)).ok()?;
            let oracles = proof_progress(&text);
            (oracles.proved + oracles.partial > 0).then(|| ProofProgress {
                file: f.clone(),
                oracles,
            })
        })
        .collect();
    Err(ExportTreeOccupied {
        out: out.to_path_buf(),
        files,
        proofs,
    }
    .into())
}

/// One entry of a directory. A symbolic link is never a directory here.
struct Entry {
    path: PathBuf,
    is_dir: bool,
}

/// The entries of `dir`, or `None` when `dir` does not exist or is not a directory. `dir` itself
/// may be a link to a directory (a linked `--out`); links inside it are not followed.
fn read_dir(dir: &Path) -> Result<Option<Vec<Entry>>, ExportTreeError> {
    let read_error = |source| ExportTreeError::Read {
        path: dir.to_path_buf(),
        source,
    };
    match dir.metadata() {
        Ok(meta) if meta.is_dir() => {}
        Ok(_) => return Ok(None),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(read_error(e)),
    }
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(dir).map_err(read_error)? {
        let entry = entry.map_err(read_error)?;
        let is_dir = entry.file_type().map_err(read_error)?.is_dir();
        entries.push(Entry {
            path: entry.path(),
            is_dir,
        });
    }
    Ok(Some(entries))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(test: &str) -> PathBuf {
        let dir =
            std::env::temp_dir().join(format!("domino-overwrite-{test}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    fn touch(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    fn occupied(out: &Path, theorems: &[&str]) -> ExportTreeOccupied {
        match check_export_tree(out, theorems) {
            Err(ExportTreeError::Occupied(o)) => o,
            other => panic!("expected a refusal, got {other:?}"),
        }
    }

    #[test]
    fn run_artifacts_are_directories_and_patterns() {
        for rel in [
            "progress/index.html",
            "progress/ec-transcript.jsonl",
            "progress/anything/new.bin",
            "!debug!/Eq_a_b/O/joint.html",
            "Eq_a_b.report.txt",
            "alignment.txt",
        ] {
            assert!(is_run_artifact(Path::new(rel)), "{rel}");
        }
        for rel in [
            "Eq_a_b.ec",
            "Types.ec",
            "notes.txt",
            "invariant.smt2",
            "progress",
            "!debug!",
            "report.txt.bak",
            "sub/progress/index.html",
        ] {
            assert!(!is_run_artifact(Path::new(rel)), "{rel}");
        }
    }

    #[test]
    fn a_missing_or_empty_output_passes() {
        let out = scratch("empty");
        check_export_tree(&out, &["A"]).unwrap();
        std::fs::create_dir_all(out.join("A")).unwrap();
        check_export_tree(&out, &["A"]).unwrap();
        let _ = std::fs::remove_dir_all(&out);
    }

    #[test]
    fn every_offending_file_of_every_theorem_is_listed() {
        let out = scratch("listed");
        touch(&out.join("A/Types.ec"), "");
        touch(&out.join("A/progress/index.html"), "");
        touch(&out.join("A/Eq_x.report.txt"), "");
        touch(&out.join("B/sub/notes.txt"), "");
        touch(&out.join("C/Types.ec"), "");
        let o = occupied(&out, &["A", "B"]);
        assert_eq!(
            o.files,
            vec![
                PathBuf::from("A/Types.ec"),
                PathBuf::from("B/sub/notes.txt")
            ]
        );
        // a run on `A` alone says nothing about `B` and `C`
        std::fs::remove_file(out.join("A/Types.ec")).unwrap();
        check_export_tree(&out, &["A"]).unwrap();
        let _ = std::fs::remove_dir_all(&out);
    }

    #[test]
    fn a_file_directly_in_the_output_directory_refuses() {
        let out = scratch("loose");
        touch(&out.join("Prf.ec"), "");
        touch(&out.join("Eq_l_r.ec"), EQ);
        let o = occupied(&out, &["A"]);
        assert_eq!(
            o.files,
            vec![PathBuf::from("Eq_l_r.ec"), PathBuf::from("Prf.ec")]
        );
        // `--force` writes beside them and discards none of their proofs
        assert_eq!(o.proofs, vec![]);
        let _ = std::fs::remove_dir_all(&out);
    }

    #[test]
    fn an_output_that_is_a_file_refuses() {
        let out = scratch("file-out");
        touch(&out, "");
        let o = occupied(&out, &["A"]);
        assert_eq!(o.files, vec![out.clone()]);
        let _ = std::fs::remove_file(&out);
    }

    #[test]
    fn a_file_where_the_theorem_directory_goes_refuses() {
        let out = scratch("file-theorem");
        touch(&out.join("A"), "");
        let o = occupied(&out, &["A"]);
        assert_eq!(o.files, vec![PathBuf::from("A")]);
        let _ = std::fs::remove_dir_all(&out);
    }

    const EQ: &str = "proof.
call (: inv); last first.

auto => />; smt().

(* O_One *)
+ proc; inline. admit.

(* O_Two *)
+ proc; inline.
  sp 1 1.
  if.
  + smt().
  + auto => /#. (* domino: no admit. here *)

(* O_Three *)
+ proc; inline.
  if.
  + smt().
  + admit. (* domino: J1 invariant; reason: stuck; Domino: verified *)
qed.
";

    #[test]
    fn proof_progress_counts_proved_and_partially_proved_oracles() {
        let counts = |proved, partial, total| OracleCounts {
            proved,
            partial,
            total,
        };
        assert_eq!(proof_progress(EQ), counts(1, 1, 3));
        assert_eq!(
            proof_progress("lemma x : true.\nproof. trivial. qed.\n"),
            counts(0, 0, 0)
        );
    }

    #[test]
    fn proof_progress_does_not_trip_on_empty_comments() {
        let text = "(* *)\n+ proc; inline. admit.\n(**)\n(* a *)\n+ proc. auto.\nqed.\n";
        assert_eq!(proof_progress(text).total, 1);
    }

    #[test]
    fn a_fresh_export_has_every_oracle_unproved() {
        let files = crate::project::DirectoryFiles::load(Path::new("example-projects/hello-world"))
            .unwrap();
        let project = crate::project::DirectoryProject::load(
            PathBuf::from("example-projects/hello-world"),
            &files,
        )
        .unwrap();
        use crate::project::Project;
        let theorem = project.get_theorem("Proof").unwrap();
        let exported = super::super::export::export_theorem(theorem, &project).unwrap();
        let eq = &exported.files[Path::new("Eq_medium_composition_small_composition.ec")];
        assert_eq!(
            proof_progress(eq),
            OracleCounts {
                proved: 0,
                partial: 0,
                total: 1
            }
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_linked_output_directory_is_followed() {
        let base = scratch("linked");
        std::fs::create_dir_all(base.join("real")).unwrap();
        std::os::unix::fs::symlink(base.join("real"), base.join("link")).unwrap();
        check_export_tree(&base.join("link"), &["A"]).unwrap();
        touch(&base.join("real/A/Types.ec"), "");
        let o = occupied(&base.join("link"), &["A"]);
        assert_eq!(o.files, vec![PathBuf::from("A/Types.ec")]);
        let _ = std::fs::remove_dir_all(&base);
    }

    #[test]
    fn the_refusal_says_what_force_would_discard() {
        let out = scratch("discard");
        touch(&out.join("A/Eq_l_r.ec"), EQ);
        touch(&out.join("A/Types.ec"), "");
        let o = occupied(&out, &["A"]);
        assert_eq!(
            o.proofs,
            vec![ProofProgress {
                file: PathBuf::from("A/Eq_l_r.ec"),
                oracles: OracleCounts {
                    proved: 1,
                    partial: 1,
                    total: 3
                },
            }]
        );
        let help = o.help().unwrap().to_string();
        assert!(
            help.contains("A/Eq_l_r.ec: 1 of 3 oracles already proved; --force discards them"),
            "{help}"
        );
        let message = o.to_string();
        assert!(message.contains("  A/Eq_l_r.ec\n  A/Types.ec"), "{message}");
        let _ = std::fs::remove_dir_all(&out);
    }
}
