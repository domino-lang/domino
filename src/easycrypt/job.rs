// SPDX-License-Identifier: MIT OR Apache-2.0

//! Story 35 (ADR 0006): what a **proof job** may assume about the export tree and what it may
//! touch.
//!
//! A proof job (`domino easycrypt prove`, `check-alignment`) never rewrites a file that belongs
//! to translation or to another equivalence. It looks at translation's files **by name only**:
//! a file that exists is taken to be what translation would have written, and its contents are
//! never read. A missing one is created by [`create_if_absent`], atomically and only if it is
//! still absent, so two jobs racing to create it cannot tear it.
//!
//! - [`create_if_absent`]: the create-if-absent helper.
//! - [`ensure_translation_files`]: every file of the export except the `Eq_*.ec`.
//! - [`SessionRecord`]: `Eq_<L>_<R>.session.json`, the minimal form (story 37 extends it).
//! - [`remove_session_records`]: what `domino easycrypt --force` does to them.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde_derive::{Deserialize, Serialize};

use crate::writers::easycrypt::export::ExportedTheorem;

/// Creates `path` holding `text`, unless it already exists. Returns whether this call created
/// it.
///
/// The text goes to a temporary file in the same directory first, which is then hard-linked to
/// `path`: a link fails when the target exists, so this never replaces a file, and a concurrent
/// reader never sees half a file. If the link fails because another job created the file first,
/// that is success (`Ok(false)`). Never a `rename`, which replaces.
pub fn create_if_absent(path: &Path, text: &str) -> std::io::Result<bool> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let dir = path
        .parent()
        .filter(|d| !d.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    std::fs::create_dir_all(dir)?;
    let name = path.file_name().expect("a file path").to_string_lossy();
    let tmp = dir.join(format!(
        ".{name}.{}.{}.tmp",
        std::process::id(),
        COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let written = (|| {
        let mut file = std::fs::File::create(&tmp)?;
        file.write_all(text.as_bytes())?;
        file.sync_all()
    })();
    let linked = written.and_then(|()| std::fs::hard_link(&tmp, path));
    let _ = std::fs::remove_file(&tmp);
    match linked {
        Ok(()) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => Ok(false),
        Err(e) => Err(e),
    }
}

/// Whether `rel` is one equivalence's proof file, which its own job owns.
fn is_proof_file(rel: &Path) -> bool {
    rel.file_name()
        .and_then(|n| n.to_str())
        .is_some_and(|n| n.starts_with("Eq_") && n.ends_with(".ec"))
}

/// Creates, in `theorem_out`, every file of `exported` that translation owns (all but the
/// `Eq_*.ec`) and that is missing, one line on stderr each. Files that exist are not read.
/// Returns the relative paths created.
pub fn ensure_translation_files(
    exported: &ExportedTheorem,
    theorem_out: &Path,
) -> std::io::Result<Vec<PathBuf>> {
    let mut created = Vec::new();
    for (rel, text) in &exported.files {
        if is_proof_file(rel) {
            continue;
        }
        if create_if_absent(&theorem_out.join(rel), text)? {
            eprintln!("created {} (missing from the translation)", rel.display());
            created.push(rel.clone());
        }
    }
    Ok(created)
}

/// The record's name for a proof file: `Eq_L_R.ec` gives `Eq_L_R.session.json`.
pub fn session_record_name(proof_file: &str) -> String {
    format!("{}.session.json", proof_file.trim_end_matches(".ec"))
}

/// How far proving one oracle got.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OracleStatus {
    /// Ended without an `interrupted` admit (admits with any other reason count as done).
    Done,
    /// Sealed by a stop.
    Interrupted,
    /// Not reached.
    Pending,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleRecord {
    pub name: String,
    pub status: OracleStatus,
}

/// `Eq_<L>_<R>.session.json`, the minimal form: what skip and `--force` need.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionRecord {
    pub version: u32,
    pub theorem: String,
    pub left: String,
    pub right: String,
    /// Every oracle is done.
    pub complete: bool,
    pub oracles: Vec<OracleRecord>,
}

impl SessionRecord {
    pub const VERSION: u32 = 1;

    pub fn new(theorem: &str, left: &str, right: &str, oracles: Vec<OracleRecord>) -> Self {
        SessionRecord {
            version: Self::VERSION,
            theorem: theorem.to_string(),
            left: left.to_string(),
            right: right.to_string(),
            complete: oracles.iter().all(|o| o.status == OracleStatus::Done),
            oracles,
        }
    }

    pub fn done(&self) -> usize {
        self.oracles
            .iter()
            .filter(|o| o.status == OracleStatus::Done)
            .count()
    }

    pub fn to_json(&self) -> String {
        let mut text = serde_json::to_string_pretty(self).expect("a record serializes");
        text.push('\n');
        text
    }

    /// The record at `path`: `Ok(None)` when there is none.
    pub fn read(path: &Path) -> Result<Option<SessionRecord>, SessionRecordError> {
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(source) => {
                return Err(SessionRecordError::Read {
                    path: path.to_path_buf(),
                    message: source.to_string(),
                })
            }
        };
        serde_json::from_str(&text)
            .map(Some)
            .map_err(|source| SessionRecordError::Read {
                path: path.to_path_buf(),
                message: source.to_string(),
            })
    }

    /// The line printed when a proof job skips the equivalence this record describes.
    pub fn skip_line(&self, proof_file: &str) -> String {
        let stem = proof_file.trim_end_matches(".ec");
        let stem = stem.rsplit('/').next().unwrap_or(stem);
        let counts = format!("{} of {} oracles", self.done(), self.oracles.len());
        if self.complete {
            format!("skipping {stem}: already proved ({counts}); --force re-proves it")
        } else {
            format!(
                "skipping {stem}: already proved ({counts}, resuming arrives with story 37); \
                 --force re-proves it"
            )
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SessionRecordError {
    #[error(
        "cannot read the session record {}: {message} (it is not meant to be edited; `--force` \
         discards it)",
        path.display()
    )]
    Read { path: PathBuf, message: String },
}

/// Deletes every `*.session.json` under `theorem_out` (translation with `--force`: the proofs
/// they describe are overwritten by skeletons). Returns how many were deleted.
pub fn remove_session_records(theorem_out: &Path) -> std::io::Result<usize> {
    let mut removed = 0;
    let mut stack = vec![theorem_out.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match std::fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => return Err(e),
        };
        for entry in entries {
            let entry = entry?;
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                stack.push(path);
            } else if path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with(".session.json"))
            {
                std::fs::remove_file(&path)?;
                removed += 1;
            }
        }
    }
    Ok(removed)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(test: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("domino-job-{test}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    #[test]
    fn two_threads_creating_the_same_file_both_succeed_and_it_holds_one_complete_copy() {
        let dir = scratch("race");
        let text = "line of text\n".repeat(200_000);
        for round in 0..20 {
            let path = dir.join(format!("Types{round}.ec"));
            let created: Vec<bool> = std::thread::scope(|s| {
                let handles: Vec<_> = (0..2)
                    .map(|_| s.spawn(|| create_if_absent(&path, &text).unwrap()))
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            assert_eq!(created.iter().filter(|c| **c).count(), 1, "one creator");
            assert_eq!(std::fs::read_to_string(&path).unwrap(), text);
        }
        // no temporary file is left behind
        let leftovers: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n.to_string_lossy().ends_with(".tmp"))
            .collect();
        assert!(leftovers.is_empty(), "{leftovers:?}");
    }

    #[test]
    fn an_existing_file_is_never_replaced_or_read() {
        let dir = scratch("existing");
        let path = dir.join("Types.ec");
        assert!(create_if_absent(&path, "first").unwrap());
        assert!(!create_if_absent(&path, "second").unwrap());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "first");
    }

    #[test]
    fn the_record_round_trips_and_says_what_it_holds() {
        let record = SessionRecord::new(
            "T",
            "L",
            "R",
            vec![
                OracleRecord {
                    name: "A".into(),
                    status: OracleStatus::Done,
                },
                OracleRecord {
                    name: "B".into(),
                    status: OracleStatus::Interrupted,
                },
                OracleRecord {
                    name: "C".into(),
                    status: OracleStatus::Pending,
                },
            ],
        );
        assert!(!record.complete);
        let parsed: SessionRecord = serde_json::from_str(&record.to_json()).unwrap();
        assert_eq!(parsed, record);
        assert!(record.to_json().contains(r#""status": "interrupted""#));
        assert_eq!(
            record.skip_line("Eq_L_R.ec"),
            "skipping Eq_L_R: already proved (1 of 3 oracles, resuming arrives with story 37); \
             --force re-proves it"
        );
        let mut all = record.clone();
        for o in &mut all.oracles {
            o.status = OracleStatus::Done;
        }
        let all = SessionRecord::new("T", "L", "R", all.oracles);
        assert!(all.complete);
        assert_eq!(
            all.skip_line("Eq_L_R.ec"),
            "skipping Eq_L_R: already proved (3 of 3 oracles); --force re-proves it"
        );
    }

    #[test]
    fn removing_records_deletes_every_session_json_under_the_directory_and_nothing_else() {
        let dir = scratch("remove");
        std::fs::create_dir_all(dir.join("sub")).unwrap();
        for f in [
            "Eq_A_B.session.json",
            "sub/Eq_C_D.session.json",
            "Eq_A_B.ec",
        ] {
            std::fs::write(dir.join(f), "x").unwrap();
        }
        assert_eq!(remove_session_records(&dir).unwrap(), 2);
        assert!(dir.join("Eq_A_B.ec").exists());
        assert!(!dir.join("Eq_A_B.session.json").exists());
        assert_eq!(remove_session_records(&dir.join("missing")).unwrap(), 0);
    }
}
