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
//! - [`SessionRecord`]: `Eq_<L>_<R>.session.json`: statuses, and (story 37) the scripts that
//!   let a job resume the equivalence.
//! - [`remove_session_records`]: what `domino easycrypt --force` does to them.
//! - [`ProofLock`], [`progress_dir`], [`check_no_live_jobs`] (story 36): one job per equivalence.

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
pub fn is_proof_file(rel: &Path) -> bool {
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

/// One `admit` of a done oracle: what the report prints of it, without the goal text.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdmitRecord {
    /// `N<k>`, `J<k>`, `S<k>` or `router`.
    pub node: String,
    /// The reason's slug (`stuck`, `domino-fails`, …).
    pub reason: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub claim: String,
    /// Domino's own verdict's slug (`verified`, `fails`, …).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub domino: String,
}

/// What lockstep execution cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockstepRecord {
    pub joint_paths: usize,
    pub ms: u64,
}

/// The sentences EasyCrypt accepted for one joint node, still in the script, in order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NodeRecord {
    pub id: String,
    pub tactics: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleRecord {
    pub name: String,
    pub status: OracleStatus,
    /// The oracle's bullet exactly as rendered into `Eq_*.ec`: only for `done` oracles of a
    /// version 2 record, and what resuming writes back.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub script: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub admits: Vec<AdmitRecord>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lockstep: Option<LockstepRecord>,
    /// Not used by resuming: kept so node-level resume needs no format change.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub nodes: Vec<NodeRecord>,
}

impl OracleRecord {
    /// An entry with a status and nothing else.
    pub fn new(name: &str, status: OracleStatus) -> Self {
        OracleRecord {
            name: name.to_string(),
            status,
            script: None,
            admits: Vec::new(),
            lockstep: None,
            nodes: Vec::new(),
        }
    }

    /// Done, with the script that resuming writes back.
    pub fn is_resumable(&self) -> bool {
        self.status == OracleStatus::Done && self.script.is_some()
    }
}

/// `Eq_<L>_<R>.session.json`: what each oracle of one equivalence has got to, and enough of
/// its proof to write it back without proving it again (story 37).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionRecord {
    pub version: u32,
    pub theorem: String,
    pub left: String,
    pub right: String,
    /// The Domino version that wrote it (absent in version 1).
    #[serde(default)]
    pub domino: String,
    /// When, RFC 3339 UTC (absent in version 1).
    #[serde(default)]
    pub updated: String,
    /// Every oracle is done.
    pub complete: bool,
    pub oracles: Vec<OracleRecord>,
}

impl SessionRecord {
    pub const VERSION: u32 = 2;

    pub fn new(theorem: &str, left: &str, right: &str, oracles: Vec<OracleRecord>) -> Self {
        SessionRecord {
            version: Self::VERSION,
            theorem: theorem.to_string(),
            left: left.to_string(),
            right: right.to_string(),
            domino: env!("CARGO_PKG_VERSION").to_string(),
            updated: rfc3339_now(),
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

    /// The entry for `name`.
    pub fn oracle(&self, name: &str) -> Option<&OracleRecord> {
        self.oracles.iter().find(|o| o.name == name)
    }

    /// Oracles that are done but have no script (a version 1 record): they cannot be resumed.
    pub fn done_without_script(&self) -> usize {
        self.oracles
            .iter()
            .filter(|o| o.status == OracleStatus::Done && o.script.is_none())
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
        format!(
            "skipping {}: already proved ({} of {} oracles); --force re-proves it",
            stem_of(proof_file),
            self.done(),
            self.oracles.len()
        )
    }

    /// The line printed when a proof job resumes the equivalence this record describes.
    pub fn resume_line(&self, proof_file: &str) -> String {
        format!(
            "resuming {}: {} of {} oracles already proved",
            stem_of(proof_file),
            self.oracles.iter().filter(|o| o.is_resumable()).count(),
            self.oracles.len()
        )
    }

    /// The line printed when a version 1 record's done oracles cannot be resumed.
    pub fn version_1_line(&self, proof_file: &str) -> String {
        format!(
            "{}: the session record has no scripts (written before story 37); its {} proved \
             oracle(s) cannot be resumed and are proved again",
            stem_of(proof_file),
            self.done_without_script()
        )
    }
}

fn stem_of(proof_file: &str) -> &str {
    let stem = proof_file.trim_end_matches(".ec");
    stem.rsplit('/').next().unwrap_or(stem)
}

/// Now, as `YYYY-MM-DDTHH:MM:SSZ`.
fn rfc3339_now() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    rfc3339(secs)
}

/// Unix seconds as `YYYY-MM-DDTHH:MM:SSZ` (days to civil date after Howard Hinnant).
fn rfc3339(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rem / 3600,
        rem % 3600 / 60,
        rem % 60
    )
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

// ----------------------------------------------------------------------------------------
// Story 36: one job per equivalence
// ----------------------------------------------------------------------------------------

/// `<theorem_out>/progress/Eq_<L>_<R>`: everything one proof job writes that is not the proof
/// file, its report or its record: the page, the transcript, the temporary files, the lock.
/// `stem` is the proof file's name without `.ec`.
pub fn progress_dir(theorem_out: &Path, stem: &str) -> PathBuf {
    theorem_out.join("progress").join(stem)
}

/// What a lock file holds: who took it and when (shown to the user, never compared).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct LockContent {
    pid: u32,
    /// Seconds since the Unix epoch.
    started: u64,
}

impl LockContent {
    /// The job this lock text names, if it parses and its pid is alive.
    fn live_job(text: &str, equivalence: &str) -> Option<LiveJob> {
        let c = serde_json::from_str::<LockContent>(text).ok()?;
        pid_is_alive(c.pid).then(|| LiveJob {
            equivalence: equivalence.to_string(),
            pid: c.pid,
            started: c.started,
        })
    }
}

/// A running proof job on `equivalence`, as its lock says.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveJob {
    pub equivalence: String,
    pub pid: u32,
    /// Seconds since the Unix epoch.
    pub started: u64,
}

impl std::fmt::Display for LiveJob {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} is being proved by pid {} (since {})",
            self.equivalence,
            self.pid,
            clock(self.started)
        )
    }
}

#[derive(Debug, thiserror::Error)]
pub enum LockError {
    #[error("{0}; wait for it or stop it")]
    Held(LiveJob),
    #[error(
        "proof jobs are running under this export, and translation would replace files under \
         them (even with `--force`): {}; wait for them or stop them",
        .0.iter().map(|j| j.to_string()).collect::<Vec<_>>().join("; ")
    )]
    JobsRunning(Vec<LiveJob>),
    #[error("cannot take the lock {}: {source}", path.display())]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

/// The lock files this process holds, so that the second Ctrl-C (which exits from a signal
/// handler, without unwinding) can remove them too: [`release_all_locks`].
static HELD: std::sync::Mutex<Vec<PathBuf>> = std::sync::Mutex::new(Vec::new());

/// The lock of one equivalence, `progress/Eq_<L>_<R>/lock`. Removed when dropped, so on every
/// way out of the job the process controls: success, error, skip, the first Ctrl-C.
#[derive(Debug)]
pub struct ProofLock {
    path: PathBuf,
}

impl ProofLock {
    /// Takes the lock of `dir` (the equivalence's progress folder, created if missing).
    ///
    /// The file is created with [`create_if_absent`], holding this process's pid and the start
    /// time. If it exists and its pid is alive, the job is refused ([`LockError::Held`]). If the
    /// pid is dead the lock is stale (a `kill -9`, a crash) and is taken over silently. A pid
    /// that was reused by another process makes a stale lock look live: the start time in the
    /// message is there for the user to judge, nothing more is tried.
    pub fn acquire(dir: &Path, equivalence: &str) -> Result<ProofLock, LockError> {
        let path = dir.join("lock");
        let io = |source| LockError::Io {
            path: path.clone(),
            source,
        };
        let mine = LockContent {
            pid: std::process::id(),
            started: now(),
        };
        let text = serde_json::to_string(&mine).expect("a lock serializes") + "\n";
        for _ in 0..3 {
            if create_if_absent(&path, &text).map_err(io)? {
                HELD.lock().unwrap().push(path.clone());
                return Ok(ProofLock { path });
            }
            let seen = match std::fs::read_to_string(&path) {
                Ok(text) => text,
                // released between the two calls: try again
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                Err(e) => return Err(io(e)),
            };
            if let Some(job) = LockContent::live_job(&seen, equivalence) {
                return Err(LockError::Held(job));
            }
            // stale (or unreadable): remove it, unless somebody replaced it since it was read
            if std::fs::read_to_string(&path).ok().as_deref() == Some(seen.as_str()) {
                match std::fs::remove_file(&path) {
                    Ok(()) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                    Err(e) => return Err(io(e)),
                }
            }
        }
        Err(io(std::io::Error::other("the lock keeps changing hands")))
    }
}

impl Drop for ProofLock {
    fn drop(&mut self) {
        HELD.lock().unwrap().retain(|p| p != &self.path);
        let _ = std::fs::remove_file(&self.path);
    }
}

/// Removes every lock this process holds. For the second Ctrl-C, which ends the process from
/// the signal handler; a normal exit drops the [`ProofLock`]s instead.
pub fn release_all_locks() {
    if let Ok(held) = HELD.lock() {
        for path in held.iter() {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// The jobs under `theorem_out` whose lock names a live pid. Stale locks are ignored.
pub fn live_jobs(theorem_out: &Path) -> std::io::Result<Vec<LiveJob>> {
    let entries = match std::fs::read_dir(theorem_out.join("progress")) {
        Ok(entries) => entries,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e),
    };
    let mut jobs = Vec::new();
    for entry in entries {
        let entry = entry?;
        let Ok(text) = std::fs::read_to_string(entry.path().join("lock")) else {
            continue;
        };
        let name = entry.file_name().to_string_lossy().into_owned();
        jobs.extend(LockContent::live_job(&text, &name));
    }
    jobs.sort_by(|a, b| a.equivalence.cmp(&b.equivalence));
    Ok(jobs)
}

/// Translation's check (story 36 §3.3): refuses, `--force` or not, while a proof job under any
/// of `theorem_outs` holds a live lock.
pub fn check_no_live_jobs(theorem_outs: &[PathBuf]) -> Result<(), LockError> {
    let mut all = Vec::new();
    for out in theorem_outs {
        let theorem = out
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        let jobs = live_jobs(out).map_err(|source| LockError::Io {
            path: out.join("progress"),
            source,
        })?;
        all.extend(jobs.into_iter().map(|mut j| {
            j.equivalence = format!("{theorem}/{}", j.equivalence);
            j
        }));
    }
    if all.is_empty() {
        Ok(())
    } else {
        Err(LockError::JobsRunning(all))
    }
}

fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// `kill(pid, 0)`: the process exists (a process we may not signal counts as alive).
#[cfg(unix)]
fn pid_is_alive(pid: u32) -> bool {
    if pid == 0 || pid > i32::MAX as u32 {
        return false;
    }
    // SAFETY: signal 0 only checks for existence and permission.
    let rc = unsafe { libc::kill(pid as libc::pid_t, 0) };
    rc == 0 || std::io::Error::last_os_error().raw_os_error() == Some(libc::EPERM)
}

#[cfg(not(unix))]
fn pid_is_alive(_pid: u32) -> bool {
    true
}

/// Local `HH:MM` of a Unix time.
#[cfg(unix)]
fn clock(secs: u64) -> String {
    let t = secs as libc::time_t;
    // SAFETY: `tm` is written by `localtime_r`, which only reads `t`.
    let tm = unsafe {
        let mut tm: libc::tm = std::mem::zeroed();
        if libc::localtime_r(&t, &mut tm).is_null() {
            return format!("{secs}");
        }
        tm
    };
    format!("{:02}:{:02}", tm.tm_hour, tm.tm_min)
}

#[cfg(not(unix))]
fn clock(secs: u64) -> String {
    format!("{secs}")
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
        let mut a = OracleRecord::new("A", OracleStatus::Done);
        a.script = Some("+ proc; inline.\n  auto.\n".into());
        a.admits = vec![AdmitRecord {
            node: "N7".into(),
            reason: "stuck".into(),
            claim: "invariant".into(),
            domino: "verified".into(),
        }];
        a.lockstep = Some(LockstepRecord {
            joint_paths: 23,
            ms: 41200,
        });
        a.nodes = vec![NodeRecord {
            id: "N0".into(),
            tactics: vec!["proc.".into(), "inline.".into()],
        }];
        let record = SessionRecord::new(
            "T",
            "L",
            "R",
            vec![
                a,
                OracleRecord::new("B", OracleStatus::Interrupted),
                OracleRecord::new("C", OracleStatus::Pending),
            ],
        );
        assert!(!record.complete);
        assert_eq!(record.version, 2);
        let parsed: SessionRecord = serde_json::from_str(&record.to_json()).unwrap();
        assert_eq!(parsed, record);
        assert!(record.to_json().contains(r#""status": "interrupted""#));
        // only done oracles carry a script
        assert_eq!(record.to_json().matches("\"script\"").count(), 1);
        assert_eq!(
            record.resume_line("Eq_L_R.ec"),
            "resuming Eq_L_R: 1 of 3 oracles already proved"
        );
        let all: Vec<_> = record
            .oracles
            .iter()
            .map(|o| OracleRecord::new(&o.name, OracleStatus::Done))
            .collect();
        let all = SessionRecord::new("T", "L", "R", all);
        assert!(all.complete);
        assert_eq!(
            all.skip_line("Eq_L_R.ec"),
            "skipping Eq_L_R: already proved (3 of 3 oracles); --force re-proves it"
        );
    }

    #[test]
    fn a_version_1_record_reads_with_statuses_only() {
        let text = r#"{"version": 1, "theorem": "T", "left": "L", "right": "R", "complete": false,
            "oracles": [{"name": "A", "status": "done"}, {"name": "B", "status": "pending"}]}"#;
        let record: SessionRecord = serde_json::from_str(text).unwrap();
        assert_eq!(record.version, 1);
        assert_eq!(record.done(), 1);
        assert_eq!(record.done_without_script(), 1);
        assert!(!record.oracles[0].is_resumable());
    }

    #[test]
    fn timestamps_are_rfc_3339() {
        assert_eq!(rfc3339(0), "1970-01-01T00:00:00Z");
        assert_eq!(rfc3339(1_709_210_096), "2024-02-29T12:34:56Z");
        assert_eq!(rfc3339(4_102_444_799), "2099-12-31T23:59:59Z");
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

    /// A pid that certainly belongs to no process: a child that has been waited for.
    fn dead_pid() -> u32 {
        let mut child = std::process::Command::new("true").spawn().unwrap();
        let pid = child.id();
        child.wait().unwrap();
        pid
    }

    fn write_lock(dir: &Path, pid: u32) {
        std::fs::create_dir_all(dir).unwrap();
        let c = LockContent {
            pid,
            started: now(),
        };
        std::fs::write(dir.join("lock"), serde_json::to_string(&c).unwrap()).unwrap();
    }

    #[test]
    fn a_lock_held_by_a_live_pid_refuses_and_names_it() {
        let dir = scratch("lock-live").join("progress/Eq_L_R");
        write_lock(&dir, std::process::id());
        let err = ProofLock::acquire(&dir, "Eq_L_R").unwrap_err();
        let text = err.to_string();
        assert!(
            text.starts_with(&format!(
                "Eq_L_R is being proved by pid {} (since ",
                std::process::id()
            )),
            "{text}"
        );
        assert!(text.ends_with("); wait for it or stop it"), "{text}");
        // the refused job leaves the holder's lock alone
        assert!(dir.join("lock").exists());
    }

    #[test]
    fn a_lock_held_by_a_dead_pid_is_taken_over_and_removed_on_drop() {
        let dir = scratch("lock-dead").join("progress/Eq_L_R");
        write_lock(&dir, dead_pid());
        let lock = ProofLock::acquire(&dir, "Eq_L_R").unwrap();
        let text = std::fs::read_to_string(dir.join("lock")).unwrap();
        let c: LockContent = serde_json::from_str(&text).unwrap();
        assert_eq!(c.pid, std::process::id());
        // and while it is held, a second job is refused
        assert!(matches!(
            ProofLock::acquire(&dir, "Eq_L_R"),
            Err(LockError::Held(_))
        ));
        drop(lock);
        assert!(!dir.join("lock").exists());
    }

    #[test]
    fn an_unreadable_lock_is_stale() {
        let dir = scratch("lock-junk").join("progress/Eq_L_R");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("lock"), "not json").unwrap();
        let lock = ProofLock::acquire(&dir, "Eq_L_R").unwrap();
        assert!(dir.join("lock").exists());
        drop(lock);
        assert!(!dir.join("lock").exists());
    }

    #[test]
    fn translation_sees_live_locks_only() {
        let out = scratch("lock-translation");
        write_lock(&out.join("progress/Eq_A_B"), std::process::id());
        write_lock(&out.join("progress/Eq_C_D"), dead_pid());
        let jobs = live_jobs(&out).unwrap();
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].equivalence, "Eq_A_B");
        let err = check_no_live_jobs(std::slice::from_ref(&out)).unwrap_err().to_string();
        assert!(err.contains("Eq_A_B is being proved by pid"), "{err}");
        assert!(!err.contains("Eq_C_D"), "{err}");
        std::fs::remove_dir_all(out.join("progress/Eq_A_B")).unwrap();
        check_no_live_jobs(std::slice::from_ref(&out)).unwrap();
        check_no_live_jobs(&[out.join("missing")]).unwrap();
    }
}
