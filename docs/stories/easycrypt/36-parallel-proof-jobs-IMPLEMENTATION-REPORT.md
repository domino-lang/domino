# Story 36 — implementation report

## What changed

- **`src/easycrypt/job.rs`**: the lock and the per-equivalence folder.
  - `progress_dir(theorem_out, stem)` gives `progress/Eq_<L>_<R>/`.
  - `ProofLock::acquire(dir, name)` creates `lock` with `create_if_absent`. It holds `{"pid", "started"}` (Unix seconds).
    - A live pid (`kill(pid, 0)`; `EPERM` counts as alive) refuses with `Eq_L_R is being proved by pid 4711 (since 14:02); wait for it or stop it`.
    - A dead pid, or a lock that cannot be parsed, is taken over silently. The stale file is removed only if it is unchanged since it was read.
    - Dropping the `ProofLock` removes the file, so every way out that unwinds or returns releases it.
  - `release_all_locks()` removes the locks this process holds. A registry (`HELD`) backs it, and the second Ctrl-C calls it because that path exits from the signal handler.
  - `live_jobs` and `check_no_live_jobs` list the live locks under theorem directories, for translation.
  - `is_proof_file` is now public. `libc` is a new dependency of the library crate (it was already in the lockfile).
- **`tactics/mod.rs`**: `run_tactics_observed` is now a loop of proof jobs.
  - Per selected equivalence, in this order: create `progress/Eq_L_R/`, take the lock, decide skip or `--force` (`plan_job`, which replaces `plan_jobs`), create missing translation files, create the transcript, build a `LiveHandle` with its own page, run, write the page's last state, release the lock.
  - The lock is taken and released per equivalence. A skipped equivalence releases the lock at once, and its folder is removed if the skip left it empty.
  - The transcript and page are per job. `TheoremTactics::transcript` is gone; `EquivalenceTactics::transcript` replaces it, and `TheoremTactics::render` prints one `transcript:` line per equivalence.
  - `ProofFile` and the `--force` restart write their temporary files (`write_atomically`) in the job's own folder. The page's `index.html.tmp` was already beside the page, so it is in the job's folder too.
  - The signature changed: `phases` is gone, and `progress` is now `&mut dyn FnMut() -> Box<dyn ExportObserver>`, called once per equivalence that is proved.
  - `TacticsError::Lock` carries a refusal. A refusal on the second equivalence of a sequential run is an error too, and stops the run after the first one's results are written.
- **`live/`**: `LiveConfig::phases` is replaced by `translation`, one line. The page shows `translation files: all N present, trusted as they are`, with `; created: …` when the job created files. The theorem-level page no longer exists.
- **`main.rs`**: translation calls `check_no_live_jobs` before anything else, `--force` or not. It runs after the ADR 0004 tree check and before the export. `stop_on_ctrl_c`'s second press calls `release_all_locks`. `LockError` is reported as an error.

## Verification

- Unit tests (`job::tests`):
  - a live pid refuses, with the specified message, and leaves the holder's lock alone;
  - a dead pid is taken over, a second job is refused while it is held, and drop removes the file;
  - an unparseable lock is stale;
  - translation sees live locks only, and a missing directory is fine.
- `easycrypt_ctrl_c.rs` (stand-in EasyCrypt, no real one needed):
  - the lock is gone after the first Ctrl-C and after the second;
  - the lock is gone after an error (`--oracle NoSuchOracle`);
  - a live holder (a `sleep`) refuses `prove` with its pid and leaves no transcript;
  - translation with `--force` is refused, naming the job;
  - after the holder is killed with SIGKILL, a new `prove` takes the lock over (its pid is in the file);
  - after that job is stopped, translation with `--force` works again.
- `easycrypt_prove.rs` (real EasyCrypt, skipped without `DOMINO_EASYCRYPT`): `two_proof_jobs_on_different_equivalences_run_at_once` starts two `prove` processes together on two equivalences of one theorem.
  - Both finish. Each `Eq_*.ec` holds a proof, and each folder has a page and a transcript whose every record names only its own file.
  - No lock is left.
  - It takes about 3 minutes (debug build).
- Existing tests were updated for the new paths (`progress/Eq_<L>_<R>/index.html`, `ec-transcript.jsonl`). The ordering test also checks that the job's folder holds `index.html` and the transcript, and no `.tmp` and no `lock`.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean, except `src/debug/sweep.rs:199` (collapsible `if`), which is older than this story.
- Full suite (`DOMINO_EASYCRYPT` an absolute path to `easycrypt/ec.native` of this worktree):
  - without `cvc5-lib`: all pass (531 passed, 5 ignored in the library tests);
  - with `--features cvc5-lib`: all pass (615 passed, 6 ignored in the library tests).
- Peak memory of two parallel jobs on `kem-dem-cpa-blended-parallel-single-challenge` (`Eq_CPA_PKE_H0` and `Eq_H1_H2`, debug build).
  - There is no two-equivalence variant of `kem-dem-cca-ssp`: it has one equivalence, the other hops are reductions. The story's `--proofstep 0` and `1` do not both name equivalences here either, so 0 and 2 were used.
  - Wall time was 185 s for the longer job, and 61 s for the other one. Sampled 20 s in, the resident sets were about 68 MB and 80 MB for the two `domino` processes and 225 MB and 283 MB for the two `ec.native` processes, about 660 MB together.
  - The `domino` processes' peak footprints were 108 MB and 99 MB.
  - The `cvc5` solver runs inside `domino` (`cvc5-lib`), so it is counted there. Memory is not the limit at this size.

## §3.4 What a proof job writes under the theorem directory

Checked on a finished two-job run. Every file newer than `Types.ec` is one of:

- its own `Eq_*.ec`, `Eq_*.report.txt` and `Eq_*.session.json`;
- `!debug!/<L>-<R>/…`;
- `progress/Eq_<L>_<R>/…`.

The only shared writes are the missing translation files, which use `create_if_absent` and so cannot tear. EasyCrypt writes no `.eco` files next to the sources (ADR 0005). `check-alignment` still writes one `alignment.txt` per theorem, as the story says it should not be made parallel-safe here.

## State handed to the next story

- One job per equivalence at a time holds while every job runs on a machine where the pid check works (see the pid reuse note). Story 37 can read and write the session record inside the lock.
- `run_tactics_observed`'s per-equivalence body is the place to add a resume: `plan_job` is where a partial record turns into one.

## Deviations and notes

- **Refusal while running a sequence.** `prove` without `--proofstep` fails when a later equivalence is locked by another process, after the earlier ones are done and reported. The story says "refuse" without saying more.
- **Takeover race.** Two jobs that both find the same stale lock can still both take it: one removes the stale file and creates its own, and the other, having read the stale contents earlier, removes only if the file is unchanged, which narrows the window without closing it. The story says not to be clever.
- **pid reuse** can make a stale lock look live. The message shows the start time for the user to judge, as in §6.
- **A kill by SIGTERM or SIGHUP** leaves a stale lock, which the next job takes over.
- **An empty folder.** A job that fails before the transcript is created leaves an empty `progress/Eq_L_R/` behind.
- **`--oracle` validation** happens after the transcript and page exist, so a typo leaves a page saying the run failed. This is the behaviour of story 35's order, kept.
- `easycrypt_ctrl_c.rs`'s first lines were already unformatted for `rustfmt`; the new code there was not reformatted either, to keep the diff small.
- `LoggingExportObserver::into_log` and `PhaseLog::phases_of` are no longer used by `main`; they stay, with their tests.

## Code review

- Spec review, findings addressed or recorded:
  - The §3.4 audit and the memory figures were in this report already (written while the review ran).
  - ADR 0006 now records the lock (a consequence bullet).
  - The takeover race and the short window before the lock (the in-memory export, about 0.3 s, runs first) are recorded above. Closing them needs `flock` or a rename protocol, which §6 rules out.
  - The sequential path (`prove` without `--proofstep`) has no test of its own. Its per-equivalence lock is the same code as the single-equivalence path.
  - The summary output changed (one `transcript:` line per equivalence, a separate `elapsed:` line). That follows from the transcript being per equivalence.
- Standards review: no hard violation in code. Fixed: the lock text is parsed in one place (`LockContent::live_job`), which `acquire` and `live_jobs` share.
  - `CONTEXT.md` lacks a term for the lock. It has uncommitted edits that are not this story's, so it is left for its owner.
  - Left as judgement calls: splitting `run_tactics_observed`'s loop body into its own function, moving `translation_line` into `job.rs`, a typed `LiveJob`, and a `cfg(not(unix))` liveness check that always says alive.
