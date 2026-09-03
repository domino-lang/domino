# Story 09 — Live exploration progress for `domino debug`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 06 (`src/debug/driver.rs`), story 07 (`src/debug/report.rs`).
**Interacts with:** story 08 (branch-level pruning) — independent, but this story adds one event
variant story 08 populates. Order between 08 and 09 does not matter; whichever lands second wires
the other's hook (§3.6).
**Blocks:** nothing.

---

## 1. Why this story exists

`domino debug` runs **completely silently**. `run_debug_command` (`src/debug/driver.rs:334`)
collects every left path up front, then loops every `(left, right)` terminal pair firing one or
two `check-sat`s each, and only when the whole exploration has finished does `crates/domino/src/main.rs:168`
do `print!("{}", render_tree(&run))` and write `index.html`.

On the epic's primary target that is a long, blank wait:

| oracle | left paths | right paths | `check-sat`s | typical wall-clock |
|---|---|---|---|---|
| `PKGEN` | 2 | 6 | ~14 | seconds |
| `PKDEC` | 5 | 65 | ~130 | tens of seconds |
| `PKENC` | 6 | 96 | ~194 | tens of seconds to minutes |

During that time the user has no idea whether the tool is making progress, how far along it is,
or whether it has already found a `GOAL FAILS`. And a `Ctrl-C` (or hitting `--max-paths`) throws
away **everything** explored so far — no `trace.json`, no `index.html`, nothing.

### What the owner asked for

> Create a story so I see the progress of paths being explored during debugging.

Settled in the kickoff (do not relitigate):

| Decision | Choice |
|---|---|
| **Render style** | A `--progress auto\|plain\|bar\|none` flag. `auto` = an `indicatif` bar when stderr is a terminal, plain stderr log lines when piped/redirected. `bar` / `plain` force one; `none` restores today's silence. |
| **Granularity** | Per pair / per `check-sat`. Every `(left, right)` pair produces a progress update, not just every left path — a 30-second right-side sweep must not look stalled. |
| **Scope** | Console progress **plus** partial artifacts: `trace.json` and `index.html` are flushed as the run proceeds, so `Ctrl-C` / `--max-paths` leaves a usable partial trace and viewer. |
| **Channel** | Progress goes to **stderr**. stdout stays exactly the final `render_tree` text so `domino debug … | tee` and scripting are unaffected. |
| **Verdict semantics** | Unchanged. This story adds observability only — same paths, same solver calls, same verdicts, same exit code. |

## 2. Inherited from earlier stories — read this before touching anything

### 2.1 The driver — `src/debug/driver.rs` (story 06 / 07)

```rust
pub fn run_debug_command<P, B>(
    project: &P, req_proof: &str, req_proofstep: usize,
    oracle: &str, claim_name: &str,
    opts: &DebugOptions, backend: &B, out: Option<PathBuf>,
) -> Result<DebugRun, DebugError>
where P: Project, B: SmtSolverBackend;                                  // :334
```

- `run_debug_command` builds `run: DebugRun` (`:453`), asserts the base frame, opens the
  transcript-backed solver, calls `explore_paths(…, &mut run)` (`:491`), then **after it returns**
  writes `inlined.txt`, `trace.json` and `index.html` (`:499-504`).
- `explore_paths` (`:540`): `collect_paths` for the left side (`:555`), then
  `'left: for (i, lp) in left_paths.iter().enumerate()` (`:563`):
  - `explored += 1`; bail to `run.partial = true` if `explored > opts.max_paths` (`:565`).
  - `solver.push()`, `write_path(solver, lp)` (`:571-572`).
  - optional `check_left` reachability check → `reachable` (`:574-578`).
  - build `LeftPath` view (`:580`).
  - if `reachable`: `collect_paths` for the right side (`:590`), then
    `for (j, rp) in right_paths.iter().enumerate()` (`:596`): `explored += 1`, cap check,
    `solver.push()`, `write_path`, `check_pair` → `(verdict, model_smt)` (`:606-609`),
    `solver.pop()`, push a `RightPath` view.
  - `solver.pop()`; `run.left_paths.push(left_view)` (`:623-624`).
  - **`run.summary = summarize(&run.left_paths)` is set once, at the very end (`:627`).**
- `check_pair` (`:634`) does the vacuity `check-sat` (unless `--no-check-right`) then the negated
  goal `check-sat`; returns `(Verdict, Option<String>)`.
- `render_tree(run: &DebugRun) -> String` (`:775`) — the stdout tree printer. Pure function of
  the finished `DebugRun`.
- `summarize(left_paths: &[LeftPath]) -> Summary` (`:748`) — pure, cheap, idempotent. Safe to
  call repeatedly on a growing `run.left_paths`.

### 2.2 The serialised shape — `DebugRun` (story 07)

```rust
pub const TRACE_SCHEMA: u32 = 1;                                        // driver.rs:142

pub struct DebugRun {
    pub schema: u32, pub theorem: String, pub proofstep: usize,
    pub left_game: String, pub right_game: String,
    pub oracle: String, pub claim: String, pub admitted: bool,
    #[serde(skip)] pub out_dir: String,
    pub options: OptionsView,
    pub base_frame_smt: String,
    pub left_listing: String, pub right_listing: String,
    pub left_sites: BTreeMap<Label, SiteView>,
    pub right_sites: BTreeMap<Label, SiteView>,
    pub left_paths: Vec<LeftPath>,
    pub summary: Summary,
    pub partial: bool,                                                  // already exists
}

pub struct Summary {                                                   // :306
    pub left_paths, left_pruned, right_paths,
        verified, unreachable, goal_fails, inconclusive: usize,
}
pub enum Verdict { Verified, Unreachable, GoalFails { model }, Inconclusive { model } }  // :293
```

- `DebugRun` and every view type already `#[derive(Serialize)]`.
- Story 07's **determinism guarantee**: `trace.json` + `index.html` are byte-identical across
  runs (serde field order, `BTreeMap`, no timestamps, `out_dir` skipped). Intermediate flushes in
  this story are simply overwritten by later ones; the *final* bytes are unchanged, so the
  guarantee holds. **Do not put elapsed time or a timestamp into `DebugRun`.**
- `report::write_trace_json(run, out_dir)` and `report::write_html(run, out_dir)`
  (`src/debug/report.rs:22`, `:33`) are the two flush functions. Both take `&DebugRun`, are pure
  w.r.t. process state, and truncate-write their file. `write_html` for `PKENC` is ~3.7 MB
  (`base_frame_smt` dominates and is fixed from the start).

### 2.3 The existing progress-UI pattern — `src/ui/` (used by `prove`)

`indicatif = "0.18"` and `indicatif-log-bridge = "0.2"` are **already** dependencies
(`Cargo.toml:36-37`). `src/ui/mod.rs` defines a `TheoremUI` trait; `src/ui/indicatif.rs`
implements it over a `MultiProgress` with nested `ProgressBar`s and a `LogWrapper` so `log::`
output does not corrupt the bars; `src/ui/mock.rs` is a test double. `MultiProgress` already
no-ops its drawing when stderr is not a terminal, but we still choose plain-vs-bar explicitly so
the *plain* path emits real log lines rather than nothing.

This story follows the same shape (trait + indicatif impl + plain impl + nop test double) but
for the debug driver, and keeps it in `src/debug/`.

### 2.4 CLI — `crates/domino/src/cli.rs`, `main.rs`

`struct Debug` (`cli.rs`) has `path, proof, proofstep, oracle, claim, check_left, no_check_right,
timeout, max_paths, out`. `fn debug(d: &Debug)` (`main.rs:135`, `#[cfg(feature = "cvc5-lib")]`)
builds `DebugOptions`, a `Cvc5LibBackend`, calls `run_debug_command`, then
`print!("{}", render_tree(&run))` and `println!("\nviewer: {}/index.html", run.out_dir)`, and
returns `Err(DebugNotVerified)` when `!run.is_ok()`.

## 3. Work to do

### 3.1 `src/debug/progress.rs` — the observer trait (new file)

`pub mod progress;` in `src/debug/mod.rs`.

```rust
use std::time::Duration;
use crate::debug::driver::{Summary, Verdict};
use crate::debug::exec::Side;

/// A structured event emitted by [`run_debug_command`] as it explores. The
/// driver borrows its strings from the in-flight `DebugRun`; an observer that
/// needs to keep one must clone.
#[non_exhaustive]
pub enum DebugEvent<'a> {
    /// Emitted once, before any solver work. `admitted` runs emit this then
    /// `Finished` and nothing between.
    Started { oracle: &'a str, claim: &'a str, admitted: bool },

    /// All left terminal paths have been enumerated. `capped` == the executor
    /// hit `--max-paths` while enumerating.
    LeftPathsCollected { total: usize, capped: bool },

    /// Starting to explore left path `index` (1-based) of `total`.
    LeftPathStarted { index: usize, total: usize, id: &'a str },

    /// `--check-left` proved this left path unreachable; its right side is
    /// skipped.
    LeftPathPruned { id: &'a str },

    /// The right terminal paths under the current left path have been
    /// enumerated. Emitted once per explored left path.
    RightPathsCollected { total: usize },

    /// One `(left, right)` terminal pair has been classified.
    PairChecked { id: &'a str, verdict: &'a Verdict, elapsed: Duration },

    /// A branch was pruned before descending into it. **Story 08 only** — the
    /// driver never emits this until story 08's `SolverPruner` is wired to call
    /// `observer.on_event` (§3.6). Observers must handle it as a no-op-friendly
    /// counter today.
    BranchPruned { side: Side, id: &'a str, label: usize },

    /// Left path `index` and its whole right subtree are done. `running` is the
    /// summary of everything classified so far.
    LeftPathFinished { index: usize, running: Summary },

    /// Exploration stopped (naturally, by `--max-paths`, or by `Ctrl-C`).
    Finished { summary: Summary, partial: bool },
}

pub trait DebugObserver {
    fn on_event(&mut self, event: &DebugEvent<'_>);
}

/// The default: does nothing. Library callers and tests pass this.
pub struct NopObserver;
impl DebugObserver for NopObserver {
    fn on_event(&mut self, _: &DebugEvent<'_>) {}
}
```

Design notes to put in the module docs:

- **The driver's behaviour is identical whether an observer is supplied or not.** Events are
  emitted at points the driver already passes through; no solver call, path, or verdict depends
  on the observer. A panicking observer is a bug in the observer, not the driver — do not
  `catch_unwind`.
- `Side` is re-exported from `crate::debug::exec`. `Summary` / `Verdict` from
  `crate::debug::driver`.
- `#[non_exhaustive]` on `DebugEvent` so story 08 (or later) can add variants without a breaking
  change; every `match` in this story's consumers ends in `_ => {}`.

### 3.2 `src/debug/progress.rs` — two consumers

#### `PlainObserver` — line-oriented stderr log

Writes to `std::io::Stderr`. One line per event, terse, greppable. Example transcript:

```
debug: PKENC / same-output — exploring
debug: 6 left paths
debug: left 1/6 (#1) …
debug:   12 right paths
debug:   #1.1  unreachable   0.08s
debug:   #1.2  verified      0.24s
debug:   … 8 verified, 3 unreachable, 1 GOAL FAILS  [running: 1 fail]
debug: left 2/6 (#2) …
…
debug: done — 6 left, 96 right; 2 verified, 93 unreachable, 1 GOAL FAILS, 0 inconclusive (partial: no)
```

- Print **every** `PairChecked` (per-pair granularity is the requirement). Keep each to one line.
- `LeftPathFinished` prints a per-left-path rollup with the running totals.
- Colour: none. This is for logs and CI.

#### `BarObserver` — `indicatif`

A `MultiProgress` with two bars plus a message line:

```
left  ▕████████░░░░░░░░▏ 3/6
pairs ▕██████████████░░▏ 71/96   ✓2  ·93  ✗1  ?0   0:38
```

- Bar 1 (`left`): length = `total` from `LeftPathsCollected`, position = `index`.
- Bar 2 (`pairs`): length reset on each `RightPathsCollected` to its `total`, position bumped on
  each `PairChecked`. On `LeftPathPruned` leave it empty with a `pruned` message.
- The suffix message carries the running tallies (`verified` / `unreachable` / `goal_fails` /
  `inconclusive`) and `indicatif`'s elapsed timer. Update it on every `PairChecked` from the
  `running` you accumulate (or recompute cheaply).
- Use `indicatif-log-bridge`'s `LogWrapper` exactly as `src/ui/indicatif.rs:30-33` does, so any
  `log::warn!` from the solver layer does not tear the bars. (If `LogWrapper::try_init` was
  already called — e.g. `prove` in the same process, which never happens for `debug` — swallow
  the error.)
- On `Finished`: `MultiProgress::clear()`. `main.rs` then prints the tree to stdout with a clean
  terminal.
- When stderr is not a terminal `indicatif` draws nothing — but `main.rs` never constructs a
  `BarObserver` in that case anyway (§3.4), so `bar` forced on a pipe just goes quiet, which is
  acceptable and documented.

Keep `GoalFails` visible: on the first `PairChecked` with a `GoalFails` verdict, `println!`
(via `MultiProgress::println`) a `⚠ GOAL FAILS at #<id>` line above the bars so the user sees it
immediately instead of only in the final tree.

### 3.3 `src/debug/driver.rs` — emit events + flush incrementally

#### Signature change

```rust
pub fn run_debug_command<P, B>(
    project: &P, req_proof: &str, req_proofstep: usize,
    oracle: &str, claim_name: &str,
    opts: &DebugOptions, backend: &B, out: Option<PathBuf>,
    observer: &mut dyn DebugObserver,          // NEW — pass `&mut NopObserver` for none
    stop: Option<&std::sync::atomic::AtomicBool>,  // NEW — `Ctrl-C` flag, `None` = never stops
) -> Result<DebugRun, DebugError>
```

Every existing call site (tests in `driver.rs`, any doctest) passes `&mut NopObserver, None`.
There is no `Option<&mut dyn DebugObserver>` — `NopObserver` is the null object and keeps the
call sites and the `explore_paths` body branch-free.

Thread `observer` and `stop` into `explore_paths` (add two params).

#### Events in `explore_paths` / `run_debug_command`

| Point | Event |
|---|---|
| top of `run_debug_command`, after claim resolved | `Started { oracle, claim, admitted: claim.is_admitted() }` |
| admitted claim (the `if !claim.is_admitted()` is false) | go straight to `Finished { summary: Summary::default(), partial: false }` and return |
| after `collect_paths` for the left side (`:555`) | `LeftPathsCollected { total: left_paths.len(), capped: left_capped }` |
| top of the `'left` loop body, after `lid` (`:569`) | `LeftPathStarted { index: i + 1, total: left_paths.len(), id: &lid }` |
| when `!reachable` (`:589` else) | `LeftPathPruned { id: &lid }` |
| after `collect_paths` for the right side (`:590`) | `RightPathsCollected { total: right_paths.len() }` |
| after each `check_pair` returns (`:609`) | `PairChecked { id: &rid, verdict: &verdict, elapsed }` — time it with `Instant::now()` around the `check_pair` call |
| after `run.left_paths.push(left_view)` (`:624`) | recompute `run.summary = summarize(&run.left_paths)`; emit `LeftPathFinished { index: i + 1, running: run.summary }`; **flush** (§3.5) |
| end of `explore_paths` (`:627`) | `run.summary = summarize(&run.left_paths)` (already there) |
| end of `run_debug_command`, after the final `write_trace_json` / `write_html` | `Finished { summary: run.summary, partial: run.partial }` |

`elapsed` for `PairChecked` is just the `check_pair` duration — cheap, and enough to show which
pairs are slow. Do not thread `Instant`s any deeper.

#### `Ctrl-C` / stop flag

At the top of the `'left` loop body **and** the top of the right-path `for` loop, check
`stop.map_or(false, |s| s.load(Ordering::Relaxed))`. When set:

```rust
run.partial = true;
solver.pop()?;                       // if inside a left push
run.left_paths.push(left_view);      // keep the partial left view
break 'left;
```

then fall through to the normal end-of-function flush. Net effect: a `Ctrl-C` leaves
`trace.json` / `index.html` reflecting every left path that finished plus the partially-explored
current one, and `render_tree` prints what there is with the `partial` marker.

The `stop` check is deliberately coarse (per pair, not mid-`check-sat`) — a single cvc5 call can
still take seconds after `Ctrl-C`; that is acceptable and matches how `prove` behaves. Do not try
to cancel an in-flight solver call.

### 3.4 `src/debug/report.rs` — nothing structural, one guard

`write_trace_json` / `write_html` are called mid-run now. They already truncate-write. The only
addition: a tiny helper the driver calls,

```rust
/// Write `trace.json` and `index.html` for the run so far. Called after every
/// left path and once at the end. Errors are surfaced (a failing flush is a real
/// problem — out of disk, bad path).
pub fn flush(run: &DebugRun, out_dir: &Path) -> std::io::Result<()> {
    write_trace_json(run, out_dir)?;
    write_html(run, out_dir)?;
    Ok(())
}
```

Move the two `report::write_*` calls at `driver.rs:503-504` to go through `report::flush`, and
call `report::flush` from inside `explore_paths` after each `LeftPathFinished`.

**`inlined.txt`** stays a single end-of-run write (`driver.rs:499`) — it is static from the start
and not worth rewriting each left path.

**IO cost.** `PKENC` flushes ~3.7 MB × 6 = ~22 MB over a run that already does ~194 `check-sat`s;
negligible. If a fixture ever makes this hurt, gate the flush on "≥ 1 s since the last one" — but
do **not** add that unless a measured run shows it matters, and say so in the report.

**Schema.** No change to the serialised shape → `TRACE_SCHEMA` stays `1` (or whatever story 08
left it at, if 08 landed first). Note in `docs/stories/07-…md` that flushes are now incremental.

### 3.5 `crates/domino` — the `--progress` flag and observer construction

`cli.rs`:

```rust
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ProgressMode { Auto, Plain, Bar, None }

// in `struct Debug`:
/// Live progress while exploring, on stderr (stdout stays the final tree):
/// `auto` shows a bar on a terminal and plain log lines when piped; `plain`
/// and `bar` force one; `none` is silent.
#[clap(long, value_enum, default_value_t = ProgressMode::Auto)]
pub(crate) progress: ProgressMode,
```

`main.rs` `fn debug`:

```rust
use std::io::IsTerminal;
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use sspverif::debug::progress::{BarObserver, PlainObserver, NopObserver, DebugObserver};

let mut observer: Box<dyn DebugObserver> = match d.progress {
    ProgressMode::None  => Box::new(NopObserver),
    ProgressMode::Plain => Box::new(PlainObserver::new()),
    ProgressMode::Bar   => Box::new(BarObserver::new()),
    ProgressMode::Auto  => if std::io::stderr().is_terminal() {
        Box::new(BarObserver::new())
    } else {
        Box::new(PlainObserver::new())
    },
};

let stop = Arc::new(AtomicBool::new(false));
{
    let stop = stop.clone();
    // best-effort; if a handler is already installed, progress just won't be
    // interruptible — not fatal.
    let _ = ctrlc::try_set_handler(move || stop.store(true, Ordering::Relaxed));
}

let run = run_debug_command(
    &project, &d.proof, d.proofstep, &d.oracle, &d.claim,
    &opts, &backend, d.out.clone(),
    observer.as_mut(), Some(&stop),
)?;

print!("{}", render_tree(&run));
if !run.admitted {
    println!("\nviewer: {}/index.html", run.out_dir);
}
if !run.is_ok() { return Err(DebugNotVerified.into()); }
```

**New dependency: `ctrlc = "3"`** (in `crates/domino/Cargo.toml`, ~1 tiny crate). If the owner
would rather not add it: drop the `stop` handler and pass `None`; the per-left-path flush still
means a `Ctrl-C` loses at most the current left path's right subtree. Note the choice in the
implementation report. **Recommended: add `ctrlc`** — it makes `--max-paths` and `Ctrl-C`
behave the same and is a common, well-audited crate.

The `#[cfg(not(feature = "cvc5-lib"))]` stub of `fn debug` is unchanged (it errors out before any
of this).

### 3.6 Story 08 interaction (whichever lands second does this)

- **If 08 is already merged when you do 09:** story 08 added `SolverPruner` (a `BranchOracle`)
  and `PrunedBranch` records. Give `SolverPruner` an `observer: &mut dyn DebugObserver` field and
  emit `DebugEvent::BranchPruned { side, id, label }` from `enter` when it returns `Prune`. Add
  `BranchPruned` handling to both observers (a counter; `PlainObserver` prints
  `  pruned #<id> at L<label>`, `BarObserver` folds it into a `·pruned N` tally). Update the
  `LeftPathsCollected` / `RightPathsCollected` totals story — with pruning the "total" is an
  upper bound; the bars should use `ProgressBar::set_length` again if a prune shrinks the
  remaining work, or just let the bar finish early. Keep it simple: bar length = collected count,
  pruned pairs count as "done".
- **If 09 is already merged when you do 08:** the `BranchPruned` variant already exists and both
  observers already `_ => {}` it; 08 just needs to start emitting it and upgrade the two `_ => {}`
  arms to real counters.

Either way this is a ~20-line follow-up, not a redesign.

## 4. Acceptance criteria

- [ ] `src/debug/progress.rs` exposes `DebugEvent` (`#[non_exhaustive]`), `DebugObserver`,
      `NopObserver`, `PlainObserver`, `BarObserver`.
- [ ] `run_debug_command` / `explore_paths` take `&mut dyn DebugObserver` and
      `Option<&AtomicBool>`. With `NopObserver` + `None` the run is **behaviourally identical** to
      today: every `driver.rs` unit test passes with only the two extra args added, and
      `trace.json` / `render_tree` output for `PKENC` / `same-output` is byte-identical to a
      pre-story-09 build.
- [ ] `--progress none` produces **zero** bytes on stderr for a full `PKGEN` run.
- [ ] `--progress plain` (or `auto` piped) emits one line per `(left, right)` pair, a per-left
      rollup, and a final summary line; the lines go to **stderr**, and stdout is still exactly
      `render_tree` + the `viewer:` line. `domino debug … 2>/dev/null | diff - <golden tree>`
      matches.
- [ ] `--progress bar` (or `auto` on a TTY) shows the two-bar display, updates on every pair, and
      `MultiProgress::clear()`s before the tree is printed (no leftover bar in the scrollback).
- [ ] A `GOAL FAILS` pair prints a visible `⚠ GOAL FAILS at #<id>` on stderr **as it is found**,
      not only in the final tree — checked with the weakened-invariant fixture (§5).
- [ ] Partial artifacts: kill a `PKENC` run part-way (`--max-paths 20`), confirm `trace.json` and
      `index.html` exist, parse, open, and carry `"partial": true` plus every left path that
      finished. Same with a real `Ctrl-C` if `ctrlc` is wired.
- [ ] `trace.json` / `index.html` after a **completed** run are byte-identical to a pre-story-09
      build (determinism from story 07 preserved — no timestamps leaked in).
- [ ] Unit test: a `Vec<DebugEvent-shaped record>` mock observer over a small fixture
      (`example-projects/hello-world` or `test-projects/test-splitinvoke`) sees the event sequence
      `Started` → `LeftPathsCollected` → (`LeftPathStarted` → `RightPathsCollected` →
      `PairChecked`* → `LeftPathFinished`)* → `Finished`, with `index` monotonic and
      `Finished.summary == run.summary`.
- [ ] Unit test: with the stop flag pre-set, `explore_paths` returns after ≤ 1 left path with
      `run.partial == true` and a well-formed (if partial) `DebugRun`.
- [ ] `cargo build --workspace` / `--features cvc5-lib`, `cargo test --workspace` /
      `--features cvc5-lib`, `cargo clippy --workspace` / `--features cvc5-lib` all clean.
- [ ] `--help` for `domino debug` documents `--progress` and its four values.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh          # from scripts/setup-cvc5-lib.sh
cargo build --workspace --features cvc5-lib

cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino

# bar on a terminal, plain when piped
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output --progress plain 2>progress.log

# stdout unchanged vs a --progress none run
$D debug … --oracle PKGEN --claim same-output --progress none  > tree-none.txt
$D debug … --oracle PKGEN --claim same-output --progress plain > tree-plain.txt 2>/dev/null
diff tree-none.txt tree-plain.txt        # empty

# partial artifacts
$D debug … --oracle PKENC --claim same-output --max-paths 20 --progress plain
ls _build/debug/.../PKENC/same-output/{trace.json,index.html}
python3 -c 'import json;print(json.load(open("_build/debug/.../PKENC/same-output/trace.json"))["partial"])'  # True

# GOAL FAILS surfaces live: drop `left.pk = right.pk` from theorem/invariant.smt2, then
$D debug … --oracle PKENC --claim same-output --progress plain    # ⚠ GOAL FAILS line appears mid-run
git checkout theorem/invariant.smt2

# cross-check the verdict is unchanged
$D prove --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
```

Smaller smoke tests first: `test-projects/test-splitinvoke`, `example-projects/hello-world`,
`example-projects/simple-KEM-example`.

> **Never** run `debug` or `prove` against `example-projects/4WHS` or `example-projects/yao`
> (the slow projects in `example-projects/known-good-slow.txt`). See `docs/stories/00-overview.md` §7.

Build gotcha (overview §7): `cargo build --workspace`, **not** `cargo build --release` — the
latter does not relink the `domino` binary in `crates/domino`.

## 6. Notes / risks

- **Determinism is the sharp edge.** Story 07 promises byte-identical `trace.json` / `index.html`
  across runs, and the `run.is_ok()` exit code + several tests depend on the final `DebugRun`
  being independent of wall-clock. Elapsed times live **only** in `DebugEvent` (consumed and
  discarded by observers), never in `DebugRun`. Do not be tempted to record per-pair timings in
  the trace "while you're here" — that is a separate story with its own determinism story.
- **`indicatif` + stdout.** The bars draw on stderr; the final tree prints on stdout. As long as
  `BarObserver` clears on `Finished` before `main.rs` prints, they do not interleave. Test in a
  real terminal, not just piped.
- **Observer panics.** An observer that panics will unwind through `run_debug_command` and lose
  the run. That is acceptable (it is a bug in first-party code), but keep the observers dead
  simple — no `unwrap` on formatting, no locks.
- **`ctrlc` handler is process-global.** `debug` is a one-shot CLI invocation so this is fine.
  Use `try_set_handler` and ignore the error rather than `set_handler().unwrap()`.
- **Do not widen scope.** No `--progress json`/NDJSON event stream, no live-reloading HTML, no
  per-pair timings in the trace, no depth/first-failure flags. Those were explicitly deferred in
  the kickoff. If a follow-up wants the NDJSON stream, it is a clean addition — a third observer
  writing `events.ndjson` — and should be its own story.

## 7. State handed to the next story

There is no next story planned. Record in
`docs/stories/09-live-progress-IMPLEMENTATION-REPORT.md`:

- The final `DebugEvent` variant list and the exact emission order (the acceptance test pins it —
  copy it in).
- Whether `ctrlc` was added or the stop flag was left unwired, and why.
- Measured flush cost on `PKENC` (bytes written, added wall-clock) and whether the "≥ 1 s since
  last flush" gate was needed.
- Screenshots or a paste of the `bar` and `plain` output on `PKENC`.
- If story 08 was already merged: the `BranchPruned` wiring; if not: a one-line reminder in
  `docs/stories/08-branch-level-pruning.md` that the variant is waiting to be emitted.
