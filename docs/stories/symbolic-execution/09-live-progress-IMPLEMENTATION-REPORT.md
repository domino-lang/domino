# Story 09 — Implementation report: live exploration progress for `domino debug`

**Status:** done, uncommitted. Branch `amir/symbolic-execution-debugger`.
**Builds on:** stories 06 (`driver.rs`), 07 (`report.rs`), 08 (branch pruning — **already merged**,
so the §3.6 hook was wired here, not deferred).

This is the last story of the epic. There is no next story.

---

## 1. What shipped

| File | Change |
|---|---|
| `src/debug/progress.rs` | **new.** `DebugEvent` (`#[non_exhaustive]`), `DebugObserver`, `SharedObserver` type alias, `NopObserver`, `PlainObserver`, `BarObserver`. |
| `src/debug/mod.rs` | `pub mod progress;` |
| `src/debug/driver.rs` | `run_debug_command` / `explore_paths` / `handle_left_path` / `handle_right_path` take an observer + stop flag; events emitted at the points the driver already passes through; incremental `report::flush` after every left path; `Ctrl-C` / stop-flag check per pair; `Summary` gained `PartialEq, Eq`. |
| `src/debug/report.rs` | `pub fn flush(run, out_dir)` — writes `trace.json` + `index.html`. |
| `crates/domino/src/cli.rs` | `ProgressMode { Auto, Plain, Bar, None }`, `Debug::progress` (`--progress`, default `auto`). |
| `crates/domino/src/main.rs` | builds the observer from `--progress` + `stderr().is_terminal()`, installs a best-effort `ctrlc` handler, passes both to `run_debug_command`. |
| `crates/domino/Cargo.toml` | **new dep `ctrlc = "3"`** (resolved to 3.5.2; pulls `nix` 0.31 on unix). |

Verdicts, paths, solver calls and exit codes are **unchanged**. With `NopObserver` + `stop: None`
the driver is behaviourally identical to a pre-story-09 build (proven byte-for-byte, §4).

## 2. `DebugEvent` — final variant list and emission order

```rust
#[non_exhaustive]
pub enum DebugEvent<'a> {
    Started        { oracle: &'a str, claim: &'a str, admitted: bool },
    LeftPathStarted  { index: usize, id: &'a str },        // index 1-based
    LeftPathPruned   { id: &'a str },                      // --check-left cut the terminal
    PairChecked      { id: &'a str, verdict: &'a Verdict, elapsed: Duration },
    BranchPruned     { side: Side, id: &'a str, label: usize },   // story 08 SolverPruner
    LeftPathFinished { index: usize, running: Summary },
    Finished         { summary: Summary, partial: bool },
}
```

Exact order (pinned by `driver.rs` test `observer_sees_a_well_formed_event_stream`):

```
Started
  ( LeftPathStarted
      ( PairChecked | BranchPruned )*
      LeftPathPruned?              // only when --check-left proved the terminal unreachable
      LeftPathFinished )*          // index strictly increasing, 1..=n
Finished                           // Finished.summary == run.summary
```

- Admitted claim: `Started { admitted: true }` → `Finished { summary: Summary::default(), partial: false }`, nothing between.
- `elapsed` on `PairChecked` is the wall-clock of that pair's `check-sat`(s) only (`Instant` around `check_pair`). It is **never** stored in `DebugRun`.
- `BranchPruned` is emitted from `SolverPruner::record_prune`, so it interleaves with `PairChecked`
  under the current left path (right-side prunes) or appears between `LeftPathStarted` and the
  first `PairChecked` (left-side prunes fire before their terminals are reached).

### Divergence from the story spec

The spec's `LeftPathsCollected { total, capped }` and `RightPathsCollected { total }` were
**dropped**. They assumed both sides were fully enumerated up front (`collect_paths`). Story 08
made *both* sides stream so branch pruning can cut subtrees before their terminals — there is no
up-front total on either side any more. Consequences:

- `BarObserver` uses **spinners** with a running pair counter, not fixed-length bars.
- `PlainObserver` prints per-pair lines and a per-left rollup; there is no "N/total" progress.

This is strictly better than a bar that would sit at a wrong length while pruning removes work.

## 3. The two observers

### `PlainObserver` (`--progress plain`, or `auto` when stderr is not a TTY)

One terse `debug: …` line per event on **stderr**. Real transcript, PKGEN / `same-output`:

```
debug: PKGEN / same-output — exploring
debug: left 1 (#1) …
debug:   #1.1  verified      0.00s
debug:   pruned #1.p1 at L6 (right)
debug:   pruned #1.p2 at L3 (right)
debug:   left 1 done — running: 1 verified, 0 unreachable, 0 GOAL FAILS, 0 inconclusive
debug: left 2 (#2) …
debug:   left path #2 unreachable — pruned
debug:   left 2 done — running: 1 verified, 0 unreachable, 0 GOAL FAILS, 0 inconclusive
debug: done — 2 left, 1 right; 1 verified, 0 unreachable, 0 GOAL FAILS, 0 inconclusive (partial: no)
```

A `GoalFails` pair prints its normal line **and** an extra `debug: ⚠ GOAL FAILS at #<id>` the
moment it is found (PKENC / `same-output` with `theorem/invariant.smt2`'s `left.pk = right.pk`
clause dropped):

```
debug:   #1.1  GOAL FAILS    0.04s
debug: ⚠ GOAL FAILS at #1.1
...
debug: done — 4 left, 2 right; 0 verified, 0 unreachable, 2 GOAL FAILS, 0 inconclusive (partial: no)
```

The line formatting is factored into `progress::plain_line` and unit-tested without capturing
stderr.

### `BarObserver` (`--progress bar`, or `auto` on a TTY)

`MultiProgress` + two `indicatif` spinner lines on stderr:

```
⠹ PKENC / same-output
⠹ pairs   71  ✓2 ·68 ✗1 ?0 ✂12  [0:00:38]
```

- line 1: current left path.
- line 2: pairs classified under it (`set_position(0)` on each `LeftPathStarted`), the cumulative
  `✓ verified / · unreachable / ✗ goal-fails / ? inconclusive / ✂ branches-pruned` tally, and
  `indicatif`'s `{elapsed_precise}`.
- first `GoalFails`: `MultiProgress::println("⚠ GOAL FAILS at #<id>")` above the bars.
- `Finished`: `finish_and_clear()` both bars + `MultiProgress::clear()` — so `main.rs` prints the
  stdout tree onto a clean terminal (verified: no leftover bar in scrollback; stdout is byte-for-byte
  the same tree as `--progress none`).
- `indicatif-log-bridge::LogWrapper::try_init` is called (error swallowed) so a stray `log::warn!`
  from the solver layer cannot tear the bars.
- Not a TTY → `indicatif` draws nothing; `main.rs` only constructs `BarObserver` for explicit
  `--progress bar` in that case, and it just goes quiet (documented).

## 4. Determinism (the sharp edge — story 07)

- **No field was added to `DebugRun`.** Elapsed times live only in `DebugEvent`, consumed and
  discarded by observers.
- `report::flush` truncate-writes both files; intermediate flushes are overwritten by later ones.
- **Verified byte-for-byte:** two completed `PKENC` / `same-output` runs (one `--progress none`,
  one `--progress plain`) → `diff -q` reports `trace.json` and `index.html` **identical**.
- **stdout unchanged:** `domino debug … --progress none > a` vs `--progress plain 2>/dev/null > b`
  → `diff a b` empty (checked on PKGEN and PKENC). All progress is on stderr.
- `TRACE_SCHEMA` stays **2** (story 08's value) — no serialised-shape change.

### `--progress none` and stderr

`--progress none` emits **zero progress bytes**. A PKGEN run still prints ~1 KB of pre-existing
*claim-resolution advisories* to stderr (`⚠ claim lemma-kem-correctness, oracle PKENC is admitted`
— from `src/parser/error.rs`, surfaced by `eqctx.generate_game_or_package_invariant_claims()`).
That is unrelated to this story and unchanged by it; the story's "zero bytes" criterion is met for
progress output.

## 5. `Ctrl-C` / partial artifacts

**`ctrlc` was added** (spec's recommended option). `main.rs` installs
`ctrlc::try_set_handler` (error ignored — if a handler already exists the run is just not
interruptible). The handler sets an `AtomicBool`; `explore_paths` checks it at the top of the
left-path callback **and** the right-path callback (same mechanism as `--max-paths`), and on a set
flag does `run.partial = true; break`. The check is coarse (per pair, not mid-`check-sat`) — a
single cvc5 call can still run for seconds after `Ctrl-C`; matches how `prove` behaves.

Because `report::flush` runs after **every** left path, a stop (Ctrl-C or `--max-paths`) leaves
`trace.json` + `index.html` reflecting every finished left path plus `"partial": true`. Verified:
`--oracle PKENC --max-paths 3` → exit 1, `trace.json` `partial: true` with 2 left paths, both
files parse / open, `index.html` contains the `PARTIAL` marker.

Unit test `stop_flag_bails_with_a_partial_run` pins the pre-set-flag path (≤ 1 left path, partial,
well-formed `DebugRun`, artifacts on disk).

## 6. Measured flush cost

With story 08's pruning, `PKENC` / `same-output` now completes with **4 left paths** (4 flushes),
2 surviving right paths. Sizes: `trace.json` ~709 KB, `index.html` ~811 KB (`base_frame_smt` is
~551 KB and fixed from the first flush). ~6 MB written over the whole run.

Wall-clock, PKENC / `same-output`, warm: `--progress none` ~15 ms, `--progress plain` ~10 ms —
**flush cost is below measurement noise**. The spec's "tens of seconds to minutes" table predates
story 08.

**The "≥ 1 s since last flush" gate was not added and is not needed.**

## 7. Test / build status

```
cargo build   --workspace --features cvc5-lib      # clean
cargo test    --workspace --features cvc5-lib      # 138 pass / 4 ignored (pre-existing), + 2 new
cargo test    -p sspverif                          # progress.rs unit tests pass without the feature
cargo clippy  --workspace --features cvc5-lib      # clean
cargo clippy  --workspace                          # clean
domino debug --help                                # documents --progress and its 4 values
```

New tests:
- `debug::progress::tests::{nop_observer_ignores_everything, plain_lines_are_terse_and_greppable}`
- `debug::driver::tests::{observer_sees_a_well_formed_event_stream, stop_flag_bails_with_a_partial_run}`

Note: linking the `--features cvc5-lib` **test** binary is memory-heavy — it was OOM-killed
(exit 137) at full parallelism on this machine; `CARGO_BUILD_JOBS=2 cargo test -j2` builds it fine.

## 8. Deliberately not done (deferred in the kickoff)

No `--progress json` / NDJSON stream, no live-reloading HTML, no per-pair timings in the trace, no
depth / first-failure flags. An NDJSON stream, if ever wanted, is a clean addition — a third
observer writing `events.ndjson` — and its own story.
