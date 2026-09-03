# Story 14 — Parallel path exploration (`--jobs`)

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 06 (`src/debug/driver.rs`), story 08 (branch pruning), story 09 (observer),
story 10 (totals events, `Ctrl-C` cancellation, unlimited `--max-paths`), story 12 (`StopReason`).
Story 11 (`SmtWriter`) and story 13 (`DebugRun.goal_smt`) should land first — both are used here,
and both are cheap to work around if they have not (§2.5).
**Blocks:** nothing. This is the last story of the epic.

---

## 1. Why this story exists

`domino debug` is strictly single-threaded. For `kem-dem` `PKENC` that is ~194 `check-sat`s in
sequence on one cvc5 instance, and the machine sits at one core. The work is embarrassingly
parallel in one specific place: **the right-side sweep under each left path is independent of
every other left path.**

### What the owner asked for

> Additionally, I want to do some parallelism to the path exploration!

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **Where the parallelism goes** | **Across left paths.** Phase 1 (left enumeration + left pruning + left terminal reachability) stays sequential on the main solver; phase 2 (the right sweep + pair checks under each left path) runs on a pool of worker threads. That is where ~95 % of the solver time is. |
| **Solvers** | One cvc5 instance **per worker thread**, created inside that thread and never moved. `cvc5::Solver` is `!Send`/`!Sync` (`src/util/smtsolver/cvc5lib.rs:11`) — this is the only shape that is sound. Each worker replays the base frame once at start-up. |
| **Threading primitive** | `std::thread::scope` + a shared work index + an `mpsc` channel back to the main thread. **Not** rayon: a scoped thread provably never migrates, and the `!Send` solver must not outlive its thread. |
| **Determinism** | `trace.json` stays byte-identical to a `--jobs 1` run: results are keyed by left-path index and re-assembled in order on the main thread. Only genuinely nondeterministic verdicts (`inconclusive` from a `--timeout`) may differ, exactly as they already may between two sequential runs. |
| **Progress + artifacts** | Observers stay single-threaded: workers send owned events over the channel and the **main thread** owns the observer, `run`, `report::flush` and `summary.txt`. |
| **Default** | `--jobs auto` = `min(available_parallelism, 8)`, clamped to the number of reachable left paths. `--jobs 1` keeps the existing sequential code path verbatim. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 The sequential driver — `src/debug/driver.rs`

- `run_debug_command` (`:386`) resolves the theorem/claim, builds `base_frame` (`:586`), opens one
  solver, writes the base frame into it, wraps it in a `RefCell`, and calls `explore_paths`
  (`:610`).
- `explore_paths` builds the left `SolverPruner` (`:980`) and runs
  `execute_streaming_with_oracle(left_inl, left_inst, left_si, Side::Left, None, Some(&mut left_pruner), &mut on_left)`.
  Its `on_left` closure numbers the left path, calls `handle_left_path` (`:748`), pushes the
  `LeftPath`, re-`summarize`s (`:1220`), emits `LeftPathFinished` and `report::flush`es.
- `handle_left_path` pushes a solver level, `write_path_delta`s the left terminal (`:954`),
  optionally checks reachability (`--check-left`), then builds a **right** `SolverPruner` and runs
  the right side streaming, with `on_right` → `handle_right_path` (`:881`) → `check_pair` (`:920`)
  → `write_model` (`:1148`).
- `write_path_delta` writes only `path.decls[reported_decls..]` / `constraints[reported_constraints..]`
  because the pruner already asserted the prefix. **A worker that starts from a clean base frame
  must assert the whole path** — add `write_path_full` (ignore the watermarks; `TerminalPath`
  always carries the complete `decls` / `constraints` / `return_constraint`, `exec.rs:156`).

### 2.2 What a worker needs, and what it must not touch

Needs (all read-only, all plain data — no `Rc`/`RefCell` anywhere in the AST or in `SmtExpr`,
verified): `&B` (the backend), `&[SmtExpr]` base frame, `&SmtExpr` negated goal, `&InlinedOracle`
right side, `&GameInstance` right instance, `&SampleInfo` right, `&DebugOptions`, `&Path` out dir,
`&SmtWriter` (story 11), and one owned `TerminalPath` per job.

Must **not** touch: the `EquivalenceContext` (leave it on the main thread — precompute the goal,
story 13's `run.goal_smt`, instead of calling `emit_claim_goal_negated` per pair), the observer,
`run`, or any file other than `models/<rid>.smt2` and `smt/<L>/…` (distinct paths per job).

Add `const _: () = { fn assert_sync<T: Sync>() {} … };` static assertions for `InlinedOracle`,
`GameInstance`, `SampleInfo`, `SmtExpr` and `Cvc5LibBackend` so a future non-`Sync` field is a
compile error rather than a mystery.

### 2.3 The solver backend

`SmtSolverBackend` (`src/util/smtsolver/mod.rs:23`): `new_smtsolver()` /
`new_smtsolver_with_transcript(w)`. `Cvc5LibBackend` (`cvc5lib.rs:35`) is `{ produce_models: bool,
tlimit_per_ms: Option<u64> }` — plain data, `Send + Sync`; only the `Cvc5LibSolver` it produces is
`!Send`. So `&backend` crosses threads, solvers do not.
`run_debug_command`'s bound therefore becomes `B: SmtSolverBackend + Sync` (and the parallel path
additionally needs `B::Solver` to be usable thread-locally, which it is by construction).

### 2.4 Progress — `src/debug/progress.rs` (stories 09 / 10)

`DebugEvent` is `#[non_exhaustive]` and **borrows** (`id: &'a str`, `verdict: &'a Verdict`), so it
cannot cross a channel as-is. Workers send an owned `WorkerMsg` (§3.3); the main thread turns each
into a borrowed `DebugEvent` and hands it to the observer. `DebugObserver` stays
single-threaded — no `Send` bound, no locks.

### 2.5 If story 11 / 13 have not landed

- No `SmtWriter`: drop that argument from the worker; nothing else changes.
- No `run.goal_smt`: call `emit_claim_goal_negated` **once** on the main thread before spawning
  and pass the `SmtExpr` down. Do not call it from a worker.

## 3. Work to do

### 3.1 Options and CLI

- `DebugOptions.jobs: usize` (0 = auto). `Default` → `0`.
- `OptionsView.jobs`; **bump `TRACE_SCHEMA`** by one.
- `cli.rs` (`struct Debug`, `:63`):
  ```rust
  /// Worker threads for the right-side sweep. `0` (the default) picks
  /// `min(cpus, 8)`. `1` explores strictly sequentially. Each worker runs its
  /// own cvc5 instance and replays the base frame once, so more jobs cost more
  /// memory.
  #[clap(long, default_value_t = 0)]
  pub(crate) jobs: usize,
  ```
- Effective jobs = `min(jobs_or_auto, reachable_left_paths.len())`, and **1** forces the existing
  sequential path.

### 3.2 Split `explore_paths` into two phases

```rust
fn explore_paths(…)                    // unchanged entry point; dispatches on `opts.jobs`
fn explore_sequential(…)               // today's body, verbatim — the `--jobs 1` path
fn explore_parallel(…)                 // new
```

**Phase 1 (main thread, sequential).** Reuse the existing left-side machinery, but with an
`on_left` that does *not* explore the right side:

- run `execute_streaming_with_oracle(left_inl, …, Some(&mut left_pruner), &mut on_left)` exactly
  as today, so left branch pruning, `left_pruned_branches` and the `--max-paths` / stop-flag
  checks are unchanged;
- in `on_left`: push, `write_path_delta`, run the `--check-left` terminal check, pop, and record
  `Job { index, id, path: lp.clone(), reachable }`;
- emit `LeftPathStarted` here as today; unreachable left paths get their `LeftPathPruned` +
  `LeftPathFinished` immediately and never become worker jobs.

Phase 1 costs one `check-sat` per left terminal plus the branch prunes — for `PKENC` a handful of
queries, against ~190 in phase 2.

**Phase 2 (workers).**

```rust
std::thread::scope(|scope| {
    let next = AtomicUsize::new(0);                 // work index into `jobs`
    let (tx, rx) = std::sync::mpsc::channel::<WorkerMsg>();
    for w in 0..n_workers {
        let tx = tx.clone();
        scope.spawn(move || worker(w, &next, &jobs, &tx, …));
    }
    drop(tx);
    for msg in rx { /* main thread: observer, run assembly, flush */ }
});
```

Each `worker`:

1. `let mut solver = backend.new_smtsolver()?;` (never with a transcript — `--transcript` forces
   `--jobs 1`, §6), `set_option("tlimit-per", …)` when `opts.timeout_ms`, then write every entry
   of the base frame. Send `WorkerMsg::Ready { worker, elapsed }` so the report can quote the
   replay cost.
2. Loop: `let i = next.fetch_add(1, Relaxed); if i >= jobs.len() { break; }`. Check the stop flag;
   on set, send `WorkerMsg::Cancelled` and break.
3. `solver.push()`, `write_path_full(&mut solver, &job.path)`.
4. Build a right `SolverPruner` over a `RefCell<solver>` exactly as `handle_left_path` does — the
   pruner code is reused unchanged, with its observer field replaced by a channel sender (§3.3).
5. Stream the right side; per terminal, `push`, `write_path_full`, `check_pair` (with the
   prebuilt goal), `pop`, send `WorkerMsg::Pair { left_index, right_index, … }`, and write the
   `smt/` files via the shared `&SmtWriter`.
6. `solver.pop()`, send `WorkerMsg::LeftDone { left_index, left_path: Box<LeftPath> }`.
7. On any `DebugError`, send `WorkerMsg::Failed { left_index, error: String }` and stop pulling
   work. The main thread records the first failure, sets the stop flag so the others wind down,
   and returns it from `run_debug_command` after flushing what it has.

**Main-thread assembly.** Keep `results: BTreeMap<usize, LeftPath>` and a `next_to_emit` cursor:
when the entry for `next_to_emit` arrives, push it into `run.left_paths`, `summarize`, emit
`LeftPathFinished`, `report::flush`, and advance. That yields **exactly** the sequential order in
`trace.json` and keeps the incremental-flush guarantee of story 09 (a `Ctrl-C` still leaves a
prefix of completed left paths — plus, possibly, none of the in-flight ones, which is correct).

### 3.3 `WorkerMsg` — owned mirrors of the events

```rust
enum WorkerMsg {
    Ready     { worker: usize, base_frame_ms: u64 },
    Pair      { worker: usize, left_index: usize, id: String, verdict: Verdict, elapsed: Duration },
    Pruned    { worker: usize, left_index: usize, id: String, label: usize },
    LeftDone  { worker: usize, left_index: usize, left_path: Box<LeftPath> },
    Failed    { worker: usize, left_index: usize, error: String },
    Cancelled { worker: usize },
}
```

The main thread maps `Pair` → `DebugEvent::PairChecked`, `Pruned` → `DebugEvent::BranchPruned`,
etc. `SolverPruner` gains a small enum for "where do my events go" — `&SharedObserver` (sequential)
or `&Sender<WorkerMsg>` (parallel) — rather than being duplicated.

### 3.4 Progress display with `--jobs > 1`

`DebugEvent` gains one variant (`#[non_exhaustive]`, so no breaking change):

```rust
    /// The worker pool started. `workers == 1` for a sequential run.
    Workers { count: usize },
```

- `PlainObserver`: prefix per-pair lines with `[w2]` when `count > 1`; unchanged otherwise.
- `BarObserver`: keep the `left k/N` bar (position = left paths **finished**, which is the honest
  number when several are in flight), and replace the single `pairs` bar with `count` bars, one
  per worker: `w0  #3  ▕████░░░░▏ 41/96  ✓2 ·38 ✗1`. Route each worker's bar by the `worker`
  field. With `count == 1` the display is exactly story 10's.
- `summary.txt` (story 12) gains a `jobs` line in its `options` block and a
  `workers  4 (base frame replay 1.2s each)` line under `paths`.

### 3.5 `Ctrl-C` and `--max-paths` under parallelism

- The stop flag is already an `&AtomicBool` shared by reference — workers check it at the same two
  granularities as the sequential path (before pulling a job, and in `SolverPruner::enter` via
  story 10's `ExecError::Cancelled`).
- `--max-paths` becomes a shared `AtomicUsize` counter that every worker bumps; the first worker
  to exceed the cap sets the stop flag. The exact set of paths explored when the cap fires is then
  **not** deterministic across runs — document that plainly in `--help` and in `summary.txt`
  (`STOPPED EARLY (--max-paths <n> reached; with --jobs > 1 the explored set is not
  reproducible)`). A capped run is a triage tool, not an artifact to diff.
- `StopReason::Interrupted` / `MaxPaths` are set on the main thread from the first
  `Cancelled` / cap message.

## 4. Acceptance criteria

- [ ] `--jobs 1` uses the sequential code path and produces `trace.json` byte-identical to a
      pre-story-14 build (modulo the new `options.jobs` field and the schema bump).
- [ ] `--jobs 4` on `kem-dem` `PKENC` / `same-output` produces `trace.json` **byte-identical** to
      `--jobs 1` on the same project (no `--timeout`). Same for `PKDEC`. This is the central test:
      run it, paste the `diff` (empty) into the report.
- [ ] Measured wall-clock for `PKENC` at `--jobs 1 / 2 / 4 / 8` in the implementation report,
      with the per-worker base-frame replay cost, and a sentence on where it stops scaling.
- [ ] A failing run (weakened `theorem/invariant.smt2`) reports the same goal-fails pair ids at
      `--jobs 4` as at `--jobs 1`, and every model file is present and non-empty.
- [ ] `Ctrl-C` during a `--jobs 4` run stops all workers, writes `trace.json` / `index.html` /
      `summary.txt` with `stop_reason: interrupted`, and exits non-zero. No thread is left running
      (the process exits promptly) and no partially-written file is left behind.
- [ ] A worker-side solver error propagates: the run returns the error after flushing partial
      results, and the other workers stop rather than continuing to burn CPU.
- [ ] `--transcript` with `--jobs > 1` is rejected up front with a clear message (§6), or silently
      clamps to `--jobs 1` and says so on stderr — pick one, document it in `--help`.
- [ ] Static assertions for `Sync` on the shared types compile.
- [ ] `--progress bar --jobs 4` shows one bar per worker plus the left bar and clears cleanly;
      `--progress plain --jobs 4` tags lines with the worker id and remains greppable.
- [ ] No `unsafe`, no `Send`/`Sync` impls written by hand, no solver value crosses a thread
      boundary (grep the diff for `Send` and justify every hit in the report).
- [ ] `cargo build`/`test`/`clippy --workspace` and `--features cvc5-lib` clean, and
      `cargo test --features cvc5-lib` is run **twice** to catch order-dependent flakiness.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output

for j in 1 2 4 8; do
  rm -rf "$O"
  /usr/bin/time -f "jobs=$j %e s  %M KB" \
    $D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output --jobs $j
  cp "$O/trace.json" /tmp/trace-$j.json
done
diff /tmp/trace-1.json /tmp/trace-4.json && echo "identical"

# interrupt a parallel run
$D debug … --oracle PKENC --claim same-output --jobs 4      # Ctrl-C after ~5s
grep status "$O/summary.txt"
```

Smaller smoke tests first: `test-projects/test-splitinvoke`, `example-projects/hello-world`,
`example-projects/simple-KEM-example` — at `--jobs 1` and `--jobs 4`, comparing `trace.json`.

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release`.

## 6. Notes / risks

- **`cvc5::Solver` is `!Send` and `!Sync` and that is not negotiable.** Create it inside the
  worker closure, use it only there, drop it there. If you find yourself wanting a
  `Mutex<Solver>`, `unsafe impl Send`, or a rayon `par_iter` over pairs, stop — the design in §3
  exists precisely to avoid all three.
- **The transcript is inherently sequential.** One interleaved `transcript.smt2` from four solvers
  is meaningless, so `--transcript` and `--jobs > 1` are incompatible. Story 11 made the
  transcript opt-in, which is why this is a footnote rather than a blocker.
- **Memory.** Each worker holds a full cvc5 instance with the base frame (~3.5 MB of SMT for
  `PKENC`, considerably more in cvc5's internal representation). Measure RSS at `--jobs 8` and say
  so in the report; if it is bad, lower the auto cap and document the number.
- **Determinism is the acceptance bar, not a nice-to-have.** Story 07's byte-identical guarantee
  and several tests depend on it. Assembling results by index (never by arrival) is what preserves
  it; verify with the `diff` in §4, not by reasoning.
- **`--max-paths` + `--jobs > 1` is the one accepted non-determinism.** Say it in `--help` and in
  `summary.txt`; do not try to make a capped parallel run reproducible.
- **Do not widen scope.** No parallelism *within* a left path (the right sweep shares one solver
  stack by design), no parallel left enumeration, no work-stealing across oracles or claims, no
  async runtime.

## 7. State handed to the next story

This is the last story of the epic. Record in
`docs/stories/14-…-IMPLEMENTATION-REPORT.md`:

- The final phase-1/phase-2 split, the `WorkerMsg` enum, and where `SolverPruner` routes events.
- The measured scaling table (`--jobs 1/2/4/8`: wall-clock, RSS, base-frame replay per worker) and
  the chosen auto cap.
- The `diff`-empty evidence for `--jobs 1` vs `--jobs 4` on `PKENC` and `PKDEC`.
- The final `TRACE_SCHEMA` and the full `OptionsView` shape at the end of the epic.
- Anything that had to stay sequential and why.
