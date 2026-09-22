# Story 08 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. **Not committed** (commit message at
the bottom). There is no story after this in the pruning line; story 09 (live progress) is
independent and unaffected except for the notes in §8.

Read together with `docs/stories/08-branch-level-pruning.md`.

`cargo build/test/clippy --workspace` (123 lib tests) and — with `scripts/setup-cvc5-lib.sh`
sourced — `cargo build/test/clippy --workspace --features cvc5-lib` (**134 lib tests**, +10) all
pass clean, `--all-targets` included. `domino prove` / `latex` / `proofsteps` untouched.

---

## 1. What landed

| File | Change |
|---|---|
| `src/debug/exec.rs` | New public surface: `BranchQuery`, `Feasibility`, `BranchOracle`, `execute_streaming_with_oracle`, `TerminalPath::{reported_decls, reported_constraints}`. The walk's two forks (`Branch`, `Unwrap`) are now **symmetric** — both children descend through the new `Executor::descend` helper, which owns the `enter`/`leave` protocol. `execute` / `execute_streaming` are thin wrappers passing `oracle: None` and are byte-identical to before. +4 unit tests with a mock oracle. |
| `src/debug/driver.rs` | `SolverPruner` (the solver-backed `BranchOracle`), rewritten `explore_paths` as a streaming DFS driven by two pruners (left + per-left-path right), `handle_left_path` / `handle_right_path`, `write_path_delta`. Vacuity in `check_pair` is now **unconditional**. `DebugOptions` default flips to `check_left = check_right = true`. New report types `PrunedBranch`; `DebugRun.left_pruned_branches`, `LeftPath.pruned_branches`, `Summary.{left_pruned_branches, right_pruned_branches, sibling_shortcuts}`. `TRACE_SCHEMA` → **2**. The solver is wrapped in a `RefCell` so the pruner and the terminal handler can both reach it (they never overlap — see §3). |
| `src/debug/report.rs` | `index.html` renders pruned branches as rows (synthetic "pruned" verdict, `badge pruned`, text `pruned at L<n> (unsat)`): right-side prunes inside the left path's child list, left-side prunes as top-level rows. They honour the existing `pruned` verdict toggle and the text filter. Summary chips gain the branch-prune counts + `sibling shortcuts`. Detail panel for a pruned row: step table + listing with the cut branch highlighted. Synthetic-`DebugRun` test updated; schema assertion is `2`. |
| `crates/domino/src/cli.rs` | `--check-left` **removed** (unreleased, no shim). `--no-check-left` added; `--no-check-right`'s help reworded — it no longer disables the vacuity check, only early pruning. |
| `crates/domino/src/main.rs` | `check_left: !d.no_check_left, check_right: !d.no_check_right`. |
| `docs/stories/07-…md` | schema section: `1` → `2`, new keys documented. |

No `Cargo.toml` / `Cargo.lock` change.

## 2. Final public surface of `exec.rs`

```rust
pub struct BranchQuery<'a> {
    pub label: Label,
    pub decision: Decision,
    pub steps: &'a [Step],        // includes `decision`
    pub decls: &'a [SmtExpr],     // delta since the enclosing Explore scope
    pub constraints: &'a [SmtExpr], // ditto; last entry is this child's path condition
    pub sibling: u8,             // 0 = first child at this fork, 1 = second
}
pub enum Feasibility { Explore, Prune }

pub trait BranchOracle {
    fn enter(&mut self, q: &BranchQuery<'_>) -> Result<Feasibility, ExecError>;
    fn leave(&mut self);
}

pub fn execute_streaming_with_oracle(
    inlined, game_inst, sample_info, side, max_paths,
    oracle: Option<&mut dyn BranchOracle>,
    on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>,
) -> Result<(), ExecError>;
```

### Ordering and balancing guarantees (as implemented)

- The executor's DFS visits, at each fork: `enter(sibling 0)` → *(its whole subtree)* →
  `leave(sibling 0)` → `enter(sibling 1)` → *(subtree)* → `leave(sibling 1)`. `enter`/`leave`
  scopes are therefore a **stack** — properly nested.
- `leave` is called **exactly once for every `enter` that returns `Ok`**, including:
  - `Ok(Feasibility::Prune)` — `descend` calls `leave` immediately, the child's subtree is not
    walked, and `ControlFlow::Continue` is returned so the sibling is still offered;
  - a `body` (walk) that returns `ControlFlow::Break` (early stop / `on_path` break);
  - a `body` that returns `Err(ExecError)` (e.g. `MaxPathsExceeded`) — `descend` binds the result
    and runs `leave` before propagating, it does **not** use `?`.
  If `enter` itself returns `Err`, that is propagated and **no** `leave` is paired with it.
- `BranchQuery::{decls, constraints}` are the delta **since the previous `enter` in this pruner
  that was answered `Explore`** — the executor advances the `SymState` watermark only then.
  `TerminalPath::{reported_decls, reported_constraints}` carry that watermark to the driver;
  `decls` / `constraints` themselves stay complete (the report renders the whole path).
- `oracle: None` ⇒ output byte-identical to `execute_streaming` — the story-05 goldens
  (`golden_hello_world_medium`, …) pass **unedited**. New test `oracle_none_matches_no_oracle`
  asserts an all-`Explore` oracle reproduces the same paths and that `enter`/`leave` balance.

### Recursion note

Story 05's iterative else-continuation is gone: both children now recurse through `descend`, so
stack depth is proportional to the number of forks on a path (≤ ~15 across the corpus; `PKENC`'s
right side has 11). A comment at `Executor::walk` says so — do not "fix" it back, it would break
the `enter`/`leave` nesting.

## 3. How the driver uses it

`explore_paths` no longer collects paths up front. It builds a **left `SolverPruner`** and runs
`execute_streaming_with_oracle(left, …, Some(&mut left_pruner), on_left)`. At each left terminal,
`on_left` calls `handle_left_path`, which — with the solver stack already at that path's branch
depth — pushes one level, asserts `write_path_delta` (only `decls[reported_decls..]` etc.), does
the per-left-path terminal `check_sat` (gated on `check_left`; catches `no-abort`-killed abort
paths, which are unsat only at the *terminal*), then builds a **right `SolverPruner`** and streams
the right oracle under it. `handle_right_path` pushes, asserts the right delta, runs `check_pair`
(unconditional vacuity, then negated goal), pops.

`SolverPruner::enter`: `push` + write the delta; if `!enabled` → `Explore`; else the **sibling
shortcut** (if `sibling == 1`, the other child was pruned, and the parent was a definite `Sat`,
answer `Explore` with no query); else `check_sat` → `Unsat` records a `PrunedBranch` and returns
`Prune`, `Sat` → `Explore` (parent-sat = true), `Unknown` / error → `Explore` (never prune).
`leave`: `pop`, pop the bookkeeping. A `scope_pruned` stack makes the "previous sibling pruned"
signal survive correctly through nested subtrees (it is set on `leave`, not `enter`).

### Why the `RefCell`

`execute_streaming_with_oracle` takes the `BranchOracle` and the `on_path` handler as **separate**
`&mut` parameters, but both need the solver: the pruner during the walk, the terminal handler when
the DFS is paused at a leaf. They never run concurrently (single-threaded; `on_path` is called
from `emit_terminal`, between an `enter` and its `leave`, never during one). `RefCell<S>` with
`borrow_mut()` at each use site expresses exactly that, and a bug (overlap) would panic loudly.
`run_debug_command` moves the solver into the `RefCell` after writing the base frame and calls
`.into_inner().close()` after.

### Push/pop discipline

`SolverPruner::depth()` (= open `enter` scopes) is `debug_assert!`ed back to `0` after the left
walk and after every right walk; the per-left-path terminal `push`/`pop` is a plain matched pair.
`transcript.smt2` replays cleanly through `cvc5 --incremental` (PKENC `same-output`: 53
`check-sat` → 25 `sat` + 28 `unsat`, no `unknown`, matching the driver's verdicts).

## 4. Before/after numbers — `example-projects/kem-dem/kem-dem-cca-ssp` proofstep 0

`--no-check-left --no-check-right` reproduces story 06's numbers **exactly**. Default (both on):

| oracle / claim | mode | left | right | branches pruned (L/R) | verified | unreachable | goal-fails | wall-clock | `check-sat` |
|---|---|---|---|---|---|---|---|---|---|
| PKGEN / same-output | no-check | 2 | 6 | – | 1 | 5 | 0 | 0.9 s | 7 |
| PKGEN / same-output | **default** | 2 (1 pruned) | 1 | 0 / 2 | 1 | 0 | 0 | 0.9 s | 10 |
| PKGEN / equal-aborts | no-check | 2 | 6 | – | 2 | 4 | 0 | 1.0 s | 8 |
| PKGEN / equal-aborts | **default** | 2 | 2 | 0 / 3 | 2 | 0 | 0 | 0.9 s | 14 |
| PKGEN / invariant | no-check | 2 | 6 | – | 1 | 5 | 0 | 0.9 s | 7 |
| PKGEN / invariant | **default** | 2 (1 pruned) | 1 | 0 / 2 | 1 | 0 | 0 | 1.0 s | 10 |
| PKDEC / same-output | no-check | 5 | 65 | – | 2 | 63 | 0 | 1.3 s | 67 |
| PKDEC / same-output | **default** | 4 (3 pruned) | 2 | 1 / 11 | 2 | 0 | 0 | 1.0 s | 40 |
| PKDEC / equal-aborts | no-check | 5 | 65 | – | 5 | 60 | 0 | 1.4 s | 70 |
| PKDEC / equal-aborts | **default** | 4 | 5 | 1 / 17 | 5 | 0 | 0 | 1.0 s | 50 |
| PKDEC / invariant | no-check | 5 | 65 | – | 2 | 63 | 0 | 1.4 s | 67 |
| PKDEC / invariant | **default** | 4 (3 pruned) | 2 | 1 / 11 | 2 | 0 | 0 | 0.9 s | 34 |
| PKENC / same-output | no-check | 6 | 96 | – | 2 | 94 | 0 | 2.0 s | 98 |
| PKENC / same-output | **default** | 4 (2 pruned) | 2 | 2 / 22 | 2 | 0 | 0 | 1.0 s | 53 |
| PKENC / equal-aborts | no-check | 6 | 96 | – | 4 | 92 | 0 | 1.8 s | 100 |
| PKENC / equal-aborts | **default** | 4 | 4 | 2 / 25 | 4 | 0 | 0 | 1.1 s | 62 |
| PKENC / invariant | no-check | 6 | 96 | – | 2 | 94 | 0 | 1.9 s | 98 |
| PKENC / invariant | **default** | 4 (2 pruned) | 2 | 2 / 22 | 2 | 0 | 0 | 1.1 s | 62 |

Notes:

- **No verdict changed.** `goal_fails` is `0` in every mode; the `verified` count is identical
  between `no-check` and `default` for every row. Branch pruning only ever removes pairs that
  would have been `Unreachable` — and it removes essentially *all* of them, one level up, which
  is why `unreachable` drops to `0` under the default. (The `Unreachable` *verdict* is still
  reachable and is still exercised by `vacuity_runs_with_all_pruning_off` and by any
  `--no-check-*` run.)
- **Wall-clock** improves ~2× on `PKENC`, ~1.3–1.4× on `PKDEC`, flat on `PKGEN`. `check-sat`
  count drops ~45 % on `PKENC` (98 → 53). The bigger win is tree shape / legibility.
- **Left path count** shrinks (6 → 4 on `PKENC`) because left *branches* are cut before their
  terminals are enumerated; a further 2–3 of the survivors are then terminal-pruned by
  `check_left` under `no-abort`.

## 5. The sibling shortcut

It fired on: `PKDEC` equal-aborts (8×), `PKDEC` invariant (6×), `PKENC` same-output (9×),
`PKENC` equal-aborts (10×). It did **not** fire on `PKGEN` (oracle too small — forks are at the
top level where the parent context has not been `check-sat`ed, so `parent_sat` is `None`) or on
`PKENC` invariant (0× — that run's pruned forks all happened to be `sibling 0`, i.e. the pruned
child was offered first, so there was no already-pruned sibling to shortcut past). Where it fires
it saves one `check-sat` per hit. Sound: `base ∧ P` `Sat` together with `base ∧ P ∧ c` `Unsat`
implies `base ∧ P ∧ ¬c` `Sat`. Never applied when the parent was only `Unknown`.

## 6. `--no-check-right` semantics changed

`--no-check-right` used to *skip the vacuity check*, so unreachable pairs fell through to
`Verified`. It now only disables early right-branch pruning; the terminal-pair vacuity check runs
unconditionally. Anyone with `--no-check-right` in a script gets a **strictly better** answer
(unreachable pairs are labelled `Unreachable`, not `Verified`). The `--help` text says so.

## 7. Acceptance criteria — status

All met.

- [x] `exec.rs` exposes the new surface; `TerminalPath` has `reported_decls` / `reported_constraints`.
- [x] `oracle: None` byte-identical — story-05 goldens pass unedited.
- [x] Mock-oracle test: pruning every `AssertFails` child yields exactly the paths with no
      `assert-fails` step; `enter` == `leave`; properly nested
      (`pruning_assert_fails_drops_exactly_those_paths`).
- [x] `leave` balances `enter` on `ControlFlow::Break` and on `MaxPathsExceeded`
      (`leave_balances_enter_on_early_break`, `leave_balances_enter_on_max_paths`).
- [x] `--no-check-left --no-check-right` reproduces today's default numbers exactly (PKENC 6/96,
      2 verified, 94 unreachable, 0 goal-fails) — `pruning_shrinks_the_tree_without_changing_verdicts`.
- [x] Default on PKENC/`same-output`: strictly fewer right paths, same `goal_fails` (0), same
      `verified` set, `verified + unreachable == right_paths` — same test.
- [x] Vacuity unconditional: `--no-check-*`-both PKGEN still reports `Unreachable`
      (`vacuity_runs_with_all_pruning_off`); the old test's `<=` is now `==` for the
      both-off run vs. the default baseline it is compared against.
- [x] Only `unsat` prunes — `SolverPruner::enter` maps `Unknown`/error to `Explore`; the exec.rs
      mock covers the executor side.
- [x] `--timeout 1` yields `Inconclusive`, never `Verified`, never a false `GoalFails`
      (`tiny_timeout_yields_inconclusive_never_a_false_pass`, run with pruning off — see the
      deviation note below).
- [x] **Weakened-invariant regression** (drop the `left.pk = right.pk` conjunct from
      `theorem/invariant.smt2`): `PKENC` / `same-output` → **2 GOAL FAILS** with models and
      readable paths, *with pruning on* (and 2 with pruning off — identical). Restore → all green
      again, exit 0. Pruning does not hide the failure.
- [x] Push/pop discipline asserted (`SolverPruner::depth() == 0`); transcript replays through
      `cvc5 --incremental`.
- [x] `trace.json` schema `2`; `index.html` renders pruned rows honouring the `pruned` filter —
      verified with a headless DOM shim over the `PKENC`, `hello-world` and `splitinvoke` traces
      (tree build, node selection, verdict toggles, text filter — no exceptions).
- [x] All four `cargo` invocations clean, default build still works.

### Deviation: the `--timeout 1` test runs with pruning **off**

The story expected `--timeout 1` to prune nothing "because the branch queries also time out". In
practice cvc5 decides the trivially-`unsat` branch prefixes in well under a millisecond, so with
pruning **on** a 1 ms budget still prunes ~24 branches on `PKENC` and — because the surviving
incremental context makes each remaining goal check easy — resolves the whole run to
`2 verified, 0 inconclusive`. That is a *correct* result (nothing was a timeout-treated-as-pass),
but it means "yields Inconclusive" only holds with pruning off. The test now sets `..both_off()`
and keeps the real guarantee: `goal_fails == 0`, `inconclusive > 0`, `!is_ok()`, nothing pruned.

## 8. Notes for follow-up

- **Story 09 (live progress)** is untouched by this. Its `on_path`-style hooks now sit inside
  `handle_left_path` / `handle_right_path` (the streaming `on_left` / `on_right` closures) rather
  than the old `for` loops; a `BranchPruned` progress event maps directly onto
  `SolverPruner::record_prune`.
- The `RefCell<S>` wrapper is a small tax. If a future refactor makes `BranchOracle` and the
  terminal handler one object, it can go away.
- `Summary.sibling_shortcuts` is diagnostic-only and not in the story's field list — added
  because the story asks the report to state whether the shortcut fired.
- Nothing regressed in `domino prove` / `latex` / `proofsteps` (not on those code paths).

## 9. Commit message

```
Story 08: branch-level pruning on both sides of `domino debug`

Adds a `BranchOracle` callback to the story-05 symbolic executor
(`execute_streaming_with_oracle`), consulted at every fork before the
walk descends. `src/debug/driver.rs`'s `SolverPruner` is that oracle: it
mirrors the executor's DFS on the solver stack (push per `enter`, pop per
`leave`) and answers `Prune` for a fork whose prefix cvc5 reports `unsat`.
Only `unsat` prunes; `unknown`/timeouts are always explored. Sound because
the per-path encoding is a plain conjunction, so an `unsat` prefix can
only ever have removed pairs that would have been `Unreachable` — it
cannot hide a `GoalFails` (kept as the weakened-invariant regression).

Verdicts are now decoupled from pruning: the terminal-pair vacuity check
is unconditional. `check_left` / `check_right` are both on by default and
only gate early pruning; `--check-left` is removed, `--no-check-left` /
`--no-check-right` disable pruning (together they reproduce the old
full-enumeration numbers exactly). A per-left-path terminal check (gated
on `check_left`) still prunes whole left paths that `no-abort` kills,
since those are unsat only at the terminal.

On kem-dem proofstep 0: PKENC `same-output` goes from 6 left / 96 right /
94 unreachable to 4 left / 2 right / 24 branches pruned / 0 unreachable,
~2x faster, check-sat 98 -> 53. No verdict changes anywhere.

trace.json schema 1 -> 2: `left_pruned_branches`, `left_paths[].pruned_
branches`, and three `summary` counts. `index.html` renders pruned forks
as rows under the existing `pruned` filter toggle. The `Branch`/`Unwrap`
forks in the executor are now symmetric (both children recurse through a
`descend` helper that owns the enter/leave protocol, incl. balancing on
`Break` and `Err`); with `oracle: None` the output is byte-identical and
the story-05 goldens pass unedited. The driver wraps the solver in a
`RefCell` so the pruner and the terminal handler can both reach it.

cargo test --workspace and --workspace --features cvc5-lib both pass
(+10 tests: 4 exec.rs mock-oracle, driver pruning/vacuity/timeout);
clippy clean --all-targets; `domino prove` output unchanged.

Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01X1JRU4uCnW8UYgLGgeiYqX
```
