# Story 08 — Branch-level pruning on both sides

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 05 (`src/debug/exec.rs`), story 06 (`src/debug/driver.rs`), story 07
(`src/debug/report.rs`).
**Blocks:** nothing.

This is the follow-up story 06's implementation report opens with in its §8:

> **Real branch-level pruning** needs a branch-point callback in story 05's `execute_streaming`
> (out of scope here — story 05 explicitly ships terminal-only streaming). With it, the driver
> could prune a shared branch prefix once instead of re-deriving `unsat` for every full path, and
> the `unreachable` counts would drop sharply.

---

## 1. Why this story exists

`domino debug` today enumerates **every syntactic path** on both sides with no solver involvement,
then pairs each left terminal with each right terminal and asks the solver about the pair. The
result on the epic's primary target, `example-projects/kem-dem/kem-dem-cca-ssp` proofstep 0:

| oracle | left paths | right paths | verified | unreachable |
|---|---|---|---|---|
| `PKGEN` | 2 | 6 | 1 | **5** |
| `PKDEC` | 5 | 65 | 2 | **63** |
| `PKENC` | 6 | 96 | 2 | **94** |

98 % of the tree is `Unreachable` noise. Worse, the noise is *structured*: right path `#4.16`
is unreachable because its very first `assert` contradicts the left path's first `assert` under
the old-state invariant — a fact the solver could have established **once, at that branch**,
instead of being re-derived at all 16 terminals below it, for each of the 6 left paths.

The owner's decision:

> I want `check-right` to be branch level pruning. The same for `check-left`. Both are on by
> default so branches are pruned; the CLI option **disables** early pruning and all paths are
> explored (`--no-check-left`, `--no-check-right`). I always want `unreachable` / `verified` /
> `goal-fails` / `inconclusive` to be distinguishable — that is not what these flags are about.
> These flags are just about pruning branches early to prevent further processing on unreachable
> branches.

So this story does two separable things:

1. **Decouple verdicts from pruning.** The terminal-pair vacuity check that produces
   `Verdict::Unreachable` becomes **unconditional**. It is no longer tied to `check_right`.
2. **Make both flags mean branch-level pruning**, both **on by default**, disabled with
   `--no-check-left` / `--no-check-right`.

`--no-check-left --no-check-right` together must reproduce **exactly** today's default behaviour.

## 2. Inherited from earlier stories — read this before touching anything

### 2.1 The executor — `src/debug/exec.rs` (story 05)

```rust
pub enum Side { Left, Right }                                   // :62
pub struct Step { pub label: Label, pub decision: Decision }    // :78
pub enum Decision { Then, Else, AssertHolds, AssertFails, UnwrapSome, UnwrapNone }  // :84
pub enum Terminal { Return { label, value }, Abort { label } }  // :113
pub struct TerminalPath {                                       // :137
    pub id: String,               // "" — the driver assigns it
    pub steps: Vec<Step>,
    pub decls: Vec<SmtExpr>,      // declare-const, in dependency order
    pub constraints: Vec<SmtExpr>,// (assert (= ssa rhs)) and path conditions, in order
    pub return_constraint: SmtExpr,
    pub terminal: Terminal,
}
pub enum ExecError { MaxPathsExceeded { explored, limit }, OracleNotExported { .. } }  // :151

pub fn execute(inlined, game_inst, sample_info, side, max_paths)                       // :921
    -> Result<Vec<TerminalPath>, ExecError>;
pub fn execute_streaming(inlined, game_inst, sample_info, side, max_paths,             // :940
    on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>) -> Result<(), ExecError>;
```

The walk (`Executor::walk`, `src/debug/exec.rs:536`) is an iterative loop over a
`Vec<Cursor<'a>>` frame stack (`Cursor { block, ip, kind }`, `FrameKind::{Sub, Call { bind }}`).
It forks in exactly **two** places, and both use the same asymmetric shape — **this is the shape
you must change**:

- `InlStmt::Branch` (`:609`) — clones `st` and `frames` for the **then**-child and recurses
  (`self.walk(frames_then, st_then, on_path)?`, `:638`); the **else**-child mutates `st`/`frames`
  in place and *continues the loop* (`:643-652`).
- `InlStmt::Unwrap` (`:569`) — clones `st` for the **none**-child and calls
  `self.emit_terminal(st_none, Terminal::Abort { .. }, on_path)?` directly (`:592`, an unwrap
  failure is always an immediate abort); the **some**-child mutates `st` in place and continues
  the loop (`:600-606`).

Other facts you need:

- `Executor.ssa` (`:382`) is one monotone counter for the whole `execute_streaming` call.
  SSA names are `<v!{side}!{n}!{basename}>` (`:450-460`). DFS order is then-subtree fully, *then*
  else-subtree — so the counter is consumed in DFS order.
- `Executor.path_count` / `max_paths` (`:383-384`) are checked in `emit_terminal`.
- `emit_terminal` (`:712`) builds `return_constraint` and calls `on_path`.
- `SymState` (`:161`) holds `locals`, `pkg_state`, `rand_ctr`, `pkg_consts`, and the accumulating
  `steps` / `decls` / `constraints`.

### 2.2 The driver — `src/debug/driver.rs` (story 06)

```rust
pub struct DebugOptions { pub check_left: bool, pub check_right: bool,   // :67
                          pub timeout_ms: Option<u64>, pub max_paths: usize }
// Default (:82): check_left=false, check_right=true, timeout_ms=None, max_paths=1000
```

- `base_frame` (`:516`) asserts, once at solver level 0: `emit_base_declarations`,
  `emit_theorem_paramfuncs`, `emit_game_definitions`, `emit_constant_declarations(Some(oracle))`,
  `emit_auto_randomness`, `emit_invariant`, `emit_return_value_helpers`,
  `emit_randomness_mapping_condition`, `emit_claim_assumptions(claim, oracle)`.
- `explore_paths` (`:540`) collects **all** left paths up front (`collect_paths`, `:690`), then per
  left path: `push`, `write_path`, optional `check_left` sat-check, then **re-collects all right
  paths** (`:590-591`) and per right path `push` / `write_path` / `check_pair` / `pop`.
- `check_pair` (`:634`) — `if opts.check_right && check_sat() == Unsat { return Unreachable }`,
  then `push`, `emit_claim_goal_negated`, `check_sat`, classify, `pop`.
- `write_path` (`:665`) writes `decls`, then `constraints`, then `return_constraint`.
- `LeftPath.reachable: bool` (`:256`) is `false` only when `--check-left` proved the whole left
  path unsat.
- `Verdict` (`:293`): `Verified` / `Unreachable` / `GoalFails { model }` /
  `Inconclusive { model }`.
- `Summary` (`:307`): `left_paths, left_pruned, right_paths, verified, unreachable, goal_fails,
  inconclusive`.
- `render_tree` (`:775`) is the stdout printer. `TRACE_SCHEMA = 1` (`:142`).

### 2.3 The report — `src/debug/report.rs` (story 07)

`write_trace_json` and `write_html` serialise `DebugRun` and embed it as `const T = {…}` in a
self-contained `index.html`. The viewer already has a **`"pruned"` verdict class and filter
toggle** (`VERDICTS` at `report.rs:283`, `.badge.pruned` styling, the `pruned (unsat)` badge at
`report.rs:322`) — used today only for the whole-left-path prune. You extend that, you do not
invent it.

### 2.4 Why prefix pruning is sound (state this in the module docs)

The per-path encoding is a **conjunction**: `decls ++ constraints ++ return_constraint`. A branch
adds one more conjunct. Therefore, for any prefix `P` and any completion `P ++ Q`:

> `base ∧ P` is `unsat`  ⟹  `base ∧ P ∧ Q` is `unsat` for every `Q`.

So cutting a subtree whose prefix is `unsat` removes only pairs that would have been
`Unreachable`. It can never hide a `GoalFails`. The converse does **not** hold — `base ∧ P` may be
`sat` while every completion is `unsat` — which is why the terminal-pair vacuity check stays, and
why `Verdict::Unreachable` still occurs with pruning fully enabled (the return constraints are not
part of any prefix).

**Only `unsat` ever prunes.** `unknown` and timeouts are always explored. This is the safety
property of the whole tool; it is already in `docs/stories/00-overview.md` §3 and must not be
weakened.

## 3. Work to do

### 3.1 `src/debug/exec.rs` — a branch-point callback

Add, next to the existing public surface:

```rust
/// What the consumer is asked about at one fork, before the executor descends.
pub struct BranchQuery<'a> {
    /// Label of the forking statement (`Branch` or `Unwrap`).
    pub label: Label,
    /// Which child is being proposed.
    pub decision: Decision,
    /// Every step on this path so far, *including* `decision`.
    pub steps: &'a [Step],
    /// `declare-const`s introduced since the previous `BranchOracle` callback,
    /// in dependency order.
    pub decls: &'a [SmtExpr],
    /// `assert`s introduced since the previous callback, in order. The **last**
    /// entry is this child's path condition.
    pub constraints: &'a [SmtExpr],
    /// `0` for the first child offered at this fork, `1` for the second.
    pub sibling: u8,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Feasibility { Explore, Prune }

/// Consulted at every fork. The executor guarantees `leave` is called exactly
/// once for every `enter`, including ones answered `Prune`, and including when
/// the walk unwinds early via `ControlFlow::Break` or `ExecError`.
pub trait BranchOracle {
    fn enter(&mut self, query: &BranchQuery<'_>) -> Result<Feasibility, ExecError>;
    fn leave(&mut self);
}
```

and the entry point:

```rust
pub fn execute_streaming_with_oracle(
    inlined: &InlinedOracle,
    game_inst: &GameInstance,
    sample_info: &SampleInfo,
    side: Side,
    max_paths: Option<usize>,
    oracle: Option<&mut dyn BranchOracle>,
    on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>,
) -> Result<(), ExecError>;
```

Keep `execute` and `execute_streaming` as thin wrappers passing `oracle: None`. **With `None` the
output must be byte-identical to today** — same paths, same order, same SSA numbers. The story-05
goldens (`golden_hello_world_medium`, `hello_world_small_is_one_straightline_path`, …) are the
check; they must not need editing.

Add two fields to `TerminalPath` so the driver can assert only what it has not already asserted:

```rust
    /// How many leading entries of `decls` were already handed to the
    /// `BranchOracle`. `0` when no oracle was supplied.
    pub reported_decls: usize,
    /// Likewise for `constraints`.
    pub reported_constraints: usize,
```

`decls` / `constraints` stay complete — the report renders the whole path (`render_path_smt`,
`driver.rs:739`), and only the driver's `write_path` uses the offsets.

#### Restructuring the walk

Both forks must become symmetric so each child has a scope with a matching `leave`. The
minimal change is to make the second child recurse too, and return:

```rust
InlStmt::Branch { label, cond, then, els, is_assert } => {
    let cond_smt = to_smt(&st, cond);
    let (d_then, d_else) = ...;

    // then-child
    let mut st_then   = st.clone();
    let mut frames_then = frames.clone();
    st_then.steps.push(Step { label: *label, decision: d_then });
    st_then.constraints.push(SmtAssert(cond_smt.clone()).into());
    frames_then.push(Cursor { block: then, ip: 0, kind: FrameKind::Sub });
    if self.descend(oracle, *label, d_then, 0, frames_then, st_then, on_path)?.is_break() {
        return Ok(ControlFlow::Break(()));
    }

    // else-child — now also a descend, then return
    st.steps.push(Step { label: *label, decision: d_else });
    st.constraints.push(SmtAssert(SmtNot(cond_smt)).into());
    frames.push(Cursor { block: els, ip: 0, kind: FrameKind::Sub });
    return self.descend(oracle, *label, d_else, 1, frames, st, on_path);
}
```

`descend` is the new helper that owns the protocol:

```rust
fn descend(&mut self, oracle: Option<&mut dyn BranchOracle>, label: Label,
           decision: Decision, sibling: u8,
           frames: Vec<Cursor<'a>>, st: SymState,
           on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>)
    -> Result<ControlFlow<()>, ExecError>
{
    // 1. slice the delta since st.reported_{decls,constraints}
    // 2. if let Some(o) = oracle { match o.enter(&query)? {
    //        Prune   => { o.leave(); return Ok(ControlFlow::Continue(())); }
    //        Explore => { /* mark st.reported_* = st.decls.len()/constraints.len() */ }
    //    }}
    // 3. let r = self.walk(oracle, frames, st, on_path);
    // 4. if oracle.is_some() { o.leave(); }          // ALWAYS, including on Err
    // 5. r
}
```

Track the "already reported" watermark on `SymState` (two `usize` fields, cloned with it) and copy
them into `TerminalPath` in `emit_terminal`.

`Unwrap` gets the same treatment: the none-child becomes
`descend(..., Decision::UnwrapNone, 0, ...)` whose body is the existing
`emit_terminal(st_none, Terminal::Abort { label }, on_path)`, and the some-child becomes
`descend(..., Decision::UnwrapSome, 1, ...)` returning.

**Step 4 must run on every exit path**, including `?` propagation of an `ExecError`. Use a small
guard struct or an explicit `match` — do not rely on `?`.

**Recursion depth.** This trades story 05's iterative else-continuation for recursion depth
proportional to the number of forks on a path (≤ ~15 in the whole corpus; `PKENC`'s right side has
11). That is fine and `max_paths` bounds the rest. Say so in a comment where story 05's
`§4.4`-motivated iterative shape used to be, so the next reader does not "fix" it back.

### 3.2 `src/debug/driver.rs` — a solver-backed `BranchOracle`

```rust
/// Mirrors the executor's DFS on the solver stack: one `push` per `enter`,
/// one `pop` per `leave`.
struct SolverPruner<'s, S: SmtSolver> {
    solver: &'s mut S,
    /// `false` ⇒ never query, never prune (still pushes/pops so the stack stays
    /// in lockstep and the terminal deltas line up).
    enabled: bool,
    /// Per open scope: was this context answered a definite `Sat`?
    known_sat: Vec<bool>,
    /// Set when the previous sibling at the current fork was pruned.
    last_sibling_pruned: bool,
    /// Recorded cuts, for the report.
    pruned: Vec<PrunedBranch>,
    /// Solver errors cannot cross `BranchOracle`'s `ExecError` return type;
    /// stash and re-raise in the driver.
    err: Option<crate::util::smtsolver::error::Error>,
}
```

`enter`:

1. `push`, then write `query.decls` and `query.constraints`.
2. If `!enabled` → `Explore`.
3. **Sibling shortcut** — if `query.sibling == 1`, the previous sibling was pruned, and the parent
   context was a definite `Sat`, answer `Explore` without a query: `base ∧ P ∧ c` unsat together
   with `base ∧ P` sat implies `base ∧ P ∧ ¬c` sat. Do **not** apply it when the parent was
   `Unknown`.
4. Otherwise `check_sat()`:
   - `Unsat` → record a `PrunedBranch`, set `last_sibling_pruned = true`, return `Prune`.
   - `Sat` → push `true` onto `known_sat`, return `Explore`.
   - `Unknown` → push `false` onto `known_sat`, return `Explore` (never prune).

`leave`: `pop`, and pop the bookkeeping stacks.

Wire it up in `explore_paths`:

- **Left side.** Replace `collect_paths(left_inl, …)` with a streaming walk driven by
  `execute_streaming_with_oracle(..., Some(&mut left_pruner), &mut |path| …)`, where
  `left_pruner.enabled = opts.check_left`. Left prunes land in
  `DebugRun.left_pruned_branches`. The solver stack at a left terminal is already at the path's
  branch depth, so `write_path` asserts only `decls[reported_decls..]`,
  `constraints[reported_constraints..]`, `return_constraint` — inside one extra `push`/`pop` for
  the terminal, so sibling left paths do not inherit it.

- **Per-left-path terminal check.** Keep today's `check_left` behaviour *in addition*: after the
  left path's `return_constraint` is asserted, `check_sat` once. `Unsat` ⇒
  `LeftPath.reachable = false`, right side not explored. This is **not** redundant with branch
  pruning: `no-abort` and the other claim assumptions constrain `<is-abort-Left>` /
  `<return-value-Left>`, which are only tied to the path once `return_constraint` lands — so a
  left abort path is unsat at its *terminal*, never at a *branch*. Gate it on `opts.check_left`,
  same as today.

- **Right side.** Same, per left path, with `enabled = opts.check_right`. Right prunes land in
  `LeftPath.pruned_branches` (they are only meaningful relative to that left path's context).

- **`check_pair`**: drop the `opts.check_right &&` guard (`driver.rs:644`). **The vacuity check is
  now unconditional.**

New report type:

```rust
#[derive(Debug, Clone, Serialize)]
pub struct PrunedBranch {
    /// `"1.p3"`, `"p2"` — a stable id in the same namespace as path ids.
    pub id: String,
    /// Steps to and including the cut decision.
    pub steps: Vec<StepView>,
    pub label: usize,
    pub line: String,
    /// `then` / `else` / `assert-holds` / `assert-fails` / `unwrap-some` / `unwrap-none`.
    pub decision: String,
}
```

`Summary` gains `left_pruned_branches: usize` and `right_pruned_branches: usize`.
`left_pruned` keeps its current meaning (whole left paths cut at their terminal).

`DebugOptions` documentation flips:

```rust
pub struct DebugOptions {
    /// Prune unreachable LEFT branches as they are reached. Default **on**.
    pub check_left: bool,
    /// Prune unreachable RIGHT branches as they are reached, under the current
    /// left path. Default **on**.
    pub check_right: bool,
    ...
}
// Default: check_left = true, check_right = true
```

Rewrite the `//! ## Branch pruning vs. what story 05 exposes` module-doc block
(`driver.rs:22-39`) — it documents the old limitation and is now wrong.

### 3.3 CLI — `crates/domino/src/cli.rs`, `main.rs`

```rust
/// Do NOT prune unreachable LEFT branches early (default: it does).
#[clap(long)] pub(crate) no_check_left: bool,
/// Do NOT prune unreachable RIGHT branches early (default: it does).
#[clap(long)] pub(crate) no_check_right: bool,
```

`--check-left` is **removed** (the feature is unreleased; no deprecation shim). In `main.rs:148`:

```rust
check_left:  !d.no_check_left,
check_right: !d.no_check_right,
```

`--no-check-right`'s meaning changes: it no longer disables the vacuity check, only early
pruning. Update its `--help` text and say so in the story's implementation report — anyone with
that flag in a script will silently get a *better* answer, but the docs must not lie.

### 3.4 Report — `src/debug/report.rs`, `trace.json`

- Bump `TRACE_SCHEMA` to `2` (`driver.rs:142`) and note the change in
  `docs/stories/07-html-execution-tree-viewer.md`'s schema section.
- `index.html`: render `pruned_branches` as rows in the same list as the right paths, with the
  existing `badge pruned` class and text `pruned at L<label> (unsat)`. They participate in the
  existing `"pruned"` verdict toggle and the text filter. Left-side prunes render as top-level
  rows alongside the left paths.
- Clicking a pruned row shows the same detail panel as a path row: the listing with `steps`
  highlighted and the terminal row replaced by the cut branch line.
- The summary chips gain the two new counts.

### 3.5 stdout — `render_tree`

```
left path #4:
  L5 if (b) {  -> else
  L29 unwrap-2 <- unwrap(MON_CCA_PKE.pk);  -> unwrap-some
  L53 return (c_kem, c_dem);

  right paths under #4:
    #4.1  L3 assert ... -> assert-holds   ...   L65 return c_;   [unsat: ok]
    pruned under #4:
    #4.p1  L3 assert (not ((MOD_CCA_PKE.pk == None))); -> assert-fails   [unsat: branch pruned]
    #4.p2  L23 if (false) { -> then                                      [unsat: branch pruned]

summary: 6 left paths, 7 right paths (34 branches pruned); 0 GOAL FAILS, 2 verified,
         5 unreachable, 0 inconclusive
```

## 4. Acceptance criteria

- [ ] `src/debug/exec.rs` exposes `BranchQuery`, `Feasibility`, `BranchOracle`,
      `execute_streaming_with_oracle`, and `TerminalPath::{reported_decls, reported_constraints}`.
- [ ] `execute` / `execute_streaming` (oracle `None`) produce byte-identical output to today —
      every story-05 test and golden passes **unedited**.
- [ ] A unit test with a mock `BranchOracle` that prunes every `AssertFails` child confirms:
      the returned paths are exactly those without an `assert-fails` step, `leave` is called
      exactly as many times as `enter`, and the call sequence is properly nested.
- [ ] A unit test confirms `leave` still balances `enter` when `on_path` returns
      `ControlFlow::Break` and when `max_paths` trips `ExecError::MaxPathsExceeded`.
- [ ] `--no-check-left --no-check-right` reproduces today's default numbers exactly:
      `PKENC` → 6 left, 96 right, 2 verified, 94 unreachable, 0 goal-fails.
- [ ] Default (both on) on `PKENC` / `same-output`: **strictly fewer** right paths, the same
      `goal_fails` set (0), and `unreachable + verified` still accounts for every explored pair.
      Record the actual numbers in the implementation report.
- [ ] The vacuity check is unconditional: a run with `--no-check-right` still reports at least one
      `Unreachable` on a fixture where one exists (`PKGEN` under `--no-check-left
      --no-check-right`). The old `no_check_right_keeps_the_same_goal_fails_set` test asserted
      `unreachable <= base.unreachable`; it must now assert **equality** for the
      `--no-check-*`-both run.
- [ ] Only `unsat` prunes — a test (or a mock oracle returning `Unknown`) confirms an `unknown`
      branch is still explored.
- [ ] `--timeout 1` still yields `Inconclusive`, never `Verified`, and never a false `GoalFails`.
      Note that with a 1 ms budget the *branch* queries also time out, so nothing is pruned —
      that is correct and the test should assert the un-pruned shape.
- [ ] The weakened-invariant regression still fires: drop the `left.pk = right.pk` conjunct from
      `example-projects/kem-dem/kem-dem-cca-ssp/theorem/invariant.smt2`, run `PKENC` /
      `same-output`, get **≥ 1 `GOAL FAILS`** with a model and a readable path; restore the file
      and get all green. **Pruning must not hide the failure** — this is the single most important
      criterion in the story.
- [ ] Push/pop discipline: assert the solver stack depth returns to its level-0 baseline at the
      end of `explore_paths`, and to the left-path level after each right-side exploration.
- [ ] `transcript.smt2` still replays coherently through `cvc5 --incremental` with the same
      sequence of answers.
- [ ] `trace.json` `schema` is `2`; `index.html` renders pruned rows and they honour the existing
      `pruned` filter toggle.
- [ ] `cargo build --workspace --features cvc5-lib`, `cargo test --workspace --features cvc5-lib`,
      `cargo clippy --workspace --features cvc5-lib` all clean; the default build still works.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh     # from scripts/setup-cvc5-lib.sh
cargo build --workspace --features cvc5-lib

cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino

# the three baselines to beat (record before/after)
for O in PKGEN PKDEC PKENC; do
  $D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle $O --claim same-output | tail -3
done

# the escape hatch must reproduce today's numbers exactly
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output \
    --no-check-left --no-check-right | tail -3
# expect: 6 left paths, 96 right paths; 0 GOAL FAILS, 2 verified, 94 unreachable

# cross-check against the prover — the verdict must agree
$D prove --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
```

Smaller smoke tests first, in this order: `test-projects/test-splitinvoke`,
`example-projects/hello-world`, `example-projects/simple-KEM-example`.

> **Never** run `debug` or `prove` against `example-projects/4WHS` or `example-projects/yao` —
> the two slow projects in `example-projects/known-good-slow.txt`. See
> `docs/stories/00-overview.md` §7.

Build gotcha (overview §7): use `cargo build --workspace`, **not** `cargo build --release` — the
latter does not relink the `domino` binary in `crates/domino`.

## 6. Notes / risks

- **The prune-hides-a-bug risk is the whole risk.** The soundness argument in §2.4 is a one-liner
  but it depends on the encoding staying a plain conjunction. If anything in the per-path encoding
  ever becomes non-monotone, prefix pruning breaks. Put the argument in the module docs of both
  `exec.rs` and `driver.rs`, and keep the weakened-invariant test as the empirical guard.
- **Query count may not drop as much as the row count.** Today `PKENC` runs ~98 `check-sat`s
  (96 vacuity + 2 goal). With pruning it runs one query per fork per surviving prefix — the right
  side has 11 fork points. The win is *legibility and tree shape* first, wall-clock second.
  Measure both and write the numbers down; if wall-clock regresses on any fixture, say so rather
  than hiding it.
- **What actually gets cut, and what does not.** Worth understanding before you start, because it
  sets expectations for the acceptance numbers:
  - Cut at branch level: `if (false)` (trivially unsat); a right `if (b)` whose left counterpart
    took the other branch (`b` is a game constant, equated across sides by
    `emit_constant_declarations`); a right `assert-fails` whose left counterpart asserted the
    negation, when the **old-state invariant** relates the two fields (this is the big one —
    it is what kills most of `PKENC`'s 94).
  - **Not** cut at branch level: anything that depends on `no-abort`, `<is-abort-…>`,
    `<return-value-…>` or `<new-state-…>`. Those are tied to the path only by
    `return_constraint`. Hence the per-left-path terminal check in §3.2 stays.
- **SSA numbering differs between a pruned and an un-pruned run** (a pruned subtree consumes no
  counter values), so `smt` strings in `trace.json` are not comparable across flag settings.
  That is fine — they are internal names — but do not write a test that assumes otherwise.
- Do not try to share right-side branch results across left paths. The right context includes the
  left path's full encoding, so a cut valid under one left path is not valid under another.
- Keep the driver's decisions in the plain `DebugRun` data structure. `report.rs` serialises
  exactly that; do not entangle it with the stdout printer.

## 7. State handed to the next story

There is no next story planned. Record in
`docs/stories/08-branch-level-pruning-IMPLEMENTATION-REPORT.md`:

- The final public surface of `exec.rs` (the `BranchOracle` protocol, including the exact
  ordering and balancing guarantees you ended up with).
- Before/after numbers for `PKGEN` / `PKDEC` / `PKENC` on `same-output`, `equal-aborts` and
  `invariant`: left paths, right paths, pruned branches, verdict counts, wall-clock, and
  `check-sat` count (grep `transcript.smt2`).
- Whether the sibling shortcut (§3.2 step 3) ever fired, and on what.
- Any place where pruning changed a verdict — there should be none; if there is, stop and
  escalate rather than adjusting the expectation.
