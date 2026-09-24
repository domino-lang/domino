# Story 23 — Lockstep execution and `domino debug --easycrypt`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first (§3 rows
"Debugger", "Lockstep rules", "EasyCrypt-mode claims"; glossary in `CONTEXT.md` § Debugging).
**Branch:** `amir/easycrypt-export`
**Depends on:** 20 (hello-world exports), 22 (plumbing branches in the IR).
**Blocks:** 24 (viewer), 27 (tactic generation walks this engine's joint tree).
**Supersedes:** story 09.

---

## 1. Why this story exists

The owner's requirement (`docs/easycrypt-interaction-and-branching.md`) is:

> Domino debugger in EasyCrypt mode operating on EasyCrypt code attempts a synchronized execution
> on both sides and tracks how much code it consumes to reach every decision point on left and
> right. If it hits a decision point only on left or right or the decision points are not
> equivalent, it considers all four cases and uses smt in the debugger to see which ones it
> actually goes in and continue execution there. If we hit a randomness only on one side we admit
> there for now!

Today's debugger does **sequential exploration**: every left path, then every right path under it.
An EasyCrypt pRHL proof instead advances both programs together and decides each branch jointly.
**Lockstep execution** is the debugger doing the same, so that:

1. on its own, `domino debug --easycrypt` tells the user, per **joint path**, whether equal-output
   and the invariant hold, and where an EasyCrypt proof would be stuck;
2. story 27 can turn the joint tree into tactics.

This must work **without EasyCrypt installed** (owner: "we don't want to rely on EasyCrypt for
debugging").

## 2. Inherited from earlier stories

- **The IR.** `inline_oracle_ec(game_inst, oracle) -> InlinedOracle`
  (`src/writers/easycrypt/lower.rs`), with `game_inst` from `EasyCryptTransform`. **Execute it
  against the Domino (`DebugTransform`) game instance and its `sample_info`**. State places,
  sample ids and entry returns are Domino's (story 08 §6). Since story 22, `Branch.plumbing` marks
  plumbing branches; a `DoneGuard`'s condition is the literal `true`.
- **Executor** (`src/debug/exec.rs`, ≈2200 lines):
  - it walks one `InlinedOracle` DFS to every terminal, using a `Cursor` stack of frames and a
    `SymState` (DSA store, path condition, `rand_ctr`);
  - `do_sample` binds the draw `(<rand-fn of game inst, type> <sample position> <counter>)` and
    bumps the counter;
  - `BranchOracle` / `Feasibility` is the hook for solver pruning at every fork (story 08);
  - **only `unsat` prunes; `unknown` is always explored.** This is the tool's safety property.
- **Driver** (`src/debug/driver.rs`, ≈2500 lines):
  - `run_debug_command`, `explore_paths`, `handle_left_path`/`handle_right_path`, `check_pair`
    (vacuity check first, then goal);
  - `SolverPruner`, `Verdict { Verified, Unreachable, GoalFails, Inconclusive }`,
    `TRACE_SCHEMA = 8`, `DebugEvent` progress (`src/debug/progress.rs`);
  - per-path SMT files (`src/debug/smtout.rs`);
  - the base frame comes from `EquivalenceContext` (`emit_auto_randomness`,
    `emit_randomness_mapping_condition`, invariants, claim assumptions).
- **Randomness mapping** (`src/writers/smt/contexts/equivalence/emit.rs:606`): for every candidate
  `(left sample id, right sample id, offsets)` of matching type, the condition asserts
  `randomness-mapping-<O>(…) ⇒ rand_L(…) = rand_R(…)`. `randomness_mapping_candidates` enumerates
  the candidates. The mapping may depend on state and arguments.
- **CLI** (`crates/domino/src/cli.rs`, `Commands::Debug`): `--path --proof --proofstep --oracle
  --claim --no-check-left --no-check-right --timeout --max-paths --progress --smt --transcript
  --out`. Output defaults to `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`.
- `src/debug/effect.rs` (symbolic-execution story 18): a path's symbolic return value and new
  state. Reuse it for the per-terminal detail.

## 3. Work to do

### 3.1 CLI

`domino debug --easycrypt --proof T --proofstep N --oracle O`:

- `--claim` is **rejected** with `--easycrypt`: both claims are always checked. Without
  `--easycrypt`, `--claim` stays required and everything is byte-identical to today.
- `--no-check-left`, `--no-check-right` and any other flag with no lockstep meaning are rejected
  with an error naming the flag.
- `--timeout`, `--max-paths` (counts **joint paths**), `--progress`, `--smt`, `--transcript` and
  `--out` keep their meaning.
- Output directory: `_build/debug/<theorem>/<left>-<right>/<oracle>/easycrypt/`.

### 3.2 Assumptions and goals

- **Assumed**, up front:
  - the invariant on the old states (main + per-game + per-package, exactly as `prove` asserts it);
  - the randomness-mapping condition and `emit_auto_randomness`;
  - the oracle arguments, which are shared symbols on both sides, as today.
- **Not assumed:** any claim dependency, `no-abort`, or **any project lemma**. The owner wants to
  see what is provable without them, because EasyCrypt won't have them.
- **Checked at every terminal pair**, after the unconditional vacuity check:
  - **equal-output**: both sides abort, or neither does and their return values are equal. Build
    it from the `equal-aborts` and `same-output` goal formulas without their dependencies. **First
    verify** that `same-output`'s formula means something when a side aborts. If it doesn't,
    define equal-output directly over `<is-abort-X>` and `<return-value-X>`, and say which you did.
  - **invariant**: the `invariant` claim's goal, on the new states.
  - **per-relation sub-verdicts**: whenever the invariant verdict is not `Verified`/`Unreachable`,
    check each **state relation** separately. Use the list of relations the EasyCrypt `inv`
    operator conjoins (story 06's translation builds it), so Domino's parts line up one for one
    with the parts story 27 admits.

  Each check yields a `Verdict`; the existing model and SMT-file writing applies per failing check.

### 3.3 The lockstep engine

Build a new module (suggested `src/debug/lockstep.rs`) that owns **one cursor per side** and walks
the **joint tree** DFS. The executor is currently a whole-path walker. Extract from it what a side
cursor needs: advancing over one statement with its `SymState`, and binding samples, calls and
returns. The sequential walker must keep producing byte-identical results (run its test suite
unchanged). Keep the engine **listing-agnostic**: it takes two `InlinedOracle`s. Lockstep on the
Domino listing is a follow-up for `amir/symbolic-execution-debugger`, not this story.

**Advance.** Each side consumes `Assign`, call entry/exit and callee `Return` until it stands at a
**decision point**: a `Branch`, a `Sample`, or a terminal (`Return` at the entry frame, `Abort`).
Record the labels consumed on each side. They are for the viewer only; story 27 does **not** use
them as EasyCrypt positions (ADR 0002).

**Joint decision.** With `A` = assumptions and `pc` = both path conditions, apply the first rule
that fits:

1. **Determined branch.** Some side's branch condition `c` has `A ∧ pc ∧ ¬c` unsat (it holds) or
   `A ∧ pc ∧ c` unsat (it fails). That side takes the determined child alone. Try left before
   right. If both queries are unsat, the joint node is unreachable; prune it. Plumbing
   `DoneGuard`s always resolve here.
2. **Synchronized branch.** Both sides are at undetermined branches and `A ∧ pc ∧ (c_L xor c_R)`
   is unsat. There are two children, (then, then) and (else, else).
3. **Split.** Any other branch situation. With both sides at branches, there are four
   combinations; with one side at a branch, that side's two outcomes and the other side unchanged.
   Prune each combination whose conjunction is unsat. **Branches before samplings:** a side at a
   sampling waits while the other side resolves its branches.
4. **Samplings.** Let `v_L`, `v_R` be the draws the executor would bind (`do_sample`'s term).
   - **Synchronized sampling:** both sides at samplings and `A ∧ pc ∧ v_L ≠ v_R` is unsat. Consume
     both.
   - Otherwise classify each side's head sampling on its own. It is **independent** when, for
     every candidate the randomness mapping could pair it with, the mapping's premise is unsat
     under `A ∧ pc`. Consume it alone, left first.
   - Otherwise, including any `unknown`, it is a **stuck point**. Record it, consume that sampling
     with Domino's semantics (the draw is still the `rand` term, so the mapping keeps constraining
     it), and continue. Left first when both are stuck. **Never classify by reading the mapping's
     text**; it may depend on state and arguments.
5. **Terminal pair.** Both sides at terminals: run §3.2's checks.

Every child of a split or synchronized node resumes lockstep. A side at a terminal stays there
while the other side advances.

**Identifiers.** Assign them deterministically in DFS order (then before else, left before right):

- `J<n>` for joint paths;
- `S<n>` for stuck points.

An unchanged project must give identical ids across runs. Story 27 writes them into
`admit (* domino: S3 … *)` comments.

### 3.4 Artifacts

- `trace.json`: `TRACE_SCHEMA` 9 with `"mode": "lockstep"` and `"listing": "easycrypt"`. Schema
  8 traces are unaffected, because sequential runs keep writing 8. The trace records:
  - the **joint tree**: nodes with kind (`determined`, `synchronized`, `split`,
    `sampling-synchronized`, `sampling-independent`, `stuck`, `terminal-pair`), per-side
    label, decision and consumed labels, whether the branch is `plumbing`, pruned children, and
    solver answers;
  - the stuck points: id, labels, reason (`partner-not-at-head`, `pairing-sat-not-valid`,
    `pairing-unknown`, `no-partner-reachable`);
  - per terminal pair: both verdicts and the per-relation sub-verdicts.
- `summary.txt`: the joint tree as text, in the story-17 style.
- stdout concise report:
  - counts of terminal pairs per `(equal-output, invariant)` verdict pair;
  - the stuck points with their labels;
  - per-relation failure counts;
  - the stop reason.
- Per-failure models and `smt/` files exactly as today, keyed by joint path.
- **No `index.html`** in this story. Story 24 builds the joint-tree viewer. Write a one-line
  placeholder page pointing to `summary.txt`, so the directory layout is final.
- Live progress (`--progress`): add lockstep events (joint node entered, pair checked, stuck point
  found). Flush partial `trace.json`/`summary.txt` periodically, and honour `Ctrl-C` as
  sequential runs do.

## 4. Acceptance criteria

- [ ] `domino debug --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC` completes
      and writes the artifacts. The same holds for `PKDEC` (which has abort paths) and for
      hello-world `UsefulOracle`.
- [ ] Every plumbing branch appears in the joint tree as a `determined` node.
- [ ] **One-directional consistency test** (`cvc5-lib` feature). For each of the three cases,
      compare with sequential `domino debug` on the **Domino** listing:
      - if lockstep verifies equal-output on every reachable joint path, sequential
        `equal-aborts` and `same-output` report no `GoalFails`;
      - if sequential `invariant` reports `GoalFails` on a pair and the claim has no
        dependencies, lockstep reports an invariant failure somewhere.
      
      A violation is a lowering or engine bug; report it, don't paper over it.
- [ ] A unit test with a hand-built pair of `InlinedOracle`s exercises each rule of §3.3 in
      isolation, including a mapping that depends on an argument, where the sampling must be
      `stuck` with reason `pairing-sat-not-valid`.
- [ ] Two runs on an unchanged project give identical `trace.json` and identical `J`/`S` ids.
- [ ] Without `--easycrypt`, every output is byte-identical to today.
- [ ] `cargo build/test/clippy --workspace` clean, including `--features cvc5-lib` (say so if it
      could not build: story 08 hit `cmake: command not found`).

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D debug --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC
cat _build/debug/*/*/PKENC/easycrypt/summary.txt
```

> **Never** run `debug` against `example-projects/4WHS` or `example-projects/yao`.

## 6. Notes / risks

- **Path explosion from splits.** Four-way splits multiply. Pruning keeps kem-dem small; report
  joint-path counts next to the sequential left × right counts.
- **Invariant vs abort.** EasyCrypt's `inv` guards the relations under `!abort_flag` (story 06).
  Check how Domino's `invariant` claim treats a terminal pair where a side aborts. If the two
  differ, record the difference in the report. **Do not change `prove`'s semantics.**
- **Don't special-case the encoder.** If a lowered construct doesn't encode, the provenance rule
  of story 08 has leaked; fix it there.
- `Unwrap` never occurs in the EasyCrypt IR (story 08 §3.1). If the engine meets one (a future
  Domino-listing lockstep), treat it as a branch on `inner = None`.

## 7. State handed to the next story

Record in `23-…-IMPLEMENTATION-REPORT.md`:

- the engine's module and public API, which story 27 drives node by node, so expose an
  iterator/visitor over the joint tree rather than only a finished `DebugRun`;
- the joint-node kinds and the trace schema 9 layout;
- how equal-output was built;
- the relation list's source;
- the id scheme;
- kem-dem and hello-world joint-path counts, stuck points and run times;
- the consistency-test results.
