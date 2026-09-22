# Epic: Symbolic-Execution Proof Debugger (`domino debug`)

> This is the epic overview. Every story under `docs/stories/` is self-contained, but read this
> file first in each new session — it carries the shared context, the design decisions, the
> testing strategy and the working agreement.
>
> Source of the requirement: `docs/symbolic-execution-plan.md` (written by the project owner).

---

## 1. The problem

When a claim of an equivalence proofstep fails today, `domino prove` gives you one word.

The current encoding is *monolithic*. `src/writers/smt/writer.rs` compiles an entire oracle body
into one deeply nested SMT term of `ite`s and `let`s (that is why the pipeline runs `returnify`,
so every path ends in a `return`, and `treeify`, so every `if` has an `else` and can become an
`ite`). `src/gamehops/equivalence/verify_fn.rs` then declares a handful of constants, asserts
one big `(assert (not (=> (and <assumptions>) <goal>)))`, and fires a single `check-sat`.

If the answer is `unsat`, great. If it is `sat` or `unknown`, you get a cvc5 model over that
whole nested term and no indication of **which execution path through the two games** actually
breaks the claim. Debugging means reading SMT by hand.

## 2. What we are building

`domino debug --proof <T> --proofstep <N> --oracle <O> --claim <C>`:

1. Runs a debug-specific transform pipeline and **inlines** the exported oracle `O` across
   package boundaries for both the left and the right game instance, producing a labelled
   listing where every branch, assertion, unwrap, return and abort has a line number.
2. **Symbolically executes the left oracle** to every terminal (`return` or `abort`), building a
   path condition and a dynamic-single-assignment (DSA) store as it goes. Every assignment gets
   a fresh SSA constant, so the SMT the solver sees is flat and readable instead of nested.
3. For each left terminal path, **symbolically executes the right oracle**, this time asking the
   solver at every branching point which branches are reachable. Only `unsat` prunes a branch;
   `sat`, `unknown` and timeouts are all explored.
4. At every (left terminal, right terminal) pair, checks the claim goal and, when it fails,
   produces a model — pinned to a concrete, human-readable execution path on both sides.
5. Writes a full incremental SMT transcript, the labelled listing, a `trace.json`, and a
   self-contained HTML tree view of left paths with their induced right paths.

## 3. Design decisions (settled with the project owner — do not relitigate)

| Topic | Decision |
|---|---|
| **Solver** | `cvc5-rs` (crates.io crate `cvc5` 0.4, features `static` + `parser`). Its `InputParser` incremental-string mode consumes SMT-LIB text, so the existing `SmtExpr` output is fed verbatim — no rewrite to a term-building API. `Solver`/`Command` are `!Send`/`!Sync`, so a cvc5 instance never crosses a thread; story 14 parallelises `debug` across left paths with **one instance per worker thread** instead. `prove` keeps the process backend and its rayon fan-out. |
| **Inlining** | A new **AST-level** inline transform producing a labelled inlined IR. The textual `src/inline.rs` on branch `amir/ty-params-features` is a pretty-printer only; it is re-implemented on top of the new IR, not ported as-is. |
| **Pipeline** | A debug-specific pipeline **without `treeify`**. `treeify` duplicates every statement following an `if` into both branches purely so the SMT writer can emit `ite`; that would multiply path counts and destroy statement identity, which the labels depend on. |
| **Base frame** | The debugger's base frame carries **datatypes and constants only** — no `(define-fun <oracle-…>)` bodies and no return constraint for any export but the debugged oracle (story 15). Nothing in the run evaluates an oracle function: story 05's per-path DSA encoding replaced it. Since those bodies were the only consumer of `treeify`, `domino debug` runs `DebugTransform` **once** by default; `--with-oracle-functions` restores the full `prove`-shaped frame (and the treeified transform) for cross-checking a verdict. |
| **Claim scope** | `--claim` is **required**. One claim per run. |
| **Assumptions** | The randomness-mapping condition, the invariants on the old game states (main + per-game + per-package) and **all of the claim's dependencies** are asserted up front, before the left oracle is executed. A dependency like `no-abort` will therefore make left abort paths `unsat` — that is intended and visible. |
| **Per-path encoding** | The per-path DSA encoding **replaces** the monolithic `(assert (= <return-X> (oracle-X <old-state> <consts> <args>)))`. `<return-value-X>`, `<is-abort-X>` and `<new-state-X>` stay constrained off `<return-X>`, so `emit_oracle_claim_assert` and the invariant/relation machinery keep working unchanged. |
| **Output** | `index.html` (self-contained, collapsible left→right tree) + labelled `inlined.txt` + `trace.json` + `summary.txt` + per-failure models + a `smt/` tree of runnable per-path queries, under `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`. The monolithic `transcript.smt2` is opt-in (`--transcript`) as of story 11. As of story 17 `summary.txt` holds the **per-path tree** and the concise run report goes to **stdout**. |
| **Guardrails** | `--timeout <ms>` (mapped to cvc5's `tlimit-per`; a timeout counts as *unknown*, i.e. explored, never pruned) and `--max-paths <n>` — **unlimited by default** as of story 10, with `Ctrl-C` as the interactive stop. No depth limit and no first-failure flag. |
| **Labels** | **Line numbers in the emitted inlined listing**: `L12:then`, `L19:assert-holds`, `L27:return`. The listing is the single source of truth for labels. |
| **`domino inline`** | In scope, as its own story, built on the new IR. |
| **Vacuity** | Yes. Before checking the goal at a terminal pair, one extra `check-sat` of the assumptions plus both path conditions. `unsat` there means the pair is **unreachable**, not **verified**. As of story 08 this check is **unconditional** — it is what makes the four verdicts distinguishable, and it is not tied to the `--no-check-left` / `--no-check-right` pruning flags. |

### Label format (agreed with the owner)

```
left path #3:
  L12 if (k != bot)            -> then
  L19 assert (T[h] = bot)      -> holds
  L27 return (Some z)

  right paths under #3:
    #3.1  L14 if (b)  -> then   L31 abort      [sat: GOAL FAILS]
    #3.2  L14 if (b)  -> else   L36 return ..  [unsat: ok]
```

## 4. Architecture at a glance

```
                    domino debug --proof/--proofstep/--oracle/--claim
                                        |
       +--------------------------------+---------------------------------+
       |                                |                                 |
  DebugTransform                  EquivalenceContext                 Cvc5LibSolver
  (story 02)                      (existing + story 04)              (story 01)
  no treeify                      base decls, game defs,             incremental
       |                          constants, invariants,             SMT-LIB text,
       v                          claim assumptions / goal           push / pop
  InlinedOracle (story 02)               |                                 |
  labelled, nested Call frames           |                                 |
       |                                 |                                 |
       +------> SymbolicExecutor (story 05) ------> DebugDriver (story 06) -+
                DSA store, path conditions,         base frame, left paths,
                terminal return/abort encoding      right paths, vacuity,
                                                    goal checks, models
                                                            |
                                                            v
                                                  trace.json + index.html
                                                       (story 07)
```

## 5. Stories and dependency order

| # | Story | File | Depends on |
|---|---|---|---|
| 01 | cvc5-rs solver backend with incremental push/pop | `01-cvc5-backend.md` | — |
| 02 | Debug transform pipeline + labelled inlined-oracle IR | `02-debug-pipeline-and-inlined-ir.md` | — |
| 03 | `domino inline` command | `03-inline-command.md` | 02 |
| 04 | Split claim assumptions from the goal; skippable return constraint | `04-claim-assumptions-and-goal-split.md` | — |
| 05 | Symbolic executor core (no solver) | `05-symbolic-executor-core.md` | 02 |
| 06 | `domino debug`: solver-guided exploration and claim checking | `06-debug-command-solver-guided.md` | 01, 04, 05 |
| 07 | HTML execution-tree viewer + `trace.json` | `07-html-execution-tree-viewer.md` | 06 |
| 08 | Branch-level pruning on both sides | `08-branch-level-pruning.md` | 05, 06, 07 |
| 09 | Live exploration progress + partial artifacts | `09-live-progress.md` | 06, 07 |
| 10 | Path totals, honest bars, unlimited `--max-paths`, responsive `Ctrl-C` | `10-path-totals-and-interruption.md` | 05, 06, 08, 09 |
| 11 | Per-path SMT files instead of one huge transcript | `11-per-path-smt-files.md` | 06, 09 |
| 12 | Concise run report (`summary.txt`) + explicit stop reason | `12-run-summary-report.md` | 06, 09, 10 |
| 13 | Collapsible HTML detail pane + the claim assertion | `13-html-collapsible-and-goal-assertion.md` | 06, 07 |
| 14 | Parallel path exploration (`--jobs`) | `14-parallel-exploration.md` | 06, 08, 09, 10, 12 |
| 15 | No oracle function definitions in the debugger's base frame | `15-no-oracle-functions-in-debug-frame.md` | 04, 05, 06, 11 |
| 16 | Paint the executed lines in the viewer's listings | `16-executed-line-highlighting.md` | 02, 05, 06, 07, 13 |
| 17 | Concise report on stdout, path tree in `summary.txt` | `17-stdout-summary-swap.md` | 06, 09, 12 |
| 18 | Symbolic return value and new state of each returning path | `18-symbolic-effect-of-a-path.md` | 02, 05, 06, 07, 13 |

Stories 01, 02 and 04 are independent and may be done in any order (or in parallel). Stories 08
and 09 are independent of each other; whichever lands second wires a one-way hook (see `09` §3.6).

Stories 01–09 are **done** (each has an `-IMPLEMENTATION-REPORT.md` next to it). Stories 10–15 are
a second wave from the owner's follow-up review of `domino debug`; 16–18 are a third.
10–13, 15, 16 and 18 are independent of each other and may land in any order; each bumps
`TRACE_SCHEMA` by one, so whichever lands second bumps from whatever it finds and records the
number in its report. **Story 14 goes last** — it reuses 10's events and cancellation, 12's
`StopReason`, 11's `SmtWriter` and 13's `goal_smt`, and it benefits from 15 making the per-worker base frame ~4× smaller.

## 6. Working agreement (important)

- Implementation is done by **Sonnet in extra-high thinking mode**, **one story per session**,
  with the **context reset after each story is finished**.
- Because of the context reset, **every story file is self-contained**. It restates the context
  it needs, names concrete files and signatures, and lists what earlier stories left behind.
  If while implementing you discover a fact a later story will need, add it to that story's
  "Inherited from earlier stories" section before you finish.
- Every story ends with **"State handed to the next story"**. Keep it accurate — it is the only
  thing the next (cold) session knows about your work besides the code itself.
- Each story is one reviewable commit/PR on branch `amir/symbolic-execution-debugger`.
- Do not expand scope beyond the story you were given. If something outside it is broken, note
  it in the story's "Notes for follow-up" and move on.

## 7. Testing strategy (applies to every story)

### Hard rule

> **Never run `domino prove`, `domino debug`, `domino latex` or `scripts/test-known-examples.sh`
> against `example-projects/4WHS` or `example-projects/yao`.**

Those two are listed in `example-projects/known-good-slow.txt`. `scripts/test-known-examples.sh`
deliberately only runs `domino proofsteps` (parse-only) on them because proving them takes a very
long time. Do not "just try it once" — it will burn the session.

### Test ladder, fastest first

1. **Unit tests** — `cargo test --workspace`. The primary safety net for stories 01, 02, 04, 05.
2. **`test-projects/*`** — tiny, prove in seconds. Projects named `err-*` are *expected to fail*;
   all others are expected to succeed. Useful shapes:
   - `test-projects/test-loopunroll` — bounded `for` loops (exercises `loopunroll`).
   - `test-projects/test-splitinvoke` — cross-package `invoke` (exercises inlining).
   - `test-projects/test-param-instantiation` — package/game parameters.
3. **`example-projects/hello-world`**, **`example-projects/simple-KEM-example`** — smallest real
   proofs; good first end-to-end smoke tests for `inline` and `debug`.
4. **`example-projects/kem-dem/kem-dem-cca-ssp`** — **the primary end-to-end target for this
   epic.** Proofstep 0 is
   `equivalence Game_MON_CCA_PKE Game_MOD_CCA_PKE_Real_KEM` (`theorem/Proof.ssp:237`) with
   oracles `PKGEN`, `PKENC`, `PKDEC` and claims `invariant`, `same-output`, `equal-aborts`, plus
   the admitted `lemma-kem-correctness`. It has real branching, sampling, cross-package invokes
   (`MON_CCA_PKE` → `Scheme_PKE`; `MOD_CCA_PKE` → `KEM`/`DEM`/`Key`) and a hand-written
   `theorem/invariant.smt2`, and it still runs in reasonable time. Every end-to-end acceptance
   criterion in these stories is phrased against it.
5. **`scripts/test-known-examples.sh`** — run only for story 04, the one story that touches code
   `prove` executes. The script already skips the slow projects.

### Build gotcha

```bash
cargo build --workspace          # correct
cargo build --release            # WRONG: does not relink the `domino` binary in crates/domino
```

### Representative commands

```bash
cargo build --workspace
cd example-projects/kem-dem/kem-dem-cca-ssp

domino proofsteps                                                     # proofstep 0 is the equivalence
domino inline --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC
domino debug  --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
domino prove  --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output  # cross-check
```

Always narrow with `--oracle` and `--claim` rather than running a whole project.

## 8. Reference: facts about the existing code

These are load-bearing for several stories; each story restates the ones it needs.

- **Transform pipeline.** `EquivalenceTransform` (`src/transforms/theorem_transforms.rs:40`)
  calls `transform_game_inst` (line 57), which runs, in order:
  `type_extract → deconstructinvoke → unwrapify → resolveoracles → samplify → loopunroll →
  sample_max_counter_extractor → returnify → treeify → tableinitialize`,
  returning `GameInstAux { types, sample_info, max_offsets }` per game instance.
- **`assert (c)` is sugar** for `if (c) {} else { abort; }` — an `IfThenElse` whose `then_block`
  is empty and whose `else_block` is exactly one `Statement::Abort`.
- **`unwrapify`** (`src/transforms/unwrapify.rs`) hoists nested `unwrap`s into assignments whose
  RHS is an `ExpressionKind::Unwrap`. `src/writers/smt/writer.rs:899` turns each such assignment
  into `if (inner = (as mk-none (Maybe T))) then abort else <bind (maybe-get inner)>`. Those
  assignments are the unwrap branch points.
- **`abort` propagates.** `smt_build_invoke` (`src/writers/smt/writer.rs:771`) makes a callee's
  abort abort the whole oracle, after writing the caller's locals back into the game state. So
  `abort` is always a *global* terminal, even several frames deep.
- **Claim encoding** lives in `src/writers/smt/contexts/equivalence/emit.rs`:
  `emit_base_declarations`, `emit_theorem_paramfuncs`, `emit_game_definitions`,
  `emit_constant_declarations` (calls the free functions `build_returns` and `build_rands`),
  `emit_auto_randomness`, `emit_invariant`, `emit_return_value_helpers`,
  `emit_randomness_mapping_condition`, `emit_oracle_claim_assert`.
- **Solver abstraction**: `SmtSolver` / `SmtSolverBackend` in `src/util/smtsolver/mod.rs`;
  process implementation in `src/util/smtsolver/process.rs`. There is no `push`/`pop` yet.
- **SMT builders reusable at terminals**: `OracleContext::smt_construct_return`,
  `smt_construct_abort`, `smt_write_back_state`, `smt_access_return_state`,
  `smt_access_return_value`; `GameInstanceContext::smt_update_gamestate_pkgstate`,
  `smt_access_gamestate_rand`, `smt_increment_gamestate_rand`;
  `PackageInstanceContext::smt_update_pkgstate_from_locals`, `smt_access_pkgstate`.
- **Expression substitution** for DSA: `Expression::map` (`src/expressions.rs:90`) and
  `Expression::mapfold` (`src/expressions.rs:228`), as used by `unwrapify`.
- **No HTML infrastructure exists on this branch.** The viewer in story 07 is written from
  scratch as a single dependency-free file.
