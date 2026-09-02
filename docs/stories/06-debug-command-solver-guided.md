# Story 06 — `domino debug`: solver-guided exploration and claim checking

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 01 (cvc5 backend + push/pop), story 04 (assumption/goal split), story 05
(symbolic executor). Story 03 is optional but useful.
**Blocks:** story 07.

---

## 1. Why this story exists

This is the story that makes the epic real: the command a user actually runs when a claim fails.
Everything before it is scaffolding.

The shape, from `docs/symbolic-execution-plan.md`:

> For the selected oracle, it symbolically executes the left oracle until each return or abort
> point. […] With the left oracle finished, the fun debugging part starts by symbolically
> executing the right oracle with all the path conditions and initial conditions. However, this
> time whenever it hits a branching point it queries the solver for which branch it should take.
> […] When the right oracle also hits an abort or return, then the actual goal of the claim is
> checked. If it fails, we can give precise possible execution path causing the error.

## 2. Inherited from earlier stories

### From story 01 — `src/util/smtsolver/`

- `SmtSolver::{write_smt, check_sat, get_model, push, pop, set_option, close}`. `push`/`pop`
  emit `(push 1)`/`(pop 1)`; `set_option` emits `(set-option :key value)`.
- `src/util/smtsolver/cvc5lib.rs` (feature `cvc5-lib`) with
  `Cvc5LibBackend { produce_models: bool, tlimit_per_ms: Option<u64> }` (`impl SmtSolverBackend`,
  ctor `Cvc5LibBackend::new(produce_models, tlimit_per_ms)`) and `Cvc5LibSolver: SmtSolver`, built
  on `cvc5`'s `InputParser` incremental-string mode, teeing every appended byte to an optional
  transcript writer.
- **`Cvc5LibSolver` is `!Send`/`!Sync`.** It cannot satisfy `SmtSolverBackend + Sync` on
  `EquivalenceSmtDriver`. The debugger needs its own single-threaded driver; do not parallelise
  and do not route `prove` through it.
- Construction sets `:produce-models`, `:incremental true`, and `:tlimit-per <ms>` when given.
  Per-query timeout is changed later via `solver.set_option("tlimit-per", "<ms>")`.
- `check_sat` returns `Unknown` for a `tlimit-per` timeout (cvc5 answers `unknown`); an
  `(error "…")` reply becomes `Error::SolverError`.
- **Build:** run `scripts/setup-cvc5-lib.sh` once, then `source ~/.cache/domino/cvc5-lib-env.sh`
  before any `cargo … --features cvc5-lib`. Full detail + API quirks:
  `docs/stories/01-cvc5-backend-IMPLEMENTATION-REPORT.md`.

### From story 04 — `src/writers/smt/contexts/equivalence/emit.rs`

- `EquivalenceContext::emit_claim_assumptions(&Claim, &str) -> Vec<SmtExpr>` — one
  `(assert <dep>)` per assumption.
- `EquivalenceContext::emit_claim_goal_negated(&Claim, &str) -> SmtExpr` —
  `(assert (not <goal>))`.
- `EquivalenceContext::emit_constant_declarations(Option<&str>) -> Vec<SmtExpr>` — with
  `Some(oracle)`, `<return-oracle>` is **declared but unconstrained** on both sides, while
  `<return-value-…>`, `<is-abort-…>` and `<new-state-…>` stay constrained off it.

### From story 05 — `src/debug/exec.rs`

- `execute` / `execute_streaming` producing
  `TerminalPath { id, steps, decls, constraints, return_constraint, terminal }`.
- Asserting `decls + constraints + return_constraint` on top of the base declarations is a
  complete, sound encoding of exactly that one path.
- `Decision::{Then, Else, AssertHolds, AssertFails, UnwrapSome, UnwrapNone}`.

### From story 02 — `src/debug/ir.rs`

- `inline_oracle(game_inst, oracle_name) -> InlinedOracle`, `Label` = 1-based line number in
  `InlinedOracle::listing.text`, `listing.sites: BTreeMap<Label, SiteInfo>`.

### From story 03 (optional)

- `crate::debug::render::render_side_by_side(...)` for `inlined.txt`.

## 3. Existing code to reuse

`src/project/mod.rs::Project::prove` (line 102) is the template for how a proofstep is set up:

```rust
GameHop::Equivalence(eq) => {
    let (theorem, auxs) = EquivalenceTransform.transform_theorem(theorem)?;
    let mut eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
    eqctx.load_invariants(self)?;
    let mut driver = EquivalenceSmtDriver::new(&eqctx, self, backend, transcript, ...);
    driver.verify(&mut ui)?;
}
```

`debug` does the same but with `DebugTransform` instead of `EquivalenceTransform`.
`load_invariants` (`src/gamehops/equivalence/mod.rs:242`) reads the package, game and main
invariant `.smt2` files and rewrites them per game instance — **you need it**; the invariants are
the debugger's main assumptions.

The claim list for an oracle comes from
`Equivalence::proof_tree_by_oracle_name(oracle_name) -> Vec<Claim>`
(`src/gamehops/equivalence/mod.rs:92`), plus the generated package/game invariant claims built by
`EquivalenceSmtDriver::generate_game_or_package_invariant_claims`
(`src/gamehops/equivalence/verify_fn.rs:271`). Lift that generation into something the debug
driver can call too (a free function or a method on `EquivalenceContext`) rather than duplicating
it. Note `Claim::is_admitted()` — an admitted claim has nothing to check; say so and exit
cleanly rather than pretending to verify it.

Output paths: follow `Project::get_smt_file` (`src/project/mod.rs:238`), which builds
`_build/code_eq/<theorem>/<left>-<right>/<claim_group>/<claim>.smt2`.

## 4. Work to do

### 4.1 CLI — `crates/domino/src/cli.rs` and `main.rs`

```rust
/// Symbolically execute both sides of an equivalence proofstep and debug one claim.
Debug(Debug),

#[derive(clap::Args, Debug)]
pub(crate) struct Debug {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)] pub(crate) path: Option<std::path::PathBuf>,
    /// Name of the theorem.
    #[clap(long)] pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep, as printed by `domino proofsteps`.
    #[clap(long)] pub(crate) proofstep: usize,
    /// Exported oracle name.
    #[clap(long)] pub(crate) oracle: String,
    /// Claim to debug. Required — one claim per run.
    #[clap(long)] pub(crate) claim: String,
    /// Ask the solver which branches of the LEFT oracle are reachable (default: explore all).
    #[clap(long)] pub(crate) check_left: bool,
    /// Do NOT ask the solver about the RIGHT oracle's branches (default: it does ask).
    #[clap(long)] pub(crate) no_check_right: bool,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`).
    #[clap(long)] pub(crate) timeout: Option<u64>,
    /// Give up after this many explored paths (left paths + right paths per left path).
    #[clap(long, default_value_t = 1000)] pub(crate) max_paths: usize,
    /// Output directory. Defaults to `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`.
    #[clap(long)] pub(crate) out: Option<std::path::PathBuf>,
}
```

`--proof`, `--proofstep`, `--oracle` and `--claim` are all required; clap enforces that by them
not being `Option`.

### 4.2 Driver — `src/debug/driver.rs`

**Base frame**, asserted once and left on the bottom of the solver stack:

1. `eqctx.emit_base_declarations()`
2. `eqctx.emit_theorem_paramfuncs()`
3. `eqctx.emit_game_definitions()`
4. `eqctx.emit_constant_declarations(Some(oracle_name))`   ← story 04
5. `eqctx.emit_auto_randomness(oracle_name)`
6. `eqctx.emit_invariant(oracle_name)`                      ← needs `load_invariants` first
7. `eqctx.emit_return_value_helpers(oracle_name)`
8. `eqctx.emit_randomness_mapping_condition(oracle_name)`
9. `eqctx.emit_claim_assumptions(&claim, oracle_name)`      ← story 04

Note this is the same order and the same content `verify_fn.rs` uses, with (4) narrowed and (9)
split out. Step 3 emits the oracle function definitions too; keep them — they are cheap and they
make the transcript self-contained and cross-checkable.

**Exploration**, with push/pop mirroring the tree exactly:

```
assert base frame                                   (level 0)
for each left path P:                               (streaming, story 05)
    if --check-left: prune P's branches as they are taken (see below)
    push                                            (level 1)
    assert P.decls, P.constraints, P.return_constraint
    for each right path Q:
        if right checks on (default): prune Q's branches as they are taken
        push                                        (level 2)
        assert Q.decls, Q.constraints, Q.return_constraint
        # vacuity
        r = check-sat
        if r == Unsat: record Unreachable; pop; continue
        push                                        (level 3)
        assert emit_claim_goal_negated(claim, oracle)
        r = check-sat
        match r:
            Unsat   -> Verified
            Sat     -> GoalFails   + get-model
            Unknown -> Inconclusive + attempt get-model
        pop                                         (level 2)
        pop                                         (level 1)
    pop                                             (level 0)
```

**Branch pruning.** At a branching point the executor is about to fork on condition `c`:
`push; assert c; check-sat; pop` and then the same for `(not c)`.

- `Unsat` → that branch is unreachable; **do not explore it**, and record it as pruned so the
  tree can show it.
- `Sat`, `Unknown`, or a timeout → **explore it**. Only `unsat` ever prunes. This is explicit in
  the plan document and is the safety property of the whole tool: the debugger must never hide a
  reachable path.

Wire this to story 05's `execute_streaming` so pruning happens during exploration rather than
after; that is the difference between "a few dozen queries" and "combinatorial".

**Timeout.** `--timeout` sets cvc5's `tlimit-per` at construction (story 01's
`Cvc5LibBackend`) and/or via `set_option`. A timed-out query returns `Unknown`, which by the rule
above means *explored* / *inconclusive*, never pruned and never "verified".

**`--max-paths`.** Counts left paths plus right paths per left path. On exceeding it, stop, print
a clear message naming how many of each were explored and that the result is partial, and still
write all artifacts. Exit non-zero.

### 4.3 Verdicts

```rust
pub enum Verdict {
    Verified,                 // goal check unsat
    Unreachable,              // vacuity check unsat — the pair cannot happen
    GoalFails { model: PathBuf },     // goal check sat
    Inconclusive { model: Option<PathBuf> },  // goal check unknown / timed out
}
```

Distinguishing `Unreachable` from `Verified` is a deliberate decision from the interview: a run
that is all-green because every pair is vacuous looks identical to a genuinely passing run
otherwise, and that is exactly the bug you want to catch.

### 4.4 Artifacts

Under `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/` (or `--out`):

- `transcript.smt2` — every command sent, in order, including `(push 1)` / `(pop 1)` /
  `(check-sat)` / `(get-model)`. This is story 01's transcript writer, unmodified.
- `inlined.txt` — the labelled side-by-side listing (story 03's renderer, or the listings
  directly if story 03 has not landed). This is what the `L<n>` labels index into.
- `models/<path-id>.smt2` — one per `GoalFails` / `Inconclusive` pair.
- stdout: the text tree.

### 4.5 stdout format

Exactly the format agreed with the owner:

```
theorem kem_dem_cca_ssp, proofstep 0 (Game_MON_CCA_PKE == Game_MOD_CCA_PKE_Real_KEM)
oracle PKDEC, claim same-output
listing: _build/debug/.../inlined.txt

left path #3:
  L12 if (k != bot)            -> then
  L19 assert (T[h] = bot)      -> holds
  L27 return (Some z)

  right paths under #3:
    #3.1  L14 if (b)  -> then   L31 abort      [sat: GOAL FAILS]  models/3.1.smt2
    #3.2  L14 if (b)  -> else   L36 return ..  [unsat: ok]

summary: 7 left paths, 11 right paths; 1 GOAL FAILS, 9 verified, 1 unreachable
```

Path ids: left paths `#1, #2, …` in exploration order; right paths `#<left>.<n>`.
Left and right line numbers are independent (they index different columns of `inlined.txt`) —
say so in the header.

Exit code: `0` if every pair is `Verified` or `Unreachable`; non-zero otherwise.

## 5. Acceptance criteria

- [ ] `domino debug --proof <T> --proofstep <N> --oracle <O> --claim <C>` runs end to end and
      writes `transcript.smt2`, `inlined.txt` and any models.
- [ ] The transcript is a single coherent incremental session: replaying it through
      `cvc5 --incremental` from the shell reproduces the same sequence of `sat`/`unsat`/`unknown`
      answers.
- [ ] Only `unsat` prunes a branch. A test (or an `--debug`-level log assertion) confirms that a
      branch answered `unknown` is still explored.
- [ ] `--check-left` reduces the number of left paths on a project where some left branch is
      genuinely unreachable under the assumptions, and changes no verdict.
- [ ] `--no-check-right` explores at least as many right paths and produces the same set of
      `GoalFails` verdicts.
- [ ] `--timeout 1` (absurdly small) yields `Inconclusive`, never `Verified`.
- [ ] `--max-paths 3` stops early, says so clearly, and exits non-zero.
- [ ] An admitted claim (`Claim::is_admitted()`) is reported as admitted, not silently verified.
- [ ] On `example-projects/kem-dem/kem-dem-cca-ssp` with an intentionally weakened
      `theorem/invariant.smt2`, at least one pair reports `GOAL FAILS` with a model and a readable
      path; with the invariant restored, every pair is `Verified` or `Unreachable`.
- [ ] `cargo build --workspace --features cvc5-lib` and
      `cargo test --workspace --features cvc5-lib` pass; the default build still works.

## 6. How to verify

```bash
cargo build --workspace --features cvc5-lib

cd example-projects/kem-dem/kem-dem-cca-ssp
cargo run --features cvc5-lib --bin domino -- proofsteps

# the happy path — everything should be verified/unreachable
cargo run --features cvc5-lib --bin domino -- debug \
    --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC --claim same-output

# cross-check against the prover on the same claim
cargo run --bin domino -- prove \
    --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC --claim same-output

# the failing path — weaken theorem/invariant.smt2, rerun debug, expect a GOAL FAILS pair,
# then restore the file
```

`kem-dem-cca-ssp` proofstep 0 is `equivalence Game_MON_CCA_PKE Game_MOD_CCA_PKE_Real_KEM`
(`theorem/Proof.ssp:237`) with oracles `PKGEN`, `PKENC`, `PKDEC` and claims `invariant`,
`same-output`, `equal-aborts`, plus the admitted `lemma-kem-correctness`. Start with `PKGEN`
(smallest), then `PKDEC`, then `PKENC` (sampling + the most invokes).

Smaller smoke tests first: `test-projects/test-splitinvoke`, `example-projects/hello-world`,
`example-projects/simple-KEM-example`.

> **Never** run `debug` or `prove` against `example-projects/4WHS` or `example-projects/yao`.
> They are the slow projects in `example-projects/known-good-slow.txt` and will burn the session.
> See `docs/stories/00-overview.md` §7.

## 7. Notes / risks

- **Assumptions prune abort paths.** With `no-abort` among the claim's dependencies, every left
  path ending in `Abort` becomes `unsat`. Under `--check-left` they vanish; without it they show
  up as `Unreachable` at the terminal pair. Both are correct and both should be legible in the
  output — do not "fix" this.
- **Push/pop discipline.** Every `push` needs exactly one matching `pop` on every exit path,
  including error paths. Consider a small RAII guard, and assert the stack depth is back to 0 at
  the end of the run.
- **Model files.** `get_model` returns `(String, SmtModel)`; write the string, and use the parsed
  `SmtModel` for the summary line if it helps. Follow what
  `verify_fn.rs:512` does today.
- Keep the driver's decisions (which paths, which verdicts) in a plain data structure. Story 07
  serialises exactly that to `trace.json`; do not entangle it with the stdout printer.
- Do not attempt to reuse `EquivalenceSmtDriver`. It is built around rayon and per-claim solver
  processes, which is the opposite of what this needs.

## 8. State handed to the next story

Story 07 will rely on:

- A plain, serialisable run structure (name it, e.g. `DebugRun`) holding: theorem/proofstep/
  oracle/claim identity, both listings with their `sites` maps, the ordered left paths with their
  `Step`s, the nested right paths with their `Step`s and `Verdict`s, model file paths, per-node
  the SMT that was asserted, and the summary counts.
- The path id scheme (`#3`, `#3.1`) and the `Decision` rendering
  (`then` / `else` / `assert-holds` / `assert-fails` / `unwrap-some` / `unwrap-none`).
- The output directory layout.

Write down here anything about solver behaviour you discovered (query counts, where the time
goes, which cvc5 options helped) — story 07 and any future tuning starts from it.
