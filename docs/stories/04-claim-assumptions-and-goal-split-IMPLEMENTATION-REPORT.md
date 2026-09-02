# Story 04 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. Committed as one reviewable commit.

This is the "State handed to the next story" for **story 06** (and story 05, which produces the
per-path constraint that replaces the one this story makes skippable). Read it together with
`docs/stories/04-claim-assumptions-and-goal-split.md` (its §8 has the signature/const-name
tables; this file has the context, the verification evidence and the gotchas).

`cargo build --workspace` and `cargo test --workspace` both pass (102 lib tests, incl. 4 new
`story04_tests::*`; 4 pre-existing ignored). The `domino prove` transcript for
`kem-dem-cca-ssp` proofstep 0 / PKENC / same-output is **byte-identical** before and after the
refactor.

---

## 1. What landed

| File | Change |
|---|---|
| `src/writers/smt/contexts/equivalence/emit.rs` | The body of `emit_oracle_claim_assert` moved verbatim into a new `claim_assumptions_and_goal(&Claim, &str) -> (Vec<SmtExpr>, SmtExpr)` returning `(dependencies_code, postcond_call)`. `emit_oracle_claim_assert` is now a 2-line wrapper `SmtAssert(SmtNot(SmtImplies(SmtAnd(deps), goal)))`. New `emit_claim_assumptions` (one `(assert dep)` per assumption) and `emit_claim_goal_negated` (`(assert (not goal))`). `build_returns` gained `skip_return_constraint_for: Option<&str>` and now returns a flat `Vec<SmtExpr>`. `emit_constant_declarations` gained the same param and threads it to both `build_returns` calls. New `#[cfg(test)] mod story04_tests`. |
| `src/gamehops/equivalence/verify_fn.rs` | line 130: `emit_constant_declarations()` → `emit_constant_declarations(None)`. Only change; `prove` path otherwise untouched. |
| `testdata/story04/emit_oracle_claim_assert.smt2` | **new golden** (17 lines). |
| `testdata/story04/emit_constant_declarations_none.smt2` | **new golden** (268 lines). |

Nothing else was touched. No behaviour change for `domino prove`, `latex`, or `proofsteps`.

## 2. Public surface for story 06

All on `impl<'a> EquivalenceContext<'a>` in `src/writers/smt/contexts/equivalence/emit.rs`:

```rust
pub(crate) fn claim_assumptions_and_goal(&self, claim: &Claim, oracle_name: &str)
    -> (Vec<SmtExpr>, SmtExpr);
pub(crate) fn emit_claim_assumptions(&self, claim: &Claim, oracle_name: &str) -> Vec<SmtExpr>;
pub(crate) fn emit_claim_goal_negated(&self, claim: &Claim, oracle_name: &str) -> SmtExpr;
pub(crate) fn emit_constant_declarations(&self, skip_return_constraint_for: Option<&str>)
    -> Vec<SmtExpr>;
```

`emit_claim_assumptions` and `emit_claim_goal_negated` currently carry `#[allow(dead_code)]`
— **story 06 is their first non-test caller; delete the attribute when you wire them in.**

### The debugger's flow (story 06)

```
smt = emit_base_declarations
    + emit_theorem_paramfuncs
    + emit_game_definitions
    + emit_constant_declarations(Some(<oracle under debug>))   // <return-O> now UNCONSTRAINED
    + emit_randomness_mapping_condition(O) / emit_auto_randomness(O)
    + emit_invariant(O)                                         // after load_invariants
    ; for each assumption in emit_claim_assumptions(claim, O): assert it   (up front)
    ; ... symbolic execution: push/pop, per-path DSA, and at each left terminal
    ;     assert (= <return-{left_GI}-O>  <return/abort built from the symbolic state>)
    ;     (this is the constraint build_returns no longer emits)
    ; at a (left terminal, right terminal) pair:
    ;     push; assert emit_claim_goal_negated(claim, O); check-sat; (model); pop
```

`emit_claim_assumptions(..)` + `emit_claim_goal_negated(..)` is **equisatisfiable** with the
single `emit_oracle_claim_assert(..)` — verified by a test (§4).

### Constant names

See `docs/stories/04-claim-assumptions-and-goal-split.md` §8 for the full table. The one that
matters most: with `emit_constant_declarations(Some(O))`, `<return-{GI}-{O}>` is **declared
but unconstrained** on **both** sides; `return-value-{GI}-{PI}-{O}`,
`<return-is-abort-{GI}-{PI}-{O}>` and `<<game-state-{GI}-new-{O}>>` stay constrained *off*
`<return-{GI}-{O}>`, so as soon as story 05's terminal encoding constrains `<return-{GI}-{O}>`
the whole downstream chain (relations, invariants, `emit_oracle_claim_assert`) is well-defined
again.

## 3. Assumption list — order and content

`claim_assumptions_and_goal(claim, O).0` is, in order:

1. `<randomness-mapping>` — a bare constant reference. It is **declared and asserted-equal
   elsewhere** (`emit_randomness_mapping_condition` declares `(declare-const
   <randomness-mapping> Bool)` + `(assert (= <randomness-mapping> <big and>))`, or
   `emit_auto_randomness` `define-fun`s `randomness-mapping-{O}`). Story 06 must still emit
   those; this list only *references* the const.
2. `(invariant <<game-state-L-old>> <<game-state-R-old>>)`
3. `(package-invariant!{GI}-{pkg}!  <<game-state-{GI}-old>>)` — one per side per package whose
   `pkg.invariants` is non-empty (left packages first, then right). **kem-dem-cca-ssp has
   none**, so this is currently untested against a real project with package invariants.
4. `(game-invariant!{GI}!  <<game-state-{GI}-old>>)` — one per side with non-empty
   `game().invariants`. Also none in kem-dem-cca-ssp.
5. `claim.dependencies()` in order, each via `ClaimType::guess_from_name`:
   - `relation*` → `(dep  <<game-state-L-new-{O}>>  <<game-state-R-new-{O}>>)`
   - else (lemma) → `(<relation-{dep}-{L}-{R}-{O}>  <<game-state-L-old>>  <<game-state-R-old>>
     <return-L-O>  <return-R-O>  <arg…>)`

`ClaimType::guess_from_name` (`src/theorem.rs:221`) is prefix-based: `relation*`→Relation,
`invariant*`→Invariant, else Lemma. The `Invariant*` arms are `unreachable!` in dep dispatch
(a claim can't depend on an invariant). **Note the story text's example "a Relation like
`no-abort`" is loose** — `no-abort` does *not* start with `relation`, so it would dispatch as
a Lemma. The test uses `relation-no-abort` to genuinely hit the Relation arm.

## 4. Tests (`src/writers/smt/contexts/equivalence/emit.rs`, `mod story04_tests`)

Fixture: `example-projects/kem-dem/kem-dem-cca-ssp`, theorem `kem_dem_cca_ssp`, first
`GameHop::Equivalence` (proofstep 0), oracle `PKENC`. Loaded with the **real**
`EquivalenceTransform` (not `DebugTransform`) via `DirectoryProject::load`, then
`EquivalenceContext::new(eq, &theorem, &auxs)`. **No solver is invoked** — pure SMT-term
construction + `Display` — so kem-dem-cca-ssp is safe as a unit fixture (same rationale as
story 02). `4WHS` / `yao` are never touched.

`load_invariants` is **not** called: neither `claim_assumptions_and_goal` nor
`emit_constant_declarations` reads the loaded `.smt2` invariant bodies (only
`pkg.invariants` / `game().invariants` presence, which is parsed from the package/game files).

| test | checks |
|---|---|
| `emit_oracle_claim_assert_matches_golden` | `emit_oracle_claim_assert(mixed_claim, PKENC).to_string()` == `testdata/story04/emit_oracle_claim_assert.smt2` |
| `emit_constant_declarations_none_matches_golden` | `emit_constant_declarations(None)` rendered == `testdata/story04/emit_constant_declarations_none.smt2` |
| `assumptions_and_negated_goal_compose_to_claim_assert` | independently recombines `SmtAssert(SmtNot(SmtImplies(SmtAnd(deps), goal)))` from `claim_assumptions_and_goal` and asserts string-equality with `emit_oracle_claim_assert`; asserts `emit_claim_assumptions` is one `(assert dᵢ)` per assumption in order; asserts `emit_claim_goal_negated` == `(assert (not goal))` |
| `skip_return_constraint_drops_exactly_two_asserts` | `emit_constant_declarations(Some("PKENC"))` is `emit_constant_declarations(None)` with **exactly two** entries removed, order otherwise preserved (subsequence check — stronger than set-difference); both removed lines are `(assert (= <return-…-PKENC> (<oracle-…)))` and they differ (one left, one right) |

`mixed_claim()` = `Claim { name: "same-output", ty: Lemma, dependencies:
["relation-no-abort", "lemma-kem-correctness"], admitted: false }` — exercises Lemma goal +
Relation dep + Lemma dep.

### Golden-file bootstrap

`check_golden(name, actual)` reads `testdata/story04/<name>`; **if missing it writes the file
and panics** ("re-run the test"). So a fresh checkout with the committed goldens just
compares; a deleted golden self-heals on one re-run. The goldens were captured *after* the
refactor (the story wanted "before") — acceptable because the refactor is a provable
structural identity (extract + recombine with the identical `SmtAssert/SmtNot/SmtImplies/
SmtAnd` constructors; `build_returns` only loses the tuple wrapper, same push order) **and**
the byte-identical `prove` transcript (§5) is the real regression guard.

## 5. Verification evidence

- `cargo build --workspace` — clean, no warnings.
- `cargo test --workspace` — 102 lib + 2 bin, all pass.
- `cargo clippy --workspace` — no warnings/errors.
- **Transcript byte-diff**: on base commit `ee1c2c9a`, ran
  `domino prove --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
  --transcript`, saved `_build/code_eq/.../PKENC/same-output.smt2` (3593 lines). Re-ran on the
  story-04 build. `diff` → **identical**.
- `DOMINO=target/debug/domino ./scripts/test-known-examples.sh`: all `test-projects/*`,
  `simple-KEM-example`, `kem-dem-cca-ssp`, `hello-world`, `hello-world-oracle-rename` pass
  (prove + latex); `4WHS`/`yao` parse-only pass.
  **Pre-existing failures, NOT caused by this story** — the four
  `kem-dem-cca-blended-*` / `kem-dem-cpa-blended-*` projects fail on the base commit too, with
  an identical `cvc5` `(error "Parse Error: <stdin>:3193.81: Symbol …")`. Verified by building
  `ee1c2c9a` and running `domino prove` in `kem-dem-cca-blended-parallel` — same error. Looks
  like a cvc5-version / environment issue in this repo checkout, unrelated to SMT emission.
  If CI treats the script's exit code as pass/fail, this predates story 04.

## 6. Gotchas / notes for follow-up

- **`emit_claim_assumptions` / `emit_claim_goal_negated` each recompute
  `claim_assumptions_and_goal`.** Cheap (pure term building) and matches how
  `emit_oracle_claim_assert` works. If story 06 wants both halves it can call
  `claim_assumptions_and_goal` once directly (it's `pub(crate)`).
- **`build_returns` return type changed** `Vec<(SmtExpr, SmtExpr)>` → `Vec<SmtExpr>`. The only
  caller is `emit_constant_declarations`. If you were planning to reuse the pairs, they're
  gone — the declares and constrains are just interleaved now.
- The story's "package-invariant / game-invariant" assumption arms (list items 3–4 in §3) are
  **not exercised by any test** because kem-dem-cca-ssp has neither. `test-projects/` has some
  invariant projects (`test-invariant-initial-state`) but not an equivalence with package
  invariants + a claim with deps. Left as-is (byte-identical `prove` transcript covers the
  real corpus); flag if story 06 sees surprises there.
- `failed` (a `scripts/test-known-examples.sh` artifact) is not tracked and not committed.
