# Story 04 — Split claim assumptions from the goal; make the return constraint skippable

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** nothing. Can be done in parallel with stories 01 and 02.
**Blocks:** story 06.

---

## 1. Why this story exists

This is a **pure refactor of the SMT emission layer** that makes room for the debugger, with
**zero behaviour change for `domino prove`**. It is the only story in the epic that touches code
`prove` executes, so it is the only one that must run `scripts/test-known-examples.sh`.

Two things need to change.

### 1a. Assumptions must be separable from the goal

`prove` emits the whole claim as a single refutation:

```smt2
(assert (not (=> (and <randomness-mapping>
                      (invariant <old-left> <old-right>)
                      (package-invariant!...! <old-left>) ...
                      (game-invariant!...! <old-left>) ...
                      <dependency calls>)
                 <goal>)))
```

One `check-sat` on that is all `prove` needs. The debugger cannot work that way: it must assert
the assumptions **positively and up front**, so that they constrain branch-reachability queries
while it walks the execution tree, and only add the negated goal at a terminal pair. (Design
decision from the interview: *all* assumptions, including the claim's dependencies, are asserted
before the left oracle is executed. A dependency like `no-abort` will then make left abort paths
`unsat` — that is intended and visible.)

### 1b. The monolithic return constraint must be suppressible

`build_returns` (`src/writers/smt/contexts/equivalence/emit.rs:1318`) emits, for every exported
oracle of a game instance, four declare/constrain pairs:

| declared | constrained to |
|---|---|
| `<return-…>` | `(= <return-…> (<oracle-fn> <old-state> <consts> <args…>))` |
| `<return-value-…>` | `(= <return-value-…> (<accessor> <return-…>))` |
| `<is-abort-…>` | `(= <is-abort-…> (= <return-value-…> <abort-ctor>))` |
| `<new-state-…>` | `(= <new-state-…> (<state-accessor> <return-…>))` |

The debugger replaces the **first** one with its own per-path DSA encoding
(`(= <return-…> <return/abort constructed from the symbolic state>)`) and keeps the other three,
so `emit_oracle_claim_assert`, the invariants and the relations all keep working untouched.
So `build_returns` needs a way to skip exactly that one assert, for exactly the oracle under
debug, on both sides.

## 2. What exists today — read this carefully

All of it in `src/writers/smt/contexts/equivalence/emit.rs`.

### `emit_oracle_claim_assert` (line 220)

```rust
pub(crate) fn emit_oracle_claim_assert(&self, claim: &Claim, oracle_name: &str) -> SmtExpr
```

Body, abridged:

1. Builds contexts and patterns for both sides (`gctx_left/right`, `octx_left/right`,
   `state_left/right`, `left_return`/`right_return` `ReturnConst` patterns, `args`).
2. Defines six closures:
   - `build_lemma_call(name)` — calls the relation `name` with
     `(old_left, old_right, <return-left>, <return-right>, args…)`.
   - `build_relation_call(name)` — `(name <new-state-left> <new-state-right>)`.
   - `build_invariant_old_call(name)` — `(name <old-left> <old-right>)`.
   - `build_left_invariant_old_call` / `build_right_invariant_old_call` — single-sided, old state.
   - `build_invariant_new_call` / `build_left_invariant_new_call` /
     `build_right_invariant_new_call` — the same on the new state.
3. `dep_calls` = each `claim.dependencies()` dispatched by `ClaimType::guess_from_name`
   (`Lemma` → lemma call, `Relation` → relation call; the invariant variants are `unreachable!`).
4. `postcond_call` = the claim itself, dispatched on `claim.ty`.
5. `dependencies_code` = `[<randomness-mapping-const>, invariant(old)]`, then one
   `package-invariant!<inst>-<pkg>!(old)` per package with invariants on each side, then one
   `game-invariant!<inst>!(old)` per side that has game invariants, then `dep_calls`.
6. Returns `SmtAssert(SmtNot(SmtImplies(SmtAnd(dependencies_code), postcond_call)))`.

### `build_returns` (line 1318) and `emit_constant_declarations` (line 782)

`emit_constant_declarations` declares old game states, game/theorem consts, oracle arguments,
then:

```rust
for (decl_ret, constrain) in build_returns(left)  { out.push(decl_ret); out.push(constrain); }
for (decl_ret, constrain) in build_returns(right) { out.push(decl_ret); out.push(constrain); }
for (decl_ctr, assert_ctr, assert_zero_ctr) in build_rands(self.sample_info_left(), left) { ... }
```

`build_returns(game_inst) -> Vec<(SmtExpr, SmtExpr)>` loops over `game_inst.game().exports` and
pushes the four pairs listed above, in this order: `return_const`, `return_value_const`,
`is_abort_const_pattern`, `state.declare_new(...)`.

### Callers of these

- `src/gamehops/equivalence/verify_fn.rs:130` — `emit_constant_declarations()` in
  `verify_equivalence`.
- `src/gamehops/equivalence/verify_fn.rs:433` — `emit_oracle_claim_assert(claim, oracle_name)` in
  `verify_oracle_claim`.

Nothing else. (`emit_game_or_package_invariant_start_assert` and `emit_invariant_start_assert` are
the invariant-start path and are **out of scope** for this story and the epic.)

## 3. Work to do

### 3.1 Extract the shared builder

```rust
/// The claim's assumptions (each an SMT *term*, not an assert) and its goal term.
/// `emit_oracle_claim_assert` combines them; the debugger asserts them separately.
fn claim_assumptions_and_goal(
    &self,
    claim: &Claim,
    oracle_name: &str,
) -> (Vec<SmtExpr>, SmtExpr);
```

Move the entire current body of `emit_oracle_claim_assert` into it, returning
`(dependencies_code, postcond_call)`.

### 3.2 Re-express `emit_oracle_claim_assert` — byte-identical output

```rust
pub(crate) fn emit_oracle_claim_assert(&self, claim: &Claim, oracle_name: &str) -> SmtExpr {
    let (deps, goal) = self.claim_assumptions_and_goal(claim, oracle_name);
    SmtAssert(SmtNot(SmtImplies(SmtAnd(deps), goal))).into()
}
```

This must produce **exactly** the same `SmtExpr` as before — same order, same nesting. Prove it
with a test (see acceptance criteria).

### 3.3 Add the two debugger-facing emitters

```rust
/// One `(assert <dep>)` per assumption, in the same order `claim_assumptions_and_goal`
/// returns them.
pub(crate) fn emit_claim_assumptions(&self, claim: &Claim, oracle_name: &str) -> Vec<SmtExpr>;

/// `(assert (not <goal>))` — the refutation the debugger checks at a terminal pair.
pub(crate) fn emit_claim_goal_negated(&self, claim: &Claim, oracle_name: &str) -> SmtExpr;
```

Both are thin wrappers over `claim_assumptions_and_goal`. Note the logical relationship, and
write it in a doc comment: `assert(d1) … assert(dn) + assert(not goal)` is equisatisfiable with
the single `assert(not (=> (and d1..dn) goal))` that `prove` uses, but it lets the assumptions
constrain intermediate queries.

### 3.4 Make the return constraint skippable

```rust
fn build_returns(
    game_inst: &GameInstance,
    skip_return_constraint_for: Option<&str>,   // exported oracle name
) -> Vec<(SmtExpr, SmtExpr)>
```

When `export.name() == skip`, push the `return_const` **declaration** with no constraint, and
keep the other three pairs exactly as they are. Since the return type is
`Vec<(SmtExpr, SmtExpr)>`, either change it to `Vec<(SmtExpr, Option<SmtExpr>)>` or push a
`Vec<SmtExpr>` of interleaved statements — pick whichever reads better and adjust
`emit_constant_declarations` accordingly.

Thread the parameter through:

```rust
pub(crate) fn emit_constant_declarations(&self, skip_return_constraint_for: Option<&str>)
    -> Vec<SmtExpr>
```

`src/gamehops/equivalence/verify_fn.rs:130` passes `None`.

## 4. Acceptance criteria

- [ ] `emit_oracle_claim_assert` output is **unchanged**. Add a unit test that constructs a
      `Claim` with a mix of dependency kinds (a `Relation` like `no-abort`, a `Lemma` like
      `lemma-kem-correctness`) and asserts the rendered `SmtExpr` string equals a golden value
      captured *before* the refactor. Capture the golden value first, then refactor.
- [ ] `emit_claim_assumptions` returns one `(assert …)` per element of the assumption list, in
      the same order, and `emit_claim_goal_negated` returns `(assert (not <goal>))` for the same
      goal term.
- [ ] `emit_constant_declarations(None)` output is **unchanged** (golden test).
- [ ] `emit_constant_declarations(Some(o))` differs from `emit_constant_declarations(None)` by
      exactly two asserts — the `constrain_return` for `o` on the left and on the right — and by
      nothing else. Assert that programmatically (set difference), not by eyeballing.
- [ ] `cargo build --workspace && cargo test --workspace` pass.
- [ ] `scripts/test-known-examples.sh` passes. **This is the one story that must run it.**

## 5. How to verify

```bash
cargo build --workspace
cargo test  --workspace

# the one story that needs the full example sweep — it already skips 4WHS and yao
DOMINO=target/debug/domino ./scripts/test-known-examples.sh

# targeted cross-check that a real proof still proves, and that the transcript is identical
cd example-projects/kem-dem/kem-dem-cca-ssp
cargo run --bin domino -- prove --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output --transcript
# transcript lands in _build/code_eq/<theorem>/<left>-<right>/<oracle>/<claim>.smt2
# diff it against a copy taken before the refactor — it must be byte-identical
```

`kem-dem-cca-ssp` proofstep 0 is `equivalence Game_MON_CCA_PKE Game_MOD_CCA_PKE_Real_KEM`
(`theorem/Proof.ssp:237`), oracles `PKGEN`/`PKENC`/`PKDEC`, claims `invariant`, `same-output`,
`equal-aborts` and the admitted `lemma-kem-correctness`. It exercises lemma dependencies,
relation dependencies and package invariants — everything this refactor touches.

> **Never** run `prove` or `scripts/test-known-examples.sh` variants against
> `example-projects/4WHS` or `example-projects/yao`. The script itself already restricts those two
> to `domino proofsteps`; do not bypass it. See `docs/stories/00-overview.md` §7.

## 6. Notes / risks

- The golden-value tests are the whole point of this story. **Capture the goldens before you
  start refactoring** — `git stash` a scratch test that prints the current output, or write the
  test first against current `main` behaviour.
- Do not "improve" the assumption list while you are in there (e.g. deduplicating, reordering,
  or lifting `<randomness-mapping>` out). Any change alters `prove`'s transcript and invalidates
  the whole point of the story.
- `ClaimType::guess_from_name` (`src/theorem.rs:220`) is string-prefix based: `relation*` →
  `Relation`, `invariant*` → `Invariant`, else `Lemma`. Keep using it; do not switch dependencies
  to `claim.ty`.

## 7. State handed to the next story

Story 06 will rely on:

- `EquivalenceContext::emit_claim_assumptions(&Claim, &str) -> Vec<SmtExpr>`
- `EquivalenceContext::emit_claim_goal_negated(&Claim, &str) -> SmtExpr`
- `EquivalenceContext::emit_constant_declarations(Option<&str>) -> Vec<SmtExpr>` — the debugger
  passes `Some(<oracle under debug>)`.
- The guarantee that with `Some(o)`, `<return-o>` is **declared but unconstrained**, while
  `<return-value-o>`, `<is-abort-o>` and `<new-state-o>` remain constrained off `<return-o>`.
  Story 05's terminal encoding supplies the missing constraint.

Record here the exact names of the constants involved (`<return-…>` etc. as produced by
`patterns::ReturnConst::name()`), since story 05 and 06 have to reference them.

## 8. Implementation notes (filled in by the story-04 session)

**Status: done.** Branch `amir/symbolic-execution-debugger`. See
`docs/stories/04-claim-assumptions-and-goal-split-IMPLEMENTATION-REPORT.md` for the full handover.

### Final signatures

```rust
// src/writers/smt/contexts/equivalence/emit.rs — impl EquivalenceContext<'a>
pub(crate) fn claim_assumptions_and_goal(&self, claim: &Claim, oracle_name: &str)
    -> (Vec<SmtExpr>, SmtExpr);                       // (assumption terms, goal term)
pub(crate) fn emit_oracle_claim_assert(&self, claim: &Claim, oracle_name: &str) -> SmtExpr;
pub(crate) fn emit_claim_assumptions(&self, claim: &Claim, oracle_name: &str) -> Vec<SmtExpr>;
pub(crate) fn emit_claim_goal_negated(&self, claim: &Claim, oracle_name: &str) -> SmtExpr;
pub(crate) fn emit_constant_declarations(&self, skip_return_constraint_for: Option<&str>)
    -> Vec<SmtExpr>;

// free fn in the same file
fn build_returns(game_inst: &GameInstance, skip_return_constraint_for: Option<&str>) -> Vec<SmtExpr>;
```

`build_returns` now returns a **flat** `Vec<SmtExpr>` of interleaved
declare/constrain statements (not `Vec<(SmtExpr, SmtExpr)>`), so the skipped constraint is
simply not pushed. `emit_constant_declarations` `out.extend(build_returns(...))`.

### Exact constant names (per exported oracle `O`, game instance `GI`, exporting package instance `PI`)

| constant | render | with `skip_return_constraint_for == Some(O)` |
|---|---|---|
| return         | `<return-{GI}-{O}>`                    | **declared, NOT constrained** (debugger supplies `(assert (= <return-{GI}-{O}> …))`) |
| return value   | `return-value-{GI}-{PI}-{O}`           | declared + `(= … (…-return-value-or-abort <return-{GI}-{O}>))` — unchanged |
| is-abort       | `<return-is-abort-{GI}-{PI}-{O}>`      | declared + `(= … (match return-value-{GI}-{PI}-{O} …))` — unchanged |
| new game state | `<<game-state-{GI}-new-{O}>>`          | declared + `(= … (…-game-state <return-{GI}-{O}>))` — unchanged |

`{GI}` is `equivalence.left_name()` / `right_name()`; for kem-dem-cca-ssp proofstep 0 those
are `Game_MON_CCA_PKE` and `Game_MOD_CCA_PKE_Real_KEM`. Old game state (input to the oracle
fn) is `<<game-state-{GI}-old>>`; oracle args are `<arg-{GI}-{O}-{argname}>`.

### Assumption list order (what `claim_assumptions_and_goal` returns as `.0`)

1. `<randomness-mapping>` (bare const ref; defined/asserted elsewhere by
   `emit_randomness_mapping_condition` / `emit_auto_randomness`)
2. `(invariant <<game-state-L-old>> <<game-state-R-old>>)`
3. one `(package-invariant!{GI}-{pkg}!  <<game-state-{GI}-old>>)` per side **per package that
   has a non-empty `invariants`** (none in kem-dem-cca-ssp), left side first then right
4. one `(game-invariant!{GI}!  <<game-state-{GI}-old>>)` per side that has game invariants
5. the claim's `dependencies()`, in declared order, each dispatched by
   `ClaimType::guess_from_name`: `relation*` → `(dep <<game-state-L-new-{O}>> <<game-state-R-new-{O}>>)`,
   anything else → lemma-style `(<relation-{dep}-{L}-{R}-{O}> <old-L> <old-R> <return-L> <return-R> <args…>)`.

The goal term (`.1`) is the claim itself dispatched on `claim.ty` (same builders).
