# Story 19 — Implementation report: all-claim runs and the strategy/listing split

**Status:** done, committed as `db1bbae4` ("Story 19: all-claim runs and the strategy/listing split").
**Branch:** `amir/easycrypt-export`
**Builds/tests:** full workspace suite green with `--features cvc5-lib` (607 lib tests); default
(non-cvc5) build compiles. After the code-review fixes only the `debug::` tests and the new CLI
tests were re-run.

This report was written after the fact from the implementing session's transcript and the
commit diff: the session crashed on low disk space mid-way, was compacted, and committed
without writing it.

---

## 1. Trace schemas

- Sequential `TRACE_SCHEMA` **8 → 9** (`src/debug/driver.rs`).
- Lockstep `LOCKSTEP_TRACE_SCHEMA` **9 → 10** (`src/debug/lockstep_run.rs`).

Both gain the strategy, `all_claims`, the claim list and per-claim verdicts; `Unreachable`
carries a reason.

## 2. CLI

`crates/domino/src/cli.rs`, `crates/domino/src/main.rs`.

- `domino debug` is Domino-listing only. `--easycrypt` is deleted; `--lockstep` picks the
  strategy (default sequential).
- `--proof` / `--proofstep` / `--oracle` / `--claim` are all optional. Omitting `--claim` is an
  all-claim run. `--proofstep` without `--proof` is rejected.
- New `--first-failure-per-claim`.
- `domino easycrypt --debug` joins the `ec_mode` group and runs lockstep on the EasyCrypt
  listing. It has no `--claim`. `--debug-timeout` (`requires = "debug"`) is in
  **milliseconds** — cvc5 `tlimit-per`, same unit as `domino debug --timeout`.
- `debug()` in `main.rs` is now a sweep: `sweep::plan`, then one run per target with a fresh
  observer. A single target keeps story 17's concise stdout report; a sweep prints one line per
  oracle, a failure table, and writes the index (§6).
- New errors: `OutNeedsOneOracle`, `DebugIo`, `EcDebugNeedCvc5Lib`, `EcDebugNotVerified`, `EcDebug`.

### Behaviour the spec does not state (decided during implementation)

- `--out` is rejected unless exactly one oracle is selected.
- An all-oracles `--claim X` silently skips oracles that have no claim `X`; it errors only if
  none has it.
- `--first-failure-per-claim` and the `--check-left/right…` flags conflict with `--lockstep`.
- An explicitly named non-equivalence proofstep is an error; a sweep skips them.
- Claim summaries carry an extra `skipped` counter.

## 3. Base frame and the per-pair check

`src/writers/smt/contexts/equivalence/emit.rs`: `claim_assumptions_and_goal` now delegates to
`claim_assumption_parts` → `(shared, own_deps, goal)`. New `emit_shared_assumptions(oracle)`
(built from a dummy dependency-free `invariant` claim) and `emit_claim_own_assumptions`.

`src/debug/driver.rs`:

- `shared_base_frame(eqctx, oracle)` holds only what every claim shares;
  `base_frame(eqctx, oracle, claim)` = shared frame + that claim's own dependencies.
- The frame is chosen by `[claim] if !all_claims => base_frame(..), _ => shared_base_frame(..)`.
  (See §8: the first version keyed on claim *count*.)
- `Checking` / `PairCheck` / `Counters` drive the terminal-pair checks; `write_model` writes
  models per claim.

### `src/debug/claims.rs` (new)

- `obligations(eqctx, eq, oracle)`: `equal-aborts`, `same-output`, `invariant`, the rest of the
  proof tree, then the generated invariant claims. Admitted claims are listed and never
  checked.
- `ClaimQuery { name, dependencies, negated }`, `PairAborts { left, right }`.
- `false_by_terminals`: `no-abort`, `left-no-abort`, `right-no-abort`, `equal-aborts` are read
  off the two terminals' abort constructors — **no solver call**.
- `check_claim`: syntactic shortcut; else push dependencies, push negated goal, `check-sat`.
  Only after the goal comes back `unsat`, a lazy extra check names a lemma dependency that is
  false on the pair.
- `aggregate`: one standing verdict for a pair — `GoalFails` before `Inconclusive` before
  `Verified`, else the first claim's `Unreachable` reason; a pair with nothing checked (all
  admitted/skipped) is `Verified`.

**Deviation:** the lazy check pops the dependency frame and re-pushes **each dependency
alone**, so it tests `dep_i ∧ path` rather than §4.3's single `deps ∧ path_l ∧ path_r`
query. A contradiction only visible in the conjunction falls back to naming the joined
dependency list. Verdicts are the same; only the named reason can be less precise.

## 4. `Unreachable` gains a reason

```rust
pub enum Unreachability {
    PairInfeasible,                          // the vacuity check was unsat
    DependencyFalse { dependency: String },  // e.g. "no-abort"
}
pub struct ClaimVerdict { claim, verdict, relations }  // relations: invariant sub-verdicts, lockstep only
pub struct ClaimSummary { claim, verified, unreachable_pair, unreachable_dependency, … }
pub struct QueryCounts  { exploration, claims }
```

`describe_unreachable` renders e.g. *"left aborts at L4, and this claim assumes no-abort"*.
Neither flavour counts as a failure. `render_tree` adds a `strategy` line, an
"admitted, not checked" line, and per-claim lines.

## 5. Lockstep on the Domino listing

- `LockstepTerms.claims: Vec<ClaimQuery>` replaces `equal_output_negated` / `invariant_negated`.
- `PairRecord { id, node, left, right, claims }` with `verdict_of`, `relations()`, `has_failure()`;
  `EQUAL_OUTPUT` survives only as the EasyCrypt grouping.
- `check_pair`: vacuity check, then `check_claim` per claim; invariant relations are computed
  only when `invariant` is neither verified nor unreachable.
- `ClaimSet { NoDependencies, Obligations { only } }`; `ListingKind::layout()` (EasyCrypt →
  `Plain`, Domino → `Strategy("lockstep")`).
- Entry points: `run_lockstep_command` (EasyCrypt, signature unchanged),
  `run_lockstep_domino(.., claim: Option<&str>, ..)`, and the shared `run_lockstep_on`.
- `LockstepDebugOptions::easycrypt(timeout_ms)` is shared by `--tactics` and `--debug`.
- `lockstep_run.rs` module doc rewritten; the wrong claim that `smt_construct_abort` drops the
  game state is fixed (§4.8).
- Viewer (`lockstep_viewer.rs/.html`): rollups over `claims: Vec<ClaimCounts>`; the JS is
  generalised (`claimsOf`, `relationsOf`, `reasonText`, `T.smt_dir`, `safeRel` allows `!`).
- `src/easycrypt/tactics/driver.rs` reads `verdict_of(EQUAL_OUTPUT)` / `verdict_of("invariant")`.

## 6. Output layout and sweep

`src/debug/layout.rs` (new): `Layout { Plain, Strategy(&'static str) }`,
`ALL_CLAIMS_DIR = "!all-claims!"`, `DOMINO_DEBUG_DIR = "_build/debug/domino"`.

```text
_build/debug/domino/<theorem>/<l>-<r>/<oracle>/<claim | !all-claims!>/
    inlined.txt                                  shared
    sequential_viewer.html  sequential_trace.json  sequential_summary.txt
    lockstep_viewer.html    lockstep_trace.json    lockstep_summary.txt
    sequential/{smt,models,transcript.smt2}   lockstep/{smt,models,transcript.smt2}

<out>/<theorem>/!debug!/<l>-<r>/<oracle>/       easycrypt --debug: plain names
```

- The two strategies coexist; neither wipes the other.
- **The default EasyCrypt lockstep dir moved** to `_build/easycrypt/<theorem>/!debug!/…`.
  `--tactics` now passes `Some(debug_dir(..))` where it passed `None`
  (`src/easycrypt/tactics/mod.rs::debug_dir`).

`src/debug/sweep.rs` (new): `plan(..) -> Plan { targets, skipped }`, `SweepEntry`
(`from_sequential`, `from_lockstep`, `one_line`), `failure_table`, `write_index` →
`_build/debug/domino/index.html` + `summary.txt`. **The index reflects only the last
invocation**, not every run on disk. Exit is non-zero on any `GoalFails` or `Inconclusive`.

`src/easycrypt/debug.rs` (new): `debug_theorem(..)` calls `run_lockstep_command` with
`debug_dir(..)`.

## 7. Acceptance evidence

- Single-claim runs match the pre-story baseline except for new fields; the `smt/` files differ
  only in their header text.
- All-claim runs verified manually on `hello-world`, `simple-KEM`, `kem-dem` `PKDEC`, and
  `testdata/story19/deps`. Both strategies agree with each other and with `prove`.
- `easycrypt --debug` runs and writes under `!debug!` (manual check only).

## 8. Code-review fixes

- **Base frame:** an all-claim run whose obligation set has exactly one claim used that claim's
  dependencies. It now keys on `all_claims`, not the claim count.
- **All-admitted pairs:** `aggregate` labelled a pair with nothing checked as `PairInfeasible`.
  It now returns `Verified`.
- **CLI tests** added (below).

The standards review's smells were left as they are. They are judgement calls: stringly-typed
dependency names, data clumps in `check_claim` and `write_model`, near-duplicate
sequential/lockstep arms in `main.rs::debug()`, and `SweepEntry::from_*` reaching into the run
types.

## 9. Tests added

- `src/debug/driver.rs::story19_tests` (10): obligation order; abort dependency with no solver
  call; lazy lemma dependency costs one query after an unsat goal; single-claim base frame;
  single vs all-claim agreement; exploration paid once regardless of claim count; admitted
  claims listed and not checked; `--first-failure-per-claim`; both strategies coexist in one
  dir; all-claim run agrees with `prove` claim by claim (silent `TheoremUI` +
  `EquivalenceSmtDriver`, because `Project::prove` installs a global logger).
- `src/debug/lockstep_run.rs` (4): Domino listing reports two claims; claim filter narrows the
  set and names the dir; lockstep and sequential agree on failing claims; EasyCrypt listing
  keeps its two dependency-free claims and plain names.
- `src/debug/claims.rs`, `src/debug/sweep.rs`: unit tests.
- `crates/domino/tests/debug_all_claims.rs` (4): `debug --easycrypt` rejected; `--proofstep`
  without `--proof` rejected; a sweep on `testdata/story19/deps` prints one line per oracle and
  exits non-zero; `easycrypt --debug --claim` rejected.
- `testdata/story19/deps/` (new project): oracles `Branch` (lemma dependency `positive`, claim
  `needs-positive`), `AbortDiff`, `AbortBoth`, `Admitted` (claim `skipped: admit []`).
- The stale test `goal_smt_is_empty_for_an_admitted_claim` pointed at a kem-dem claim that no
  longer exists and was already failing at baseline. It now uses `testdata/story19/deps`.

## 10. Open items / not verified

- **`--tactics` byte-identity (§3, §5) is unverified.** The old-vs-new `Eq_*.ec` / report
  comparison on kem-dem was lost in the crash, and no test guards it. The `--tactics` path did
  change (`verdict_of` with `.expect`, the new debug dir), so this is the most important check
  to run.
- No comparison of `--claim` verdicts and query counts against a pre-story baseline (§5).
- No end-to-end test of `easycrypt --debug`: `--proofstep`/`--oracle` narrowing, the `!debug!`
  layout, the non-zero exit. The exit path in `main.rs` was checked manually only.
- No end-to-end assertion that an aborting pair's `DependencyFalse { "no-abort" }` keeps the
  query count flat; only `false_by_terminals` is unit-tested.
- Pre-existing from story 18: `kem_dem_cca_blended_parallel` proofstep 4 fails during solver setup
  with `get-rand-ctr-H3` not declared.

## 11. Why the diff is large (~3 900 + / 670 −)

Five constraints meet in the two debuggers:

1. **Per-claim verdicts.** A fixed `equal_output`/`invariant` pair became a variable claim list,
   which touches the driver, both reports, both viewers and the `--tactics` consumer.
2. **Two listings.** `--tactics` and `easycrypt --debug` share frozen behaviour, so the
   EasyCrypt listing's output had to stay the same.
3. **Two strategies in one directory.** Every artifact name and both trace schemas carry the
   strategy, which is why `Layout` exists.
4. **Flat solver cost.** Dependencies are split into syntactic ones, lazy lemma checks and a
   shared base frame, so claims don't multiply the exploration queries.
5. **Sweeps.** Planning, an index and a failure table on top of all of the above.
