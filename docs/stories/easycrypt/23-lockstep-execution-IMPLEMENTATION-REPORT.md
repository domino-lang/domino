# Story 23 — implementation report

## What changed

- `src/debug/exec.rs`: the statement walk is split so a side can be driven step by step. `walk`
  now runs on `Executor::advance` (consume everything up to the next decision point and return a
  `Head`), `take_sample`, `apply_unwrap` and `open_if_child`. The sequential debugger is
  byte-identical: `trace.json`, `index.html`, `inlined.txt` and `smt/` of `domino debug … --claim
  same-output` on kem-dem `PKENC` were diffed against the pre-change binary, and every `exec` and
  `driver` test passes unchanged. `SideExec` / `SidePos` are the `pub(crate)` face the engine uses.
- `src/debug/lockstep.rs` (new): the engine, listing-agnostic, plus the joint-tree data types.
- `src/debug/lockstep_run.rs` (new): `run_lockstep_command`, the trace header (`LockstepMeta`), the
  summary counts, the solver vocabulary built from `EquivalenceContext`.
- `src/debug/lockstep_report.rs` (new): `trace.json` (schema 9), `summary.txt`, stdout report,
  placeholder `index.html`, `smt/` files.
- `src/debug/progress.rs`: four new `DebugEvent`s (`JointNode`, `JointPairChecked`,
  `StuckPointFound`, `LockstepFinished`), with plain and bar rendering.
- `src/writers/smt/contexts/equivalence/emit.rs`: `randomness_mapping_candidates` is `pub(crate)`
  and carries the sample indices; new `randomness_mapping_premise` and `state_relation_names`.
- `crates/domino`: `debug --easycrypt`. `--claim`, `--no-check-left`, `--no-check-right` conflict
  with it (clap error naming both flags); without `--easycrypt` `--claim` stays required.
- `testdata/lockstep/rules/`: a small project (`GL ~ GR`, 14 oracles) with one oracle per rule of
  §3.3, used by the engine tests on the **Domino** listing.

## Deviations

- **Unit tests use a fixture project, not hand-built `InlinedOracle`s.** An executor needs a game
  instance and `SampleInfo` for the sample ids, state places and argument names, so hand-built IR
  would still have needed one. `run_lockstep_on(ListingKind::Domino, …)` runs the engine on
  `inline_oracle` of the fixture's `DebugTransform` game instances. `ListingKind::Domino` is not on
  the command line (that is the follow-up for `amir/symbolic-execution-debugger`).
- **Extra node kind `unreachable`**: the "both queries unsat, prune it" outcome of rule 1 needs a
  place in the tree when it is the root or was not checked by its parent (determined and
  synchronized children are not).
- The solver-answer records name the query (`left-then-possible`, `branches-differ`,
  `draws-differ`, `left-pairing-0-valid`, …), not the SMT.

## The engine (what stories 24 and 27 consume)

```rust
// src/debug/lockstep.rs
pub fn run_lockstep<S: SmtSolver>(
    solver: &mut S,                 // base frame (assumptions A) already at level 0
    left: LockstepSide, right: LockstepSide,   // InlinedOracle + Domino GameInstance + SampleInfo
    terms: &LockstepTerms,          // negated goals, relations, randomness-mapping pairings
    opts: &LockstepOptions,         // max_paths, stop flag, out_dir for models
    observer: &mut dyn LockstepObserver,
) -> Result<LockstepOutcome, DebugError>;
```

`LockstepObserver` (all methods default to no-ops) is called in depth-first order with the solver
stack at the reported node's state and `&LockstepOutcome` as found so far:
`node_entered(node)`, then `stuck_found` / `pair_checked` for what was found at it, then for each
explored child `child_entered(node, child_position)` followed by that child's whole subtree, then
`node_left(node)`. Story 27 walks this; it does not get the solver.

`LockstepOutcome { tree: JointTree, pairs: Vec<PairRecord>, stuck: Vec<StuckPoint>, stop_reason }`.
The tree is an arena, `tree.nodes`, in depth-first pre-order; node 0 is the root.

- `JointNode { index, kind, left: SideView, right: SideView, answers, children, pair, stuck }`.
  `kind` is `determined`, `synchronized`, `split`, `sampling-synchronized`, `sampling-independent`,
  `stuck`, `terminal-pair` or `unreachable`.
- `SideView { head: {kind: branch|unwrap|sample|return|abort, label}, consumed: [[a,b]…],
  plumbing: done-guard|call-result|null }`. `consumed` are the listing lines the side passed
  through since the last decision it took (viewer only, ADR 0002); a waiting side reports none.
- `JointChild { left: SideStep|null, right: SideStep|null, outcome }`, `SideStep { label,
  decision }` with decision `then|else|assert-holds|assert-fails|unwrap-some|unwrap-none|draw`.
  A side that did not move is `null` (this is how a determined or one-sided child reads).
  `outcome` is `explored {node}`, `pruned {answer}` (the solver proved the combination infeasible)
  or `not-explored` (the run stopped first).
- `PairRecord { id: "J<n>", node, left/right: PairSide { steps, terminal, lines, effect },
  equal_output, invariant, relations }`; verdicts are the existing `Verdict`
  (`verified|unreachable|goal-fails{model}|inconclusive{model}`). `relations` is filled only when
  `invariant` is neither verified nor unreachable.
- `StuckPoint { id: "S<n>", node, side, label, left_label, right_label, sample, draw, reason }`,
  `reason` in `partner-not-at-head`, `pairing-sat-not-valid`, `pairing-unknown`,
  `no-partner-reachable`.

### `trace.json`, schema 9

`schema: 9`, `mode: "lockstep"`, `listing: "easycrypt"`, then the identity, `options`,
`base_frame_smt`, `goals` (`equal_output_smt`, `invariant_smt`, `relations[{name, smt}]`), both
listings and `*_sites`, `left_syntactic` / `right_syntactic`, then `tree`, `pairs`, `stuck`,
`summary` and `stop_reason` (same shape as schema 8). The absolute output directory and the wall
clock are not serialised, so two runs of an unchanged project are byte-identical (tested).
Sequential runs still write schema 8. Partial `trace.json`/`summary.txt` are flushed every 8
joint paths and at the end; `Ctrl-C` stops at the next node and leaves a partial run
(`stop_reason.kind == "interrupted"`). `--max-paths` counts joint paths. `index.html` is the
one-line placeholder.

### Ids

`J<n>` and `S<n>` count from 1 in depth-first order: children in the order then before else, left
before right (a four-way split is (then,then), (then,else), (else,then), (else,else)). A stuck
point is numbered when its node is decided, a joint path when its terminal pair is. Nothing else
feeds them, so an unchanged project gives the same ids.

## How each rule was built

- **Determined**: two queries per branching side, `A ∧ pc ∧ c` and `A ∧ pc ∧ ¬c`; only `unsat`
  counts. `DoneGuard`s (condition `true`) always land here, and so does every `CallResult` guard on
  the three acceptance cases: the callee's `Abort` is a global terminal in the IR, so the `None`
  side is infeasible. Both tested (`every_plumbing_branch_is_a_determined_node`).
- **Synchronized** asks for `A ∧ pc ∧ ¬(c_L = c_R)` (not an `xor`); **split** prunes a combination
  by asking `A ∧ pc ∧ <its two path conditions>`.
- **Samplings**: a side's head sampling is independent iff `or` of the mapping premises of every
  candidate pairing (same sample index, same draw counter) is `unsat`; the candidates are
  `randomness_mapping_candidates`, the premise is `(randomness-mapping-<O> …)`. The mapping's text
  is never read. Reasons, in this priority: some premise `unknown` → `pairing-unknown`; some
  premise valid (its negation `unsat`) and the other side already ended → `no-partner-reachable`,
  otherwise `partner-not-at-head`; premises only satisfiable → `pairing-sat-not-valid`. When both
  sides are stuck, left goes first and the right one is classified again after it.

## How equal-output was built

`same-output`'s formula does mean something when a side aborts: it compares the two
`ReturnValueOrAbort` values, an aborting side's is the `abort` constructor, so a pair where exactly
one side aborts fails it and a pair where both abort passes. So the goal is the conjunction of the
`equal-aborts` and `same-output` goals, built from `claim_assumptions_and_goal` on a claim with no
dependencies (`equal_output_negated = (assert (not (and equal-aborts same-output)))`). Tests:
`equal_output_fails_when_exactly_one_side_aborts`, `equal_output_holds_when_both_sides_abort`.

## The relation list's source

`EquivalenceContext::state_relation_names()`: the names of the `define-state-relation` statements
of the equivalence's invariant files, in file order — the same statements
`writers::easycrypt::invariant` turns into the `Domino_<name>` operators its `inv` conjoins. Each
relation's goal is `(<name> <new left state> <new right state>)`, negated.

## Invariant vs abort (open difference, `prove` untouched)

Domino's abort return carries the state the side had reached (`OracleContext::smt_construct_abort`
keeps the game state), so on a pair where a side aborts the `invariant` claim compares the states
at the abort, including writes made before it. EasyCrypt's `inv` is
`params_inv ∧ (l.abort_flag = r.abort_flag) ∧ (!l.abort_flag ⇒ relations)`: after an abort it asks
nothing of the states. So Domino's invariant verdict is stricter at abort pairs, and `prove` only
gets around it with the `no-abort` dependency this mode does not assume. The engine reports
Domino's answer as the story asks; the abort flags of a pair are in `PairRecord.{left,right}
.terminal.is_abort` and the failing-paths list of the stdout report marks them
(`[left aborts]`). Pinned by `the_invariant_is_checked_on_the_state_at_the_abort` (the `AbortState`
oracle). None of the three acceptance cases hits it (their aborts are equal and state-neutral).
Story 27 should not admit a relation obligation at a pair where a side aborts merely because this
verdict fails.

## Numbers (debug build, `--progress none`)

| case | joint paths | nodes | stuck | pruned children | time | sequential EC-IR left x right |
|---|---|---|---|---|---|---|
| kem-dem `PKENC` | 4 | 43 | 0 | 0 | 0.9 s | 12 x 32 = 384 |
| kem-dem `PKDEC` | 5 | 25 | 0 | 0 | 0.8 s | 7 x 18 = 126 |
| hello-world `UsefulOracle` | 1 | 3 | 0 | 0 | 0.05 s | 2 x 1 = 2 |
| simple-KEM `GetPK` / `Run` / `TestSender` / `TestReceiver` | 2 / 2 / 5 / 5 | 6 / 14 / 10 / 10 | 0 | 0 | 0.2 s each | |

Every joint path verifies both claims. The undetermined branch queries of kem-dem answer `unknown`
rather than `sat` (the invariant on the old states has quantifiers); they count as "possible", as
the story's safety property says.

## Consistency with the sequential debugger (one direction, §4)

`lockstep_agrees_with_sequential_execution_on_the_acceptance_cases` (EasyCrypt listing against the
sequential Domino listing, all three cases) and `…_on_the_rule_oracles` (Domino against Domino, 12
oracles): no violation. On the acceptance cases every joint path verifies equal-output, and
sequential `equal-aborts` / `same-output` report no `GoalFails`; their `invariant` claim depends on
`no-abort`, so the second implication is vacuous there. The rule oracles' claims have no
dependencies, so it is exercised for real (`BadState`, `AbortState`: sequential invariant fails,
lockstep reports a failure).

## Verification

- `cargo build/clippy --workspace --all-targets`: clean, with and without `--features cvc5-lib`
  (cvc5 built; `source ~/.cache/domino/cvc5-lib-env.sh`).
- `cargo test --workspace`: 422 lib tests pass, 5 ignored.
  `cargo test --workspace --features cvc5-lib`: 476 pass, 6 ignored (before the review fixes), and **one failure that predates
  this story**: `debug::driver::tests::goal_smt_is_empty_for_an_admitted_claim` asks kem-dem for a
  claim `lemma-kem-correctness` that its `Proof.ssp` no longer declares.
- 32 new tests in `lockstep_run::tests`, all behind `cvc5-lib` because they run the solver; the
  default build's test count is unchanged.

## Notes for follow-up

- The engine asks the solver at every decision; kem-dem sizes are small (under a second in a
  debug build). Nothing was run on 4WHS or yao (the hard rule).
- A `--smt` file for a joint path holds the base frame, both sides' whole paths (declarations,
  constraints, return constraint), the vacuity `check-sat` and one block per check that failed
  (`all` and `deltas` write every check). `cvc5 --lang smt2 smt/J3.smt2` reproduces the verdicts
  (tested).
- `pairing-unknown` is not covered by a test: there is no cheap way to make cvc5 answer `unknown`
  on a pairing premise deterministically.

## Code review

Two parallel reviews (standards, spec). Fixed: the duplicated verdict helpers are now
`Verdict::slug` / `Verdict::is_failure` in `driver.rs`, used by `smtout.rs` and the lockstep files.
Left as they are, on purpose: `NodeKind::Synchronized` keeps the story's kind names in
`trace.json`; the `Unwrap` path of the engine (a branch on `inner = none`, story §6) has no test,
because the EasyCrypt IR never produces one and the fixture Domino listing has none in the rule
oracles; the candidate pairings a sampling is classified against are all of the mapping's
`(sample, offset)` candidates whose offsets equal the head draw's counter, which is every
candidate the mapping enumerates for that draw.
