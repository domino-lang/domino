# Claim dependencies move to the terminal pair, and strategy is split from listing

**Status:** accepted. Implemented by
`docs/stories/symbolic-execution/19-all-claim-runs-and-strategy-split.md`.
Supersedes two rows of `docs/stories/symbolic-execution/00-overview.md` §3 that were previously
marked "do not relitigate".

The debugger originally required `--claim` and asserted that claim's dependencies in the **base
frame**, before any exploration. That was the right call while the tool answered one question at a
time: a dependency like `no-abort` prunes every aborting left path at the fork, which is a large
saving. But it makes the exploration *claim-specific*, so the expensive part of a run — inlining
both oracles, enumerating left paths, asking the solver which right branches are reachable — cannot
be shared. Three claims meant three identical explorations, and pointing the debugger at a project
you had not already diagnosed was impossible.

We therefore **split the assumption set by scope**. Everything every claim of an oracle shares —
the invariants on the old states, the randomness-mapping condition, `emit_auto_randomness` — stays
in the base frame. Each claim's own declared dependencies move to the **terminal pair**, asserted
one `push` above the pair's path conditions, so a single exploration serves the oracle's whole
obligation set at one `check-sat` per claim per pair. A run with `--claim` keeps the old frame and
the old pruning; only an **all-claim run** pays the wider exploration.

This is verdict-preserving, which is the property that makes it safe. Paths are exhaustive and
disjoint, and moving a dependency from the base frame into the terminal conjunction does not change
what the solver sees there. Pruning only decides which pairs get enumerated, and a pruned pair is
`unsat` at the goal check anyway. Agreement with `domino prove`, per claim, is an acceptance
criterion of the story rather than an aspiration.

We also separated two axes that one flag had been carrying. **Strategy** (sequential exploration vs
lockstep execution) and **listing** (Domino code vs EasyCrypt code) are independent, and
`domino debug --easycrypt` meant one particular corner of the grid. `domino debug` is now
Domino-listing only, with `--lockstep` selecting the strategy; the EasyCrypt listing is reached
only through `domino easycrypt --debug`, which `--tactics` uses internally.

## Considered options

- **Keep a per-claim base frame and share only the branch decisions**, re-checking each claim
  against a cached exploration tree. Rejected: the tree is only valid under the assumptions that
  produced it, so either the cache is per-claim again or the sharing is unsound.
- **Drop dependencies entirely in an all-claim run** — check `same-output`, `equal-aborts` and
  `invariant` assuming nothing but the old-state invariants, as lockstep-on-EasyCrypt does.
  Rejected: `no-abort` is not a project lemma, it is the inductive crutch `verify_induction_step`
  legitimately grants once `equal-aborts` is discharged, and `smt_construct_abort` carries the
  state reached at the abort. Dropping it makes `invariant` demand a relation hold at the abort
  point, which the SSP proof never asks for — the debugger would report failures on projects that
  are correct, and its verdicts would no longer be comparable to `prove`'s.
- **A fifth verdict for "the claim's premise is false on this pair"**, distinct from
  `Unreachable`. Rejected: `Unreachable` already means *infeasible under the assumptions in force*,
  and those assumptions have always included the claim's dependencies. Moving them does not create
  a concept, it gives the existing one a scope. `Unreachable` carries a *reason* instead.
- **Sequential exploration on the EasyCrypt listing**, filling the fourth cell of the
  strategy × listing grid. Rejected as unwanted: claims have no meaning on the EasyCrypt listing,
  which has neither `no-abort` nor project lemmas, so the cell would duplicate lockstep-on-EasyCrypt
  with a worse search order.

## Consequences

- An all-claim run explores strictly more paths than a narrowed one, because abort paths are no
  longer pruned at the fork. They surface as `Unreachable { DependencyFalse }` at the terminal pair.
  Verdicts are unchanged; only the path count grows. `--claim` remains the escape hatch.
- Deciding `DependencyFalse` is free for the dependencies that matter. `no-abort`,
  `left-no-abort`, `right-no-abort` and `equal-aborts` are functions of the two return values'
  abort constructors, and the driver knows both terminals syntactically — so the default proof
  trees and every generated package/game invariant claim cost no solver call. Only project lemmas
  need one.
- `equal-output` stops being a verdict on the Domino listing. `equal-aborts` and `same-output` have
  different dependency sets there and cannot share one. It survives as a presentation grouping in
  the EasyCrypt report, where both claims genuinely do have no dependencies.
- `domino debug --easycrypt` is deleted rather than aliased. Its meaning under the new axes would
  be "sequential on EasyCrypt", which is precisely the cell we decided not to build.
