# Story 22 — implementation report

## What changed

- `Plumbing { DoneGuard, CallResult }` lives in `src/debug/ir.rs`. `InlStmt::Branch` gained
  `plumbing: Option<Plumbing>`; both Domino IR constructors set `None`.
- `src/writers/easycrypt/lower.rs`: `if (!ec_done) { B }` is no longer spliced. `lower_if` emits it
  as a labelled `Branch` with `cond` = the literal `true` (`Expression::boolean(true)`), an empty
  `els`, `then_lines` covering `B`, and `plumbing: Some(DoneGuard)`. The listing text is unchanged
  (the rows were always printed); they are now labelled sites. Guards `!(ec_rN = None)`
  (`call_result_guard`: `Not(Equals[Generated ec_r*, None])`) get `Some(CallResult)`. Every other
  EasyCrypt branch is `None`.
- Router prelude (`if (!abort_flag)`) and tail (`if (ec_result = None) { abort_flag <- true }`) stay
  out of the IR by design; recorded in the `lower.rs` module doc. Stories 26/27 must know the
  router's shape from `game.rs`, and treat a lockstep terminal as matching any EasyCrypt skeleton
  left on that side.
- `src/debug/exec.rs`: one destructuring gained `..`. The executor itself is unchanged: `true` is
  decided by the solver like any condition.

## Path counts (`count_terminals`, EasyCrypt vs Domino)

| Game | before | after | Domino |
|---|---|---|---|
| `Game_MON_CCA_PKE` | 10 | 12 | 6 |
| `Game_MOD_CCA_PKE_Real_KEM` | 28 | 32 | 16 |

Each `DoneGuard` adds one structurally present, infeasible else child.

## Goldens

`testdata/easycrypt/story08/*.txt` did not change: they hold the listing text, which already
printed the guard rows, and labels are not printed. Plain `domino inline` is untouched.

## Verification

New test `plumbing_branches_are_labelled_decision_points` (every `if (!ec_done)` row is a `Branch`
with `DoneGuard`, `true` condition, empty else; every `if (!(ec_r` row is `CallResult`; all others
`None`). `plumbing_variables_never_reach_the_ir`, `executor_walks_every_structural_path`,
`no_path_reads_an_unbound_local_...`, `listing_compiles_as_an_easycrypt_procedure` pass.

## State handed to the next story

- Story 23 sees `DoneGuard` conditions as literal `true`: "determined", taken on its side alone.
  `CallResult` guards are ordinary branches over `ec_rN` and are decided by the solver, with the
  callee's return value bound to `ec_rN`.
- A path that reaches a `DoneGuard` else side is infeasible; the solver prunes it.
