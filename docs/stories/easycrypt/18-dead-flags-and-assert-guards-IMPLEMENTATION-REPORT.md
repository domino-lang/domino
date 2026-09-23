# Story 18 — implementation report

Both parts are implemented in `src/transforms/easycryptify.rs`. The parser is untouched.

- **Part A:** `prune_done` (backwards liveness over the loop-free tree) replaces
  `contains_done_guard` and `drop_done`. It also flips every `if` left with an empty *then* and a
  non-empty *else* (`flip_if_then_empty`), collapsing `not (not c)` to `c`. A `debug_assert!`
  (`ec_done_is_only_read_by_done_guards`) checks that done guards are the only readers.
- **Part B:** `some_test` recognises `not (e == None)` and is shared by `UnwrapGuards::block` and
  `every_unwrap_is_guarded`. `e` becomes a fact inside the *then* branch, and after the `if` when the
  *else* always terminates and the *then* does not write anything `e` reads.

## Measured (`Full4WHS`, `Simple4WHS`, regenerated with `domino easycrypt`)

| | before | after |
|---|---|---|
| `ec_done <- true;` in `Full4WHS/Pkg_KX.ec` | 31 | 8 |
| same, all `Pkg_*.ec` of `Full4WHS` | 158 | 58 |
| same, all `Pkg_*.ec` of `Simple4WHS` | 50 | 13 |
| `Full4WHS/Pkg_ReductionMac.ec` | 48 | 22 |

Repeated `State[ctr]` / `LTK[kid]` tests on one path: 0 (asserted for every oracle of every example
by `no_example_repeats_an_unwrap_guard_on_one_path_or_keeps_a_temporary`, which no longer allows the
old `assert` exception).

The number of oracles that declare `ec_done` is unchanged in every `Full4WHS` package. Those oracles
still have a live guard, and only their dead writes went. `Pkg_Prot.ec` is byte-identical in both
theorems. `AtLeast` keeps its three `ec_done <- true` arms.

`Pkg_CR.ec` `MAC` now reads `if (!(A \/ B)) { ec_done <- true; }`, parenthesised, as in §3.2.

## Debugger (§3.5)

`src/writers/easycrypt/lower/tests.rs`:

- `executor_walks_every_structural_path`: `Game_MON_CCA_PKE` now also reaches the router abort
  (its outer `else { ec_done <- true }` arms were dead and pruned). Comment updated.
- `kem_dem_pkenc_path_counts`: **not unchanged, contrary to §3.5/§5.** The EasyCrypt counts went from
  `(12, 6)` and `(31, 16)` to `(10, 6)` and `(28, 16)`. The Domino counts are unchanged. An else side
  that used to end in its own abort leaf now falls through to the frame's shared exit, which merges
  some of the infeasible surplus that test already documents. `executor_walks_every_structural_path`
  still checks that executed paths equal `count_terminals`. **The owner should confirm this.**
- `every_ec_done_true_that_is_not_after_a_return_is_an_abort` passes unchanged.

## Other changed tests and goldens

- Goldens: `testdata/easycrypt/story03/4WHS/Pkg_KX*.ec`, `Pkg_PRF.ec`,
  `testdata/easycrypt/story08/inline-kem-dem-pkenc.txt`.
- `package.rs`: `Send1` now has 2 `if`s (was 3, the duplicate `State` test is gone); the `Send3`
  cascade expectation is dedented one level.
- `easycryptify.rs`: four expectations lost their trailing dead `ec_done <- true`;
  `an_oracle_where_nothing_can_exit…` expects the flipped `if (not d)`. New tests cover §5 A(a)–(f)
  and B(a)–(e).
- The example-project test asserts that pruning again is a no-op, which covers "every remaining
  write is live" and "no empty *then* beside a non-empty *else*".

## Deferred, still present

- `AtLeast`'s `if (b = false /\ !(d_First.[sid] = None) …)` followed directly by
  `if (!(d_First.[sid] = None))`: conjunctions are not recognised (§4.3).
- The negated form `if (e == None) { abort } else { … }`.
- General condition implication, merging adjacent guards, table-index disequality (story 16 §7).

## Verification

`cargo test --workspace` (419 passed), the ignored `easycryptify_matches_treeify` differential test
(passes), `cargo clippy --workspace --all-targets` (clean). Not run: `easycrypt compile` on the
exported projects.
