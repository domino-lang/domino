# Story 16 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (381 passed, 5 `#[ignore]`d:
the 4 that were already there plus the new differential test, none failing) and
`cargo clippy --workspace --all-targets` are clean. `easycrypt` (`r2026.06-12-g7e192dd`) was on
`PATH`, so every compile-shaped test ran for real. `cvc5` 1.3.4 was on `PATH`, and
`cargo test --workspace -- --ignored easycryptify_matches_treeify` passes (about 75 s).

## 1. What changed

- **New `src/transforms/easycryptify.rs`**: the Domino→Domino transform (§3.1–3.4), with 19 unit
  tests (`CodeBlock` in, `CodeBlock` out, no solver).
- **`src/transforms/theorem_transforms.rs`**: new `EasyCryptTransform`. The old
  `run_treeify: bool` is now `enum ControlFlowLowering { Treeify, None, EasyCryptify }`.
  `easycryptify` runs last, after `tableinitialize`. `EquivalenceTransformError` gains
  `EasyCryptUnsupportedLoop(easycryptify::UnsupportedLoopError)`. `EquivalenceTransform` and
  `DebugTransform` behave exactly as before (`Treeify` / `None`). `treeify.rs` is not touched.
- **`src/writers/easycrypt/export.rs`**: `export_theorem` runs `EasyCryptTransform`. Every writer
  test module (`package`, `interfaces`, `game`, `invariant`, `typesfile`, `proof`) switched to it
  as well, so they test what is actually exported.
- **`src/writers/easycrypt/package.rs`**: the oracle translator is now a near-identity lowering
  (§3.5):
  - The continuation nesting for `Unwrap` and `Invoke` is gone, and so is the early
    return-and-discard on `Return`/`Abort`. `Abort`, a `Return` anywhere except last, and `For`
    are all `unreachable!`.
  - The trailing `Return(Some(e))` becomes the proc's `return e;`.
  - An `if` with an empty else block renders with no `else`.
  - `declare_temp` and the synthesised `ec_result` are gone.
  - `build_import_procs` no longer wraps the return type in an option; the signature is already
    `Maybe(T)`.
- **Option wrapping removed** at `interfaces.rs` (`build_export_procs`) and `game.rs` (the import
  adapter and the router's export procs). The router reads the inner type back out of the
  `Option` for its `None_` annotation. The `invariant.rs` `EcType::Option` uses are untouched.
- **`src/writers/easycrypt/mod.rs`**: `EcExportError::Transform` is no longer `#[from]`. A manual
  `From<EquivalenceTransformError>` maps the `for`-loop error to the same
  `UnsupportedStatement { construct: UNSUPPORTED_FOR, span }` the writer raised before, with the
  span kept.
- **`src/writers/smt/expr_expr.rs`**: `ExpressionKind::Bot` now lowers to `mk-empty` instead of
  panicking with `"bot is broken"`. §3.3 makes `easycryptify` emit `Some(())` for a valueless
  `return`, and the SMT lowering is what the executor, and so the differential test, runs on. The
  parser never produces `Bot`, so nothing else is affected.
- **`src/debug/driver.rs`**: the comment at the transform split now names the third transform and
  says why the debugger does not use it (§3.6).
- **`src/debug/ir.rs`**: two regression tests:
  - `plain_domino_listing_still_renders_assert` checks that a plain `DebugTransform` listing of
    kem-dem `PKENC` still says `assert (`.
  - `easycrypt_transform_listing_has_no_assert` checks that the `EasyCryptTransform` listing has
    no `assert` and no `abort`, so the two views differ by construction.
- **New `src/debug/easycryptify_differential.rs`**: the §5.1 cvc5 test (`#[ignore]`).
- **`docs/stories/easycrypt/17-unwrap-temporaries.md`**: new §2.1a with the facts story 17 needs
  (see §8).

## 2. `Term` and the lowering as implemented

`Term` follows §3.2 exactly, with two clarifications:

- An `Assignment` counts as an unwrap only when its whole right-hand side is `Unwrap(_)`, which is
  the only shape `unwrapify` leaves.
- A `For` is `Term::Maybe` (conservative). The hard error is raised when `lower` reaches it, as
  `UnsupportedLoopError { span }`. A `For` after an always-terminating statement is dead code and
  is dropped like any other.

The lowering follows §3.3, with these refinements:

1. **A join with an empty `REST` emits no guard.** It returns `(out, d1 || d2)` so the enclosing
   block guards its own continuation. Without this, every nested join would emit an empty
   `if (!ec_done) {}`.
2. **Flipping after the drop.** When `ec_done` is dropped (§3.4) and an `if`'s then-branch held
   nothing but `ec_done <- true` (source `if c { abort }`), the `if` becomes `if (not c) { … }`.
   Otherwise the writer would emit an empty then-branch. An `if` that had an empty branch in the
   source is left as the source had it. This is what keeps "the output of an abort-free oracle is
   statement-for-statement the input" true.
3. **Invoke into a table.** `T[k] <- invoke O()` stores the value, so it lowers to
   `ec_rN <- invoke O(); if (not (ec_rN == None)) { T[k] <- Some(Unwrap(ec_rN)); … }`. No project
   uses this shape; it has a unit test.
4. **The invoke itself is retyped.** It gets `return_type: Some(Maybe(T))` and an embedded `Edge`
   whose signature is wrapped, so the output typechecks as Domino. `T` is taken from the resolved
   edge's original signature, falling back to `return_type`.
5. **Signatures that travel.** These are all rewritten together:
   - `OracleDef.sig`;
   - every package's `imports`;
   - `Composition.edges`;
   - `Composition.exports`;
   - the `Edge` embedded in each invoke.

   `split_exports` does not exist on this branch.
   `every_oracle_of_every_example_satisfies_the_contract` checks all of them over hello-world,
   simple-KEM, kem-dem-cca-ssp, both 4WHS theorems, test-splitinvoke and test-loopunroll. That is
   more than 100 oracle bodies, and it checks that each embedded edge equals the callee's
   definition.

## 3. Naming and the `ec_done` drop

- The names are `ec_result : Maybe(T)`, `ec_done : Bool` and `ec_r<N> : Maybe(T_callee)`, all
  `Identifier::Generated`. `N` is a per-oracle counter starting at 1, in lowering order. The
  constants `EC_RESULT`, `EC_DONE` and `EC_INVOKE_PREFIX`, plus `is_generated_name`, live in
  `easycryptify.rs`.
- **Correction to §3.4, which says these "mangle to themselves": they do not.** The mangler's
  rule 4 reserves the `ec_` prefix and would render them `d_ec_result`. The writer now resolves
  every variable through `var_name`, which passes a `Generated` identifier satisfying
  `is_generated_name` through unmangled. A *user* identifier `ec_result` still becomes
  `d_ec_result`, so the two can never collide (`a_user_local_named_ec_result_does_not_collide`).
  To make that work, `record_local` now dedups declarations by their EasyCrypt name instead of
  the raw name.
- The writer keeps one temporary of its own: a sample into a table entry (`T[k] <-$ τ`), which
  EasyCrypt cannot express directly. It is renamed `ec_s<N>` so it cannot collide with `ec_r<N>`.
  No project uses it.
- **The drop rule, as implemented:** after lowering an oracle, if no `IfThenElse` anywhere in its
  body has the condition `not ec_done`, every `ec_done <- …` assignment is deleted, including the
  initial `ec_done <- false`. That also removes the local's declaration, because it no longer
  appears in any assignment. The flip in §2 item 2 is applied during the same pass.
- `ec_result` is now declared as `var ec_result : T option;` and initialised by an
  `ec_result <- None;` statement, instead of `var ec_result : T option <- None;`. `collect_locals`
  still puts it first. This is cosmetic golden churn.

## 4. Measurements

All counts come from one script, run on `domino easycrypt` output before the change (built from
`HEAD`) and after it. "Depth" is the brace depth inside the proc. "Empty" counts `{ }` bodies,
blank lines included.

| `Full4WHS` | lines | `if`s | depth | empty branches | tail copies | `unwrap_N` | `if (!ec_done)` |
|---|---|---|---|---|---|---|---|
| `Pkg_KX_noprfkey.ec` `Send1`, before | 26 | 3 | 3 | 3 | 1 | 1 | — |
| `Pkg_KX_noprfkey.ec` `Send1`, after | **22** | **3** | 3 | **0** | 1 | 1 | 0 |
| `Pkg_KX_noprfkey.ec` `Send3`, before | 130 | 19 | 12 | 16 | 4 | 8 | — |
| `Pkg_KX_noprfkey.ec` `Send3`, after | **99** | **15** | **9** | **0** | **1** | 8 | **2** |
| `Pkg_KX_nochecks.ec` `Send3`, before | 79 | 10 | 9 | 7 | 4 | 5 | — |
| `Pkg_KX_nochecks.ec` `Send3`, after | 78 | 11 | 9 | **0** | **1** | 5 | **1** |
| `Pkg_KX_noprfkey.ec` `NewSession`, after | 14 | 1 | 1 | 0 | 1 | 0 | 0, no `ec_done` declared |

The story's §1.1 table says 131 lines and 17 empty branches for the "before" `Send3`. The script
here counts one line fewer and one empty branch fewer. The depth (12), `if` count (19), tail
copies (4) and `unwrap_N` count (8) all match.

- **`Send1` matches §1.2** in structure: three `if`s, no empty branch, no `else`. It has one line
  more than §1.2's listing, `state <- unwrap_1;`. That line belongs there. §1.2 was transcribed
  from output that had the bug described in §6 below.
- **`Send3` has two guards in `Pkg_KX_noprfkey.ec`, not one.** This is correct, and the story's
  acceptance line conflates two oracles. The oracle §1.1 *quotes* is `KX_nochecks::Send3`,
  rendered in `Pkg_KX_nochecks.ec`, and it has exactly **one** guard, with the tail once.
  `KX_noprfkey::Send3` also writes `ReverseMac[…Unwrap(ni)…Unwrap(nr)…]` inside
  `if (mess == 2)`, after the `First`/`Second` cascade. That write is a second, nested join, so it
  needs its own guard. Its 3-statement tail still appears once.
  - Tests: `full_4whs_kx_nochecks_send3_has_its_tail_once_and_one_flag_guard` and
    `full_4whs_kx_noprfkey_send3_has_its_tail_once_and_a_guard_per_join`.
  - `Send3` still has `else { ec_done <- true; }` arms. They are needed whenever the flag is kept,
    which is why its line count drops less than `Send1`'s.
- **Most of what is left is story 17's to remove.** That includes the duplicated
  `d_State.[ctr] = None` test and the eight `unwrap_N` temporaries. In
  `KX_noprfkey::Send3`, the second guard is also effectively dead: the `sid` guards it protects
  against are dominated by the first `Unwrap(sid)` guard.

## 5. Which oracles keep the flag

**30 of the 154 distinct `Package::Oracle` pairs** across hello-world, simple-KEM,
kem-dem-cca-ssp and both 4WHS theorems. That is about 20%, which is **more than a handful**. Every
one of them is a genuine join of §3.3's last case. None is spurious. They fall into four shapes:

1. **An `invoke` or `Unwrap` in an arm of an `if`, followed by more code.** This is the most
   common shape.
   - kem-dem: `DEM::ENC`, `MON_CCA_PKE::PKENC`, `MOD_CCA_PKE::PKDEC`. These use
     `if b { c <- invoke X(…) } else { c <- invoke X(…) }; …`.
   - 4WHS: `KX*::Test`, `ReductionMac::Run2`–`Run5`.
2. **A conditional `assert`, followed by more code.** 4WHS: `CR::MAC`, `CR::PRF`,
   `Nonces::Sample`. These use `if b { assert … }; …`.
3. **An early `return` inside nested `if`s.** 4WHS: `KX::SameKey`, `KX::AtMost`,
   `KX*::AtLeast`.
4. **The `First`/`Second` unwrap cascades.** 4WHS: `KX*::Send3`, `KX*::Send4`.

The flag can only be avoided in these oracles by duplicating the continuation, which is
`treeify`'s cost. Several of the guards protect only *infeasible* exits: in `Send3`, `Send4` and
`KX::Test`, every `sid = None` arm is already excluded by an earlier guard. Story 17's
dominated-guard rule should make many of these flags droppable.

## 6. A pre-existing writer bug, fixed as a side effect

The old `translate_block` did `return self.translate_invoke(…)` on an invoke, and so **discarded
every statement it had already emitted in the same block.** Two examples:

- `NewSession` lost `ctr_ <- ctr_ + 1; d_State.[ctr_] <- …;` and kept only the invoke and what
  followed it.
- Every `SendN` lost `state <- unwrap_1;`. `easycrypt compile` flagged those as
  `may use uninitialized local variables: … -> [state]`, and there were more than 60 such lines
  across `Full4WHS`.

The new writer lowers statement by statement, so nothing is dropped. The `state` warnings are
gone. What remains is below, and all of it comes from the flag:

- `KX*::Test -> [k]` or `[k_]`;
- `ReductionMac::Run2`–`Run5 -> [kmac, tau, tau_new, verified]`.

These locals are read in the guarded tail after a join. EasyCrypt's syntactic analysis cannot see
that `ec_done` protects the read. This is the "`ec_done` is dead code in Domino and load-bearing
in EasyCrypt" note of §6: the warnings are harmless, not errors.

## 7. The differential test (§5.1)

`src/debug/easycryptify_differential.rs`, `easycryptify_matches_treeify`, `#[ignore]`.

- Both pipelines run on the same theorem. The reference is `EquivalenceTransform` (treeified),
  executed as `Side::Left`. The easycryptified version is `EasyCryptTransform`, executed as
  `Side::Right`, **on the same game instance**. The two therefore share the argument constants,
  the old game state, the game constants and the `__sample-rand` functions. Only their SSA names
  differ.
- The test asserts that `samplify`'s sample positions are identical in the two pipelines.
- For every pair of terminal paths, cvc5 must find `base ∧ l ∧ r ∧ ¬agree` unsat. The `agree`
  condition is:
  - `(= gs_l gs_r)`, compared on aborts too;
  - and one of: `((_ is mk-none) v_r)` if the reference aborts, `(= v_r (mk-some v_l))` if it
    returns, `false` if the easycryptified path "aborts".
  - The easycryptified side has no `abort`. Its only abort terminals are the executor's
    `unwrap-none` children of already-guarded `Unwrap`s, and these must be infeasible.
- **Vacuity guard.** The base frame must be sat. Every feasible reference path must overlap at
  least one easycryptified path. At least one reference path must be feasible.
- One `cvc5 --lang=smt2 --tlimit-per=60000` script per oracle, using incremental `push`/`pop`.
  The in-crate `Communicator::new_cvc5()` starts cvc5 with `--no-incremental`, so the test spawns
  cvc5 itself. Any `unknown` or error fails the test.
- **Base frame.** It is the treeified `EquivalenceContext`'s:
  - `emit_base_declarations`, `emit_theorem_paramfuncs` and `emit_game_definitions`;
  - `emit_constant_declarations(Some(oracle))` **minus the `(assert (= <return-…> …))` ties of the
    other oracles**, which this check never mentions.

  `emit_constant_declarations` also asserts that the old randomness counters are 0. That restricts
  the prior state, but symmetrically for both sides.

**Oracles and path counts** (reference × easycryptified):

| oracle | paths | what it covers |
|---|---|---|
| `Full4WHS` hop 7 `H4 == H5`, left, `KX_nochecks::Send3` | 26 × 228 | the cascade: the flag, and the tail as one copy |
| `Full4WHS` hop 0 `H0 == H1_0`, left, `KX::Send2` | 6 × 15 | nested unwraps under an invoke |
| `Full4WHS` hop 0, left, `KX::NewSession` | 3 × 4 | no join, no flag |
| synthetic `AllAbort` | 2 × 2 | `(Always, Always)`, with the continuation dropped |
| synthetic `ThenAborts` | 2 × 2 | `(Always, _)`, with the continuation moved into `else` |
| synthetic `Join` | 3 × 7 | a join whose early exit (an `Unwrap`) is **feasible** |
| synthetic `NestedReturn` | 3 × 6 | a join after a nested `return` that is **feasible** |
| synthetic `Chain` | 5 × 38 | a bare invoke, and a callee that returns `Maybe(Integer)` and may abort |

The synthetic oracles run on both sides of their equivalence (`b = false` / `b`).

**Why there is a synthetic project.** No project in the repo has an oracle whose every path
aborts. Also, in the 4WHS oracles every early exit that reaches a join is infeasible, so there the
`ec_done` guard is not load-bearing. The synthetic project is written to a tempdir at test time:
two packages and one theorem.

**Mutation check, by hand.** Two deliberate bugs were planted in the transform. The test failed
on both, then the transform was restored:

- Emitting the post-join `REST` unguarded fails on `Join`.
- Moving the `(Always, _)` continuation into the wrong branch fails on `ThenAborts`.

**Two harness workarounds for executor limitations** (the executor itself is untouched):

1. The executor explores paths without a solver. On an *infeasible* easycryptified path, a local
   can be read before it is assigned: the body of an `if (!ec_done)` guard reached after a failed
   guard. The executor then leaves the raw symbol in the SMT (`<caller#0::y>`). That symbol is
   not even legal SMT-LIB, because `#` ends a simple symbol. The harness renames such symbols and
   declares them as unconstrained constants. This is sound, because an arbitrary value only makes
   disagreement easier to find. See §8 for why this matters to story 09.
2. The path's `return_constraint` is taken apart structurally,
   `(assert (= <return-…> (<mk-oracle-return-…> GS RV)))`, to get the final game state and the
   return value. The constraint itself is never asserted: the easycryptified side's `Maybe(T)`
   return datatype is not declared in the treeified base frame.

## 8. State handed to the next story

- **Golden paths that moved:** `testdata/easycrypt/story03/hello-world/Pkg_{Fwd,Rand}.ec` and
  `testdata/easycrypt/story03/4WHS/Pkg_{KX,KX_NoKeys,KX_NoPrf,PRF,Prot,Prot_NoKey,Prot_NoPrf}.ec`.
  Each was regenerated and read by eye: no empty branches anywhere, one `if` per source abort
  point, and the tails appear once.
  - `Pkg_KX.ec` has six flagged oracles, one guard each: `Send3`, `Send4`, `Test`, `SameKey`,
    `AtMost` and `AtLeast`.
  - `KX_NoKeys` and `KX_NoPrf` have one each, in `Test`.
  - The story04/story06 goldens (games, interfaces, invariants) and every `Eq_*` golden did not
    change. That confirms the router, the adapters and `Interfaces.ec` render the same
    `T option` as before, with no double wrapping.
- **EasyCrypt compile of the fresh export** (every `Types.ec`, `Pkg_*`, `Comp_*` and `Eq_*` of
  `Simple4WHS`, `Full4WHS` and `kem-dem-cca-ssp`): everything compiles. The only failures are the
  four known base-case gaps from story 15: `Eq_H0_H1_0`, `Eq_H1_1_H2_0`, `Eq_H3_1_H4` and kem-dem's
  one hop, each `cannot prove goal (strict)` at line 22. They are unchanged.
- **For stories 08 and 09: the flag selects the transform.** `--easycrypt` uses
  `EasyCryptTransform`. Without it, `DebugTransform`, unchanged. Do not reconcile the two listings.
  `plain_domino_listing_still_renders_assert` guards the Domino side. The easycryptified Domino is
  now close to 1:1 with the emitted EasyCrypt.
  - **Warning for 09:** when the executor runs on easycryptified code, *infeasible* paths can read
    unassigned locals and emit an illegal `<pkg#N::x>` symbol (§7, workaround 1). The debug
    driver asserts path prefixes into cvc5, so it will hit a parse error on such a path unless
    branch pruning cuts it first, or the executor binds unassigned locals to fresh constants.
    `Join`-shaped oracles are the reproducer. Story 09 should fix this in the executor, not work
    around it.
- **For story 17:** each `Unwrap(e)` guard sits exactly where `unwrapify` put the binding, and no
  abort moves. The facts story 17 needs are also written into its §2.1a:
  - `Pkg_KX_noprfkey.ec`'s `Send3` has two guards and an extra `ReverseMac` write. The §1.1 oracle
    is `KX_nochecks::Send3`, in `Pkg_KX_nochecks.ec`.
  - New `ec_*` locals must go through `is_generated_name`.
  - The differential test's oracle list.

## 9. Acceptance criteria

- [x] New `src/transforms/easycryptify.rs`. `treeify.rs` is unmodified. `DebugTransform` is
      unmodified in behaviour: it passes `ControlFlowLowering::None` instead of `false`.
- [x] A plain `domino inline` listing still renders `assert (…);`
      (`plain_domino_listing_still_renders_assert`).
- [x] Every exported oracle body has no `Abort` and exactly one `Return`, last
      (`every_oracle_of_every_example_satisfies_the_contract`).
- [x] `Send1` in `Pkg_KX_noprfkey.ec`: 3 `if`s, no empty branches, no `else`
      (`full_4whs_send1_has_one_if_per_abort_point_and_no_empty_branch`).
- [x] `Send3`: the tail appears once. There is exactly one `if (!ec_done)` in `KX_nochecks::Send3`
      (the §1.1 oracle), and two in `KX_noprfkey::Send3` because of its extra nested join (§4).
      The counts are recorded in §4.
- [x] `NewSession` declares no `ec_done` (`full_4whs_new_session_declares_no_flag`).
- [x] An oracle with no return value gives `unit option` and `Some tt`
      (`oracle_with_no_return_type_is_unit_option_and_some_tt`, now through `easycryptify`).
- [x] A `Maybe(T)`-returning oracle gives `T option option`
      (`oracle_already_returning_maybe_is_t_option_option`; also
      `signatures_are_rewritten_everywhere_together` at the Domino level).
- [x] `CodeBlock` unit tests cover:
  - each of the four `IfThenElse` cases, plus the flip;
  - `assert`, unwrap, invoke (bare and bound), and invoke into a table;
  - a nested `if` under an `if`;
  - the no-abort oracle, which is statement for statement the input plus the wrapper.
- [x] Running the transform twice does not panic (`running_the_transform_twice_does_not_panic`).
- [x] `cargo test --workspace easycrypt` is green. The goldens were regenerated and reviewed (§8).
- [x] Every generated `.ec` still compiles, except the known base-case gaps (§8).
- [x] `cargo build/test/clippy --workspace` are clean. The output is deterministic: no hash
      iteration anywhere in the transform, and the existing `rendering_is_deterministic` passes.
- [x] The differential test exists as `#[ignore]` and passes with cvc5 1.3.4.

## 10. Notes for follow-up

- **`domino easycrypt` still fails on `example-projects/hello-world` and `simple-KEM-example`**,
  both before and after this story. The error is `unsupported SMT sort <GameState_…>` from their
  invariant `.smt2` files: the invariant translation gap of story 07 §6.2 and story 15 §6. It is
  not touched here. Their package modules are still golden-tested through `story03`.
  `kem-dem-cca-ssp` and both 4WHS theorems export cleanly.
- **Flagged oracles keep `else { ec_done <- true; }` arms**, and `ec_done <- true` after the final
  `ec_result <- Some …`, even where nothing reads the flag afterwards. A liveness-based drop
  finer than §3.4's all-or-nothing rule would shorten them. It is not required by this story.
- **EasyCrypt `may use uninitialized local variables` warnings** now come only from the flag-join
  shape (§6). If they bother a reader, initialising such locals to their type's default before
  the join would silence them. That is a writer or transform tweak, and a behaviour-visible
  choice.
- **The repository is not `rustfmt`-clean**, for example `src/debug/driver.rs`, `exec.rs` and
  most of `src/writers/easycrypt/`. Only the two new files were formatted, to keep the diff
  reviewable.
- The comment on the old `EquivalenceTransformError` (`only pipeline failure a parser-accepted
  project can still trigger`) is now true only of `EquivalenceTransform`/`DebugTransform`. The
  new variant documents that only `EasyCryptTransform` raises it.
