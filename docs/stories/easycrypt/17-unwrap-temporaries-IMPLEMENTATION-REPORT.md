# Story 17 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (395 passed, 5
`#[ignore]`d: the same 5 as after story 16, none failing) and `cargo clippy --workspace
--all-targets` are clean. `easycrypt` (`r2026.06-12-g7e192dd`) and
`cvc5` 1.3.4 were both on `PATH`, so every compile-shaped test ran for real. The story-16
differential test, `cargo test --workspace -- --ignored easycryptify_matches_treeify`, passes. It
now covers 4 more synthetic oracles aimed at this story, and takes about 37 s where it took 75 s
before, because the easycryptified side has fewer paths.

## 1. What changed

- **`src/transforms/easycryptify.rs`**: a new pass, `guard_unwraps`, which `lower_oracle` runs on
  each oracle body before the story-16 lowering (§3). It implements rules 1–3 of story 17 §3 on
  one shared invalidation analysis.
  - The Lowerer's own `Unwrap`-assignment arm is **gone**. `guard_unwraps` now emits every unwrap
    guard itself, as an `assert`-shaped
    `if (not (e == None)) {} else { abort }` at the binding's position. The lowering's existing
    `(_, Always)` case turns that into exactly story 16's guard: the continuation moves into the
    then-branch, and the else-branch becomes `ec_done <- true`. So `Term` now counts a
    whole-right-hand-side `Unwrap` assignment as `Never`, and `term_rules` changed to match.
  - **New error enum `EasyCryptifyError`** (`UnsupportedLoop` | `TemporaryNameCollision`) is the
    transform's `Err`. `TemporaryNameCollision { name, span }` is the §3.4 hard error.
  - `lower_oracle` takes a `reserved: &BTreeSet<String>`: the package's parameters and state
    fields, plus the oracle's arguments. `Transformation` builds it.
  - A containment check, `every_unwrap_is_guarded`, runs as a `debug_assert!` after lowering
    (§3.3: "assert the containment").
  - **13 new unit tests** (32 in the module now). The 19 story-16 tests are unchanged except for
    `term_rules` and the new `lower_oracle` argument.
- **`src/transforms/theorem_transforms.rs`**: new variant
  `EquivalenceTransformError::EasyCryptTemporaryNameCollision`, and a
  `From<EasyCryptifyError>` impl.
- **`src/writers/easycrypt/mod.rs`**: `From<EasyCryptifyError> for EcExportError`. A loop still
  maps to `UnsupportedStatement`. A name collision surfaces as the transparent
  `EcExportError::Transform(…)`, span label intact.
- **`src/writers/smt/expr_expr.rs`**: an `Unwrap` *nested inside* an expression now lowers to
  `(maybe-get e)` instead of panicking.
  - Why: after this story, `First[Unwrap(sid)]` appears in easycryptified Domino, and the
    executor lowers expressions through `SmtExpr::from`. The differential test cannot run without
    this.
  - `maybe-get` is exactly EasyCrypt's `oget`: total, with an unspecified value on `mk-none`.
  - The `prove` pipeline is unaffected: `unwrapify` still hoists every unwrap there, so the arm
    is unreachable from it.
  - `expr_term.rs` has the same panic and was left alone; nothing reaches it with a nested
    unwrap.
- **`src/writers/easycrypt/package.rs`**:
  - the `translate_table_write` doc comment no longer claims `rhs` is never `Unwrap`-headed. It
    can be now, and the general arm already handles it correctly;
  - the story-16 test `…noprfkey_send3…a_guard_per_join` became `…_and_one_flag_guard`, with
    1 guard instead of 2 (§4);
  - a new test, `full_4whs_kx_nochecks_send3_cascade_has_one_sid_guard_and_no_temporaries`,
    pins the §1.2 cascade text.
- **`src/debug/easycryptify_differential.rs`**: four new synthetic oracles, each run on both
  sides (§5).
- **`testdata/easycrypt/story03/4WHS/Pkg_{KX,KX_NoKeys,KX_NoPrf,PRF,Prot,Prot_NoKey,Prot_NoPrf}.ec`**:
  regenerated, and every hunk read (§6).
- **`docs/stories/easycrypt/08-ec-ir-lowering.md`**: new §2.4 with the facts story 08 needs from
  this one.

`unwrapify.rs` and `treeify.rs` are untouched.

## 2. The algorithm as implemented

`guard_unwraps` walks the unwrapified body once, **in the source's block structure**, carrying:

- **facts**: operands known to be `Some` here;
- **`inlined`**: a map from `unwrap-N` to `Unwrap(e)`, scoped to the rest of the block that binds
  it.

Each statement first has the `inlined` map applied to its own expressions. Then, for a binding
`p <- Unwrap(e)`:

1. **Rule 2.** If `e` is already a fact, no guard is emitted. Otherwise the assert-shaped guard is
   emitted and `e` becomes a fact. Facts are cloned into each branch of an `if` and never flow
   out of it, so a guard in one branch never covers the sibling branch or the code after the
   `if`. That is the sibling-branch rule, enforced structurally. Nothing is hoisted, and no
   dominator analysis is involved.
2. **Rule 1.** If `p` is an `unwrap-N` temporary, `size(e) ≤ 6` and `inlining_is_sound`, the
   binding is deleted and every later use becomes `Unwrap(e)`.
3. **Rule 3.** Otherwise the binding stays. If `p` is a temporary, it is recorded as a survivor.

**Invalidation (§3.2).** A fact is killed by any write to a name it reads:

- a local or state field: the pattern's identifier;
- a table: any `T[…] <-`, whatever the index;
- after an `if`: everything either branch writes;
- in a `for`: everything the body writes, killed *before* the body is walked;
- after an `invoke`: only the local it binds. The callee is another package, and packages share
  no state (§2.2).

`inlining_is_sound` uses the same notion of a write. It walks the rest of the block in execution
order, statement by statement, and fails if any use of the temporary is reached after a write to
a name the operand reads. For an `if`, the "written" flags of the two branches are OR-merged.

**Naming survivors (§3.4).** A survivor of `Unwrap(x)`, where `x` is a plain identifier that is
not itself an `unwrap-N`, is renamed `x_v`. Otherwise it keeps its `unwrap-N` name. The story's
two sentences about collisions are read as follows:

- **ambiguous**: two survivors derive the same name. Both keep `unwrap-N`. This is not a silent
  rename, because nothing takes the derived name.
- **colliding**: the derived name is already an identifier of the oracle (body, arguments) or of
  its package (parameters, state). This is `TemporaryNameCollision` with the binding's span.

**The guard never moves.** Every emitted guard sits exactly where `unwrapify` placed the binding.
Rules 1 and 2 only delete.

## 3. The two judgement calls

### Pass ordering (§3.5): **before** the story-16 guard generation

Story 17 recommends this order, and it turned out to be strictly better than cleaning up
afterwards, for three reasons:

1. **It removes joins, not just guards.** Once a dominated unwrap is a plain value, the lowering's
   `term_block` sees a block that cannot terminate, so no join is created for it.
   - `KX_noprfkey::Send3` and `::Send4` each lose their *second* `if (!ec_done)` guard this way.
     That is the "effectively dead" guard story 16 §4 pointed at.
   - A post-pass could delete the inner `if (!(sid = None))` guards, but it would leave the
     second `if (!ec_done)` and its `else { ec_done <- true; }` arms behind, unless it also
     re-derived the join analysis.
2. **The analysis sees the bindings where `unwrapify` put them.** "Structurally enclosed by an
   earlier guard" is simply "later in the same block, or nested in a later statement of it". This
   holds because the lowering then moves that whole suffix into the guard's then-branch.
   `every_unwrap_is_guarded` checks the result after lowering.
3. **One owner for unwrap guards.** The pass emits `assert`s, so the Lowerer's unwrap arm could be
   deleted, and there is no second place where an unwrap becomes a guard.

The cost is the `Term` change: a bare `x <- Unwrap(e)` is `Never` to the lowering. That is only
true because `guard_unwraps` always runs first. `lower_oracle` is the only entry point, so it
always does.

### Size threshold (§3.4): **`MAX_INLINED_UNWRAP_SIZE = 6` expression nodes**

`expr_size` is `1 +` the sizes of the children. So:

- a variable is 1;
- `T[k]` is 2;
- `T[Unwrap(First[sid])]` is 4;
- a table read at a 5-tuple key is 7, which is over the threshold.

Every operand in the example projects is 1, 2 or 4 nodes, so the threshold never fires on them.
It exists for genuinely large operands, and a unit test covers it
(`a_large_operand_keeps_its_temporary_but_not_its_duplicate_guard`).

The threshold counts AST nodes rather than rendered characters. That keeps the transform
independent of the EasyCrypt writer, and node count tracks the rendered token count closely.

Rule 1 never *repeats* an operand relative to story 16's output: each temporary had exactly one
use, and that use is replaced. So the threshold only guards readability of the nested `oget`.
Expect to revisit it if a large operand ever shows up.

## 4. Measurements

The script is story 16's methodology, re-implemented. It counts one extra line per proc (the
closing brace); the line counts below subtract it so they line up with story 16's table. Every
other column reproduces story 16's "after" row exactly.

| `Full4WHS` | lines | `if`s | depth | empty | tail copies | `unwrap_N` | `if (!ec_done)` | `sid = None` tests |
|---|---|---|---|---|---|---|---|---|
| `Pkg_KX_nochecks.ec` `Send3`, story 16 | 78 | 11 | 9 | 0 | 1 | 5 | 1 | 4 |
| `Pkg_KX_nochecks.ec` `Send3`, **story 17** | **56** | **8** | **7** | 0 | 1 | **0** | 1 | **1** |
| `Pkg_KX_noprfkey.ec` `Send3`, story 16 | 99 | 15 | 9 | 0 | 1 | 8 | 2 | 4 |
| `Pkg_KX_noprfkey.ec` `Send3`, **story 17** | **65** | **10** | **7** | 0 | 1 | **0** | **1** | **1** |
| `Pkg_KX_noprfkey.ec` `Send1`, story 16 → 17 | 22 → **20** | 3 | 3 | 0 | 1 | 1 → **0** | 0 | — |
| `Pkg_KX_noprfkey.ec` `NewSession`, story 16 → 17 | 14 → 14 | 1 | 1 | 0 | 1 | 0 | 0 | — |

**The §1.2 cascade** (`KX_nochecks::Send3`):

- counting `if (_mess = 2)` itself, **7 `if`s → 4**, and 4 temporaries → 0;
- below it, 6 → 3, which is the "three `if`s" of story 17 §1.2.

It is structurally the Domino source, with **one difference from §1.2's listing**: the `sid` guard
keeps an `else { ec_done <- true; }` arm. That arm is load-bearing. When `_mess = 2` and
`sid = None`, Domino aborts, and the tail after the `if (_mess = 2)` join
(`d_State.[ctr] <- state; ec_result <- Some msg_;`) must not run. §1.2 was written without the
flag. Removing the arm would need the `sid` guard to be provably dead, which it is not
syntactically (§7).

`KX_noprfkey::Send3` has the same cascade (spelled `mess`), then two guards for its `ReverseMac`
write (`ni` and `nr`, where the second `Unwrap(ni)` is dominated).

**Over every exported package file** (`Simple4WHS`, `Full4WHS`, `kem-dem-cca-ssp`; each file
counted once per theorem):

| | before | after |
|---|---|---|
| `var unwrap_N` declarations | 320 | **0** |
| `if` statements | 866 | 709 |
| lines of `Pkg_*.ec` | 6622 | 5698 |
| `if (!ec_done)` guards (distinct procs) | 35 | 33 |
| procs that declare `ec_done` (distinct) | 30 of 149 | 30 of 149 |

No oracle loses its flag entirely. The two guards removed are the nested second joins of
`KX_noprfkey::Send3`/`Send4`. Story 16 hoped the dominated-guard rule would make "many" flags
droppable. It does not, because every remaining flag is set by a guard that is *not* dominated:

- the first `Unwrap(sid)` of a cascade;
- the `k` guard in `KX::Test`;
- the invokes in `ReductionMac::Run*` and kem-dem.

Those exits are infeasible only semantically (e.g. `sid` comes out of a `State` entry that was
already checked). Syntactic dominance cannot see that. See §7.

## 5. Tests

**Unit tests** (`src/transforms/easycryptify.rs`), mapped to §4 of the story:

| §4 criterion | test |
|---|---|
| `Send3` cascade → one guard, no temporaries | `send3_cascade_collapses_to_one_guard_and_no_temporaries` |
| invalidated by a table write: temp and both guards kept | `a_table_write_between_binding_and_use_keeps_the_temporary_and_both_guards` (a write at a *different* index still invalidates) |
| invalidated by a reassigned local | `a_reassigned_local_between_binding_and_use_keeps_the_temporary_and_both_guards` (the survivor is named `m_v`) |
| sibling branches: no hoisting | `unwraps_in_sibling_branches_keep_their_guards_in_place` (siblings, plus an unwrap after the join) |
| `invoke` between binding and use | `an_invoke_between_binding_and_use_invalidates_nothing_the_caller_reads` (comment names DAG / own-package / no-shared-state), plus `an_invoke_invalidates_the_local_it_binds` |
| derived name / collision is a hard error with a span | `a_derived_name_collision_is_a_hard_error_with_a_span` (a body local, and a caller-reserved name), `ambiguous_derived_names_fall_back_to_the_counter_names` |
| size threshold | `a_large_operand_keeps_its_temporary_but_not_its_duplicate_guard` |

Also:

- `a_dominated_unwrap_inside_a_branch_causes_no_join` (the second-join removal);
- `a_nested_unwrap_is_substituted_into_the_outer_operand`;
- `the_guard_containment_check_catches_an_unguarded_unwrap`;
- **`no_example_repeats_an_unwrap_guard_on_one_path_or_keeps_a_temporary`**, run over hello-world,
  simple-KEM, kem-dem and both 4WHS theorems. On every path it checks that each
  `not (e == None)` is tested at most once, that no `unwrap-N` survives, and that every `Unwrap`
  is contained in a guard.
  - The one allowed repeat is a guard directly under the user's own `assert not (e == None)`.
    Those operands are read off the `DebugTransform` body; see §7.
  - Sensitivity was checked by hand: with rule 2 disabled, it fails on `CPA::Test`.

**Differential test.** Four synthetic oracles were added and run on both sides:

- `Dominated`: two dominated guards, one across an `if` and one across an invoke, with a
  *feasible* first abort;
- `AfterJoin`: an unwrap after a join whose other branch never unwrapped;
- `TableWritten`: `u[j] <- None` between two `Unwrap(u[k])`;
- `LocalReassigned`.

Path counts are 8×15, 5×13, 3×5 and 3×5. `Send3` went from 26×228 to 26×75.

**Mutation check, by hand**, with the transform restored afterwards:

- making `kill` a no-op fails on `TableWritten` (cvc5: `sat`);
- letting facts leak out of an `if`'s branches is caught first by the containment
  `debug_assert`. With that assert disabled too, the differential test fails on `AfterJoin`.

## 6. State handed to the next story

- **Golden paths that changed:**
  `testdata/easycrypt/story03/4WHS/Pkg_{KX,KX_NoKeys,KX_NoPrf,PRF,Prot,Prot_NoKey,Prot_NoPrf}.ec`.
  - Each was regenerated from `domino easycrypt` output (they are byte-identical to the
    `Simple4WHS` export) and read hunk by hunk. Only `unwrap_N` lines and dominated guards
    disappear, and `oget e` appears where the temporary was.
  - `Prot::Send2`'s five `Unwrap(ni)` guards became one. `KX::Test`'s `k` guard, which is in a
    branch before a join, correctly stays.
  - `hello-world`'s `Pkg_{Fwd,Rand}.ec`, every story04/06 golden (games, interfaces, invariants)
    and every `Eq_*` golden are unchanged.
  - Across the fresh exports, only `Pkg_*.ec` files differ. `Comp_*`, `Eq_*`, `Interfaces.ec`
    and `Types.ec` are byte-identical to story 16's.
- **EasyCrypt compile** of every `Types.ec` and `Pkg_*.ec` of `Simple4WHS`, `Full4WHS` and
  `kem-dem-cca-ssp`, plus the in-suite full-tree compile tests:
  - everything compiles;
  - the `may use uninitialized local variables` warnings are **identical** to story 16's: 13,
    all from the flag-join shape (`KX*::Test`, `ReductionMac::Run2–4`, kem-dem `DEM::ENC`,
    `MOD_CCA_PKE::PKDEC`, `MON_CCA_PKE::PKENC`);
  - no new warnings.
- **`domino easycrypt`** exports `kem-dem-cca-ssp` and both 4WHS theorems cleanly. hello-world and
  simple-KEM still fail on their invariant `.smt2` files (`unsupported SMT sort <GameState_…>`),
  unchanged from story 16 §10. Their package modules are still covered by the golden and
  transform tests.
- **Temporaries that survive: none**, across hello-world, simple-KEM, kem-dem and both 4WHS
  theorems (pinned by the repo-wide test). This is because `unwrapify` always places a binding
  directly before its one use, so nothing can invalidate it in between, and every operand is at
  most 4 nodes. Rule 1's invalidation check, the size threshold and the naming only fire on
  hand-built unit-test inputs.
- **For stories 08/09:**
  - `Unwrap` now appears *inside* expressions in exported code;
  - `expr_expr.rs` lowers it to `maybe-get`;
  - a whole-right-hand-side unwrap is still an `InlStmt::Unwrap` fork, with an infeasible
    `unwrap-none` child.
  These facts are written into `08-ec-ir-lowering.md` §2.4. Story 16 §8's warning about infeasible
  paths reading unassigned locals still applies.
- **Output is deterministic:** only `BTreeMap`/`BTreeSet`/`Vec` are used, and the existing
  `rendering_is_deterministic` passes.

## 7. Notes for follow-up

- **The assert-then-unwrap duplication is still there**, deliberately. Example:
  `if (!(d_State.[ctr] = None)) { if (!(d_State.[ctr] = None)) { state <- oget d_State.[ctr];`.
  - This is story 17 §6's deferred redundant-*condition* elimination. §4's "no two syntactically
    identical guard conditions on one path" is therefore read as "no two *unwrap* guards", and the
    repo-wide test exempts exactly the user-`assert` + unwrap pair.
  - The machinery makes it a one-line change: seed `facts` with the operand of an `assert not
    (e == None)` (`if` with an `[Abort]` else-branch) when walking past it. It needs the owner's
    sign-off.
- **Flags that stay because an exit is only semantically infeasible.** Examples: the first
  `Unwrap(sid)` of `Send3`/`Send4`, `k` in `KX*::Test`, and invokes whose callee never aborts.
  Removing them needs either invariants or a callee-can't-abort analysis. That is not syntactic,
  and not this story.
- **`ec_r<N>` invoke temporaries are untouched** (not `unwrap_N`). An example is
  `d_return <- oget ec_r1; (state, msg_) <- d_return;`. The same substitute-the-value idea would
  shorten that to `(state, msg_) <- oget ec_r1;`. It is out of scope.
- **Some inlined lines are long**, e.g.
  `(_U, _u, …, _mess) <- oget d_State.[oget d_First.[sid]];` in `KX::AtLeast`. That is within
  the threshold, since its operand is 4 nodes. If a reader objects, lower
  `MAX_INLINED_UNWRAP_SIZE` to 3. That keeps a temporary for every operand whose index is itself
  an unwrap. It would be named `unwrap_N`, since the operand is not a plain identifier.
- **`src/writers/smt/expr_term.rs`** still panics on a nested `Unwrap`. Nothing reaches it with
  one today. Mirror the `expr_expr.rs` change if something ever does.
- **Formatting:** only `easycryptify.rs` and `easycryptify_differential.rs` were run through
  `rustfmt` (both were clean at HEAD). The other touched files follow story 16 §10 and were not
  reformatted.
