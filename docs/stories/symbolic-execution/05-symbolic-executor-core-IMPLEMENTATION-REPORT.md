# Story 05 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. Not yet committed.

Read together with `docs/stories/05-symbolic-executor-core.md`. This is the "State handed to the
next story" for **story 06** (and 07, transitively).

`cargo build --workspace`, `cargo test --workspace` (110 lib tests, +8 new `debug::exec::tests::*`),
and `cargo clippy --workspace` all pass clean. `domino prove` / `latex` / `proofsteps` are
untouched.

---

## 1. What landed

| File | Change |
|---|---|
| `src/debug/exec.rs` | **new** (~850 lines incl. docs + 8 tests). The solver-free symbolic executor. |
| `src/debug/mod.rs` | `pub mod exec;` (before `pub mod ir;`). |
| `testdata/story05/hello_world_medium.smt2` | **new golden** (self-bootstrapping: missing → written + panic "re-run"). |

Nothing else was touched.

## 2. Public surface for story 06

`crate::debug::exec::{ Side, Step, Decision, Terminal, TerminalPath, ExecError, execute,
execute_streaming }`

```rust
pub enum Side { Left, Right }                    // Side::as_str() -> "left" | "right"

pub struct Step { pub label: Label, pub decision: Decision }
pub enum Decision { Then, Else, AssertHolds, AssertFails, UnwrapSome, UnwrapNone }
                                                 // Decision::as_str() -> "then" | "else" |
                                                 // "assert-holds" | "assert-fails" |
                                                 // "unwrap-some" | "unwrap-none"
pub enum Terminal { Return { label, value: Option<Expression> }, Abort { label } }
                                                 // .label() -> Label ; .is_abort() -> bool

pub struct TerminalPath {
    pub id: String,                 // always "" here — the driver assigns "L3" / "L3.R2"
    pub steps: Vec<Step>,
    pub decls: Vec<SmtExpr>,         // one `declare-const` per SSA var, in order
    pub constraints: Vec<SmtExpr>,   // `(assert (= <ssa> <rhs>))` + path conditions, in order
    pub return_constraint: SmtExpr,  // `(assert (= <return-{GI}-{O}> <constructed>))`
    pub terminal: Terminal,
}

pub enum ExecError { OracleNotExported { oracle, game_inst },
                     MaxPathsExceeded { explored: usize, limit: usize } }

pub fn execute(inlined: &InlinedOracle, game_inst: &GameInstance, sample_info: &SampleInfo,
               side: Side, max_paths: Option<usize>) -> Result<Vec<TerminalPath>, ExecError>;

pub fn execute_streaming(inlined, game_inst, sample_info, side, max_paths,
    on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>) -> Result<(), ExecError>;
```

- `game_inst` **must** be the same `DebugTransform` output `inlined` was produced from.
  `sample_info` is `GameInstAux::sample_info` for that instance.
- `execute` = `execute_streaming` collecting clones. Story 06 should prefer `execute_streaming`
  and stop early with `ControlFlow::Break` once it has decided a left path is uninteresting.
- `max_paths` counts **completed** paths. Hitting the cap is `Err(MaxPathsExceeded { explored,
  limit })` (with `explored == limit`), never silent truncation. `on_path` is *not* called for
  the path that trips the cap.

### The guarantee story 06 relies on

Asserting, on a solver that already has the story-06 base
(`emit_base_declarations + emit_theorem_paramfuncs + emit_game_definitions +
emit_constant_declarations(Some(O)) + randomness-mapping + invariant + claim assumptions`), a
single path's `decls` ++ `constraints` ++ `return_constraint` is a **complete, self-contained,
flat** encoding of that one execution of oracle `O` on side `side`. It constrains exactly the
`<return-{GI}-{O}>` constant that `emit_constant_declarations(Some(O))` left free;
`return-value-…`, `<return-is-abort-…>` and `<<game-state-…-new-O>>` stay constrained off it, so
the invariant / relation / `emit_claim_goal_negated` machinery is well-defined again.

## 3. How it works

- **Store.** `locals: HashMap<VarKey, Identifier>` (each value an `Identifier::Generated(ssa,
  ty)` → renders `<ssa>`), `pkg_state: HashMap<(pkg_inst, field), Identifier>` (global, **not**
  frame-scoped — mirrors the prover), `rand_ctr: HashMap<sample_id, usize>` (plain counter, 0 →
  n). Cloned at every fork.
- **SSA names.** `<v!{side}!{n}!{basename}>`, `n` a process-wide monotonic counter on the
  `Executor` (so names are globally unique across every path in a run, which keeps transcripts
  readable). `basename` = the last `::` segment of a `VarKey`, or the package-state field name.
- **DSA.** `Assign` / `Sample` / `Unwrap`-some / `Call` arg-bindings / callee-`Return` binding
  each: allocate a fresh const, push `declare-const` to `decls`, push `(assert (= <const>
  <substituted rhs>))` to `constraints`, rebind the store slot. `subst` walks the RHS with
  `Expression::map`, swapping tracked locals / package-state idents for their current store
  value and leaving constants / literals / theorem params alone (so they lower exactly as the
  prover's `From<&Expression> for SmtExpr`).
- **Forking.** `Branch` → then-child recurses to completion, then else-child continues in place
  (`(assert cond)` / `(assert (not cond))`). `Unwrap` → none-child terminates in `Abort` at the
  unwrap's **own** label with `(assert (= <inner> (as mk-none (Maybe T))))`; some-child continues
  with `(assert (not …))` and binds `(maybe-get <inner>)`. Recursion depth is bounded by branch
  *nesting*, not path count.
- **Continuations.** `Vec<Cursor>` "instruction-pointer stack"; `Cursor { block: &InlBlock, ip,
  kind: Sub | Call { bind } }`. `if`/`else` sub-blocks push a `Sub` cursor with the same
  meaning; a `Call` body pushes a `Call` cursor. A `Return` is a **terminal** iff no `Call`
  cursor is on the stack; otherwise it pops cursors up to and including the nearest `Call`,
  binds that call's result, and the loop resumes the caller after the `Call` node (the
  continuation is **not** duplicated — that is why `treeify` is skipped). `Abort` is always a
  terminal, any depth.

## 4. Terminal game-state reconstruction — read this (story 05 §7, §8)

This is the part most likely to diverge from the prover. What I did and learned:

1. **Thread the game state through fresh SSA constants**, one per reconstruction step. The
   naïve version (fold everything into one nested term) blows up: `smt_increment_gamestate_rand`
   and `smt_update_gamestate_pkgstate` each *re-read the whole accumulator* for every field they
   copy, so two package folds over a rand-incremented state produced a ~5 KB single term for a
   3-statement oracle. Binding `<v!{side}!{n}!gamestate>` after each step keeps it flat and
   O(steps). These game-state constants use `Type::empty()` as a dummy in the `Identifier` (only
   `smt_identifier_string()` is used) but are `declare-const`'d with the real
   `octx.oracle_arg_game_state_pattern().sort()`.

2. **Order:** start from `<<game-state-{GI}-old>>`, then (a) `smt_increment_gamestate_rand` once
   per draw for each `sample_id` with a non-zero counter (sorted by id), then (b)
   `smt_update_gamestate_pkgstate` once per folded package instance, in `game().pkgs` order.
   The prover interleaves these (rand increments inside the sampling let-chain, package
   write-backs at invoke boundaries + at return), but the game-state selectors compose: rand
   updates and pkg-state updates use disjoint selectors, and re-folding an instance with its
   final field values is idempotent w.r.t. the prover's repeated write-backs of the same
   instance. Net state at the terminal is identical.

3. **Which package instances to fold:** entry instance ∪ every instance that appears as a `Call`
   callee anywhere in the body (`collect_call_pkg_insts`). This is exactly the prover's set —
   `smt_build_invoke` writes the caller back *unconditionally* before every invoke, and every
   caller is either the entry instance or another callee. Instances never touched are **not**
   folded, so the old game state keeps their value verbatim, exactly like the prover. These
   instances' fields are also the only package state seeded up front (from
   `smt_access_gamestate_pkgstate(old) ∘ smt_access_pkgstate`), which is identical to the
   per-oracle-fn `let` bindings in `smt_define_nonsplit_oracle_fn`.

4. **Randomness values vs. the zero-assert.** `Sample` uses the literal counter `k` (0-indexed)
   in `(__sample-rand-{gi}-{ty} <pos> k)`, where the prover uses the *term*
   `(access-rand <game-state>)` = `(+ 1 … (access-rand old))`. These agree **only** under
   `build_rands`' `(assert (= (access-rand old) 0))`, which story 06's setup emits
   (`emit_constant_declarations`). Counting from 0 is the intended design (story §4.3), not an
   approximation — but a standalone consistency check (see §6) must add that assert. The
   *terminal counter* materialisation, by contrast, matches the prover symbolically regardless
   (both are `n` nested `(+ 1 …)` over `(access-rand old)`).

5. **`return` term:** `Terminal::Return { Some(e) }` → `octx.smt_construct_return(<gs>, <subst
   e>)`; `Return { None }` → `smt_construct_return(<gs>, "mk-empty")`; `Abort` →
   `smt_construct_abort(<gs>)`. `return_constraint = (assert (= <return-{GI}-{O}> <that>))` with
   `<return-{GI}-{O}>` built as the literal string `format!("<return-{}-{}>", game_inst.name(),
   inlined.oracle_name)` — `inlined.oracle_name` is the exported/adversary-visible name, which is
   exactly `patterns::ReturnConst { oracle_import_name, .. }.name()`.

6. `octx.set_renamed(export.alias())` is applied before `octx.smt_arg_name(..)` so the seeded
   argument constants match `build_returns` (`arg-{GameName}-{alias-or-signame}-{argname}`).

## 5. Tests (`src/debug/exec.rs`, module `tests`)

Helper `with_debug(dir, theorem, |theorem, auxs|)` = `DirectoryProject::load` + `DebugTransform`.
`run(dir, theorem, game_inst, oracle)` = load + `inline_oracle` + `execute(Side::Left, None)`.

| test | fixture | checks |
|---|---|---|
| `hello_world_small_is_one_straightline_path` | `hello-world` `small_composition` / `UsefulOracle` | 1 path, `Return`, no `steps`; SSA names unique; 3 non-game-state decls; `return_constraint` names `<return-small_composition-UsefulOracle>` |
| `hello_world_medium_inlines_a_call_and_resumes` | `hello-world` `medium_composition` / `UsefulOracle` | 1 path; the callee's `return (ctr,rand)` bound `y` and the entry frame returned it (continuation ran) |
| `hello_world_useless_assert_forks_into_hold_and_fail` | `hello-world` `medium_composition_more_oracles` / `UselessOracle` | 2 paths: `AssertFails`→`Abort`, `AssertHolds`→`Return` |
| `simple_kem_test_branch_assert_unwrap_enumeration` | `simple-KEM-example` `Prot` / `TestSender` | 2 asserts × unwrap × 1 `if` → **5** paths, **3** `Abort`; the `UnwrapNone` path aborts at the unwrap's own label |
| `splitinvoke_continues_after_call_with_tuple_bind` | `test-splitinvoke` `game_split` / `Query` | 1 path; `(x,y) <- invoke` produced `el2-1` / `el2-2` tuple projections; continuation after the call ran |
| `max_paths_errors_with_progress` | `simple-KEM-example` `Prot` / `TestSender`, cap 2 | `Err(MaxPathsExceeded { explored: 2, limit: 2 })` |
| `kem_dem_pkenc_path_count_is_small` | `kem-dem-cca-ssp` `Game_MON_CCA_PKE` / `PKENC` | path count in `1..=64` (sanity — "tens not thousands"); SSA unique on every path |
| `golden_hello_world_medium` | `hello-world` `medium_composition` / `UsefulOracle` | full `decls` + `constraints` + `return_constraint` pinned as `testdata/story05/hello_world_medium.smt2` |

`kem-dem-cca-ssp` and `simple-KEM-example` are used as unit fixtures — safe, parse + transform +
inline + term-construction only, **no solver**. `4WHS` / `yao` are never touched.

## 6. The consistency check — **deferred to story 06** (story §5 permits this)

Story 05 §5's "the important one": `(and <path conditions>) ⇒ <return-const> = <oracle-fn> applied
to the old state`. I **did not** add the `#[ignore]`d system-`cvc5` variant. Reasons:

- The check needs the full single-side base (`emit_base_declarations` … `emit_game_definitions`
  … `emit_constant_declarations(None)` so `<oracle-fn>` is defined and `<return-{GI}-{O}>` is
  constrained), which only `EquivalenceContext` produces — and story 06 already builds exactly
  that and already cross-checks against `domino prove`.
- The golden test pins the encoding structurally; `kem_dem_pkenc_path_count_is_small` exercises
  the real branching/sampling/invoke shape.

**Story 06 must, as its first cross-check:** for one small oracle (e.g. `hello-world`
`medium_composition` / `UsefulOracle`, or `simple-KEM-example` `Prot` / `GetPK`), assert per
path `(=> (and constraints) (= <return-{GI}-{O}> <oracle-fn old consts args>))` is `unsat` to
negate — i.e. the per-path DSA agrees with the monolithic oracle function. If it does not, the
bug is almost certainly in §4 (terminal reconstruction) or the rand zero-assert dependency
(§4.4).

## 7. Deviations / notes for follow-up

- **`TerminalPath.id` is always `""`.** The driver (06) assigns `L{left_label}` /
  `L{…}.R{right_label}` or similar.
- **`decls` and `constraints` are separate `Vec`s**, both in dependency order. Story 06 emits
  all `decls`, then all `constraints`, then `return_constraint`, inside one `push`/`pop` scope
  per path (or per (left,right) pair).
- **Game-state SSA constants** (`<v!{side}!{n}!gamestate>`) appear in `decls`/`constraints` only
  at the terminal, interleaved by the same `ssa` counter — they are not special-cased, just
  filtered by name where a test needs the "real" DSA count.
- **`borrow_map` gap** (story 02 report §5): `subst` will `panic!` on
  `Neg/Inv/Pow/Mod/Concat/Sum/Prod/Any/All/Union/Cut/SetDiff` in oracle expressions. None occur
  in any current fixture; the fix (if ever needed) is to fill the arms in `src/expressions.rs`.
- **`Place::Tuple`** is destructured component-wise with `el{N}-{i+1}` accessors (matching
  `smt_build_parse`); discard elements are skipped. Only flat `Ident` lists occur in the corpus.
- **`Place::Index` (table write)** → `(store <current base value> <index> <value>)`, fresh const
  bound to the whole `store`, base rebound — matches `smt_build_assign` / `smt_build_sample`.
- No solver calls anywhere in this file, by design. Story 06 owns branch pruning.

## 8. State handed to story 06 — quick reference

- Call `execute_streaming(inlined, left_game_inst, left_sample_info, Side::Left, max_paths, …)`
  for the left side; for each left `TerminalPath`, `execute_streaming(…, Side::Right, …)` with
  solver-guided pruning layered on (the streaming callback is where you query the solver).
- Left path assumptions go on the solver **once, up front** (per story 04): randomness mapping,
  invariants, claim dependencies. Then per left path: `push`, assert its `decls` + `constraints`
  + `return_constraint`, then explore right paths, then `pop`.
- Vacuity check (overview §3): before the goal at a (left, right) terminal pair, `check-sat`
  of assumptions + both path conditions; `unsat` ⇒ **unreachable**, not verified.
- `Decision::as_str()` gives the label strings for `trace.json` / the HTML tree.
