# Story 06 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. **Not committed** (commit message at
the bottom).

Read together with `docs/stories/06-debug-command-solver-guided.md`. This is the "State handed to
the next story" for **story 07**.

`cargo build --workspace`, `cargo test --workspace` (111 lib tests), `cargo clippy --workspace`,
and — with the env from `scripts/setup-cvc5-lib.sh` sourced —
`cargo build/test/clippy --workspace --features cvc5-lib` (121 lib tests, +3 cvc5lib) all pass
clean. `domino prove` / `latex` / `proofsteps` output is unchanged.

---

## 1. What landed

| File | Change |
|---|---|
| `src/debug/driver.rs` | **new** (~1000 lines incl. docs + tests). The `domino debug` driver: `DebugOptions`, `DebugError`, `DebugRun` + views, `run_debug_command`, `render_tree`. |
| `src/debug/render.rs` | **new** (~70 lines). `side_by_side(left, right) -> String` — the `inlined.txt` renderer. Minimal; `domino inline` (story 03) can build on it. |
| `src/debug/mod.rs` | `pub mod driver;` + `pub mod render;`. |
| `src/debug/exec.rs` | **story-05 gap fixed** — package consts in oracle expressions are now seeded into the store (see §3). +~90 lines, all story-05 tests + goldens still green. |
| `src/util/smtsolver/cvc5lib.rs` | `check_sat` accepts `unknown (TIMEOUT)` / `unknown (…)` as `Unknown`, not just bare `unknown` (a `tlimit-per` timeout answers `unknown (TIMEOUT)`). |
| `src/writers/smt/contexts/equivalence/emit.rs` | `generate_game_or_package_invariant_claims` lifted from `EquivalenceSmtDriver` onto `EquivalenceContext` (story 06 needs the same claim set). |
| `src/gamehops/equivalence/verify_fn.rs` | calls `self.eqctx.generate_game_or_package_invariant_claims()`; the three private `generate_*` fns removed. Behaviour identical. |
| `crates/domino/src/cli.rs` | `Debug` subcommand + args struct. |
| `crates/domino/src/main.rs` | `debug()` dispatch — real impl behind `#[cfg(feature = "cvc5-lib")]`, a clear error otherwise. Three new local `Error` variants. |
| `crates/domino/Cargo.toml` | `cvc5-lib = ["sspverif/cvc5-lib"]` feature (so `cargo … --features cvc5-lib -p domino` forwards it). |

No `Cargo.lock` change (`cvc5` was already locked by story 01).

## 2. Public surface for story 07

`crate::debug::driver::{ DebugOptions, DebugError, DebugRun, LeftPath, RightPath, StepView,
TerminalView, Verdict, Summary, run_debug_command, render_tree }`

```rust
pub struct DebugOptions { pub check_left: bool, pub check_right: bool,
                          pub timeout_ms: Option<u64>, pub max_paths: usize }
// Default: check_left=false, check_right=true, timeout_ms=None, max_paths=1000

pub fn run_debug_command<P: Project, B: SmtSolverBackend>(
    project: &P, req_proof: &str, req_proofstep: usize, oracle: &str, claim_name: &str,
    opts: &DebugOptions, backend: &B, out: Option<PathBuf>,
) -> Result<DebugRun, DebugError>;

pub fn render_tree(run: &DebugRun) -> String;   // the stdout text tree (§4.5 of the story)
impl DebugRun { pub fn is_ok(&self) -> bool; }   // exit-code criterion
```

`DebugRun` / `LeftPath` / `RightPath` / `StepView` / `TerminalView` / `Summary` / `Verdict` — see
`07-html-execution-tree-viewer.md` §2 (updated) for the exact fields. **No `serde` derives yet** —
story 07 adds them + `serde_json` + `trace.json`.

The driver is **generic over `SmtSolverBackend`** and has no `cvc5` dependency of its own — it is
compiled in the default build. Only `crates/domino/src/main.rs` constructs a `Cvc5LibBackend`, and
only there is `#[cfg(feature = "cvc5-lib")]`.

## 3. The two-transform split — read this

The `EquivalenceContext` machinery (`emit_game_definitions` in particular, which compiles every
oracle body into the monolithic nested SMT term via `smt_codeblock_nonsplit`) **requires
`treeify`** — without it an empty `then`/`else` block (every `assert` has one) hits
`innermost.unwrap()` at `writer.rs:86`.

So `run_debug_command` runs **both** transforms of the same theorem:

- `EquivalenceTransform` (with `treeify`) → the `EquivalenceContext` for the base frame, the
  invariants, the claim assumptions and the negated goal.
- `DebugTransform` (no `treeify`) → the `GameInstance` + `SampleInfo` fed to `inline_oracle` and
  the symbolic executor (story 02/05 need the 1:1 statement structure the labels depend on).

They line up because `samplify` / `sample_max_counter_extractor` run **before** `treeify` in the
shared pipeline, so `sample_info`, argument names, `<return-{GI}-{O}>` names and the game-state
constants are byte-identical between the two. The `per_path_dsa_agrees_with_the_oracle_function`
test proves it: for `hello-world` it asserts the non-treeified per-path DSA forces
`<return-…> = <oracle-fn …>` (from the treeified base with `emit_constant_declarations(None)`) —
`unsat` to negate on every path. This is **the story-05 consistency check** the story asked for
first; it passes.

### Package consts in oracle expressions (story-05 gap, fixed here)

Story 05's `subst` left package/game consts untouched, expecting `From<&Expression> for SmtExpr`
to lower them — but for a `PackageIdentifier::Const` that produces a **bare atom**
(`isideal_kem_cpa_security`), which is undeclared standalone. The prover only gets away with it
because `smt_define_nonsplit_oracle_fn` wraps the body in
`(let ((isideal_kem_cpa_security (<pkg-consts-…> (<pkgconsts-…> <game-consts>))) …) …)`.

Fix in `src/debug/exec.rs`:

- `collect_referenced_pkg_consts` scans the inlined body for `PackageIdentifier::Const`
  identifiers actually used in an expression.
- `Executor::initial_state` seeds **only those** as DSA constants:
  `(<pkg-consts-{Pkg}-{c}> (<pkgconsts-{Game}-{inst}> <<game-consts-{GI}>>))`, mirroring
  `bind_pkg_consts`. `<<game-consts-{GI}>>` = `octx.oracle_arg_game_consts_pattern()
  .unit_global_const_name(game_inst_name)`, defined by `emit_game_definitions`.
- `SymState.pkg_consts: HashMap<(pkg_inst, name), Identifier>`; `SymState::lookup` gets a
  `PackageIdentifier::Const` arm.

Seeding *only referenced* consts keeps every story-05 golden byte-identical (they reference none —
`Bits(n)` is a `CountSpec`, not an expression).

**Still not handled (nothing in the corpus hits it):** `GameIdentifier::Const` used directly in an
oracle expression (post-transform they resolve to package consts in every current fixture), and
package consts used only inside a table *index* expression. If a future project trips this, extend
`collect_referenced_pkg_consts` / `lookup` the same way.

## 4. How the driver works

**Base frame**, asserted once at solver level 0 (`base_frame`), in the story's order:
`emit_base_declarations`, `emit_theorem_paramfuncs`, `emit_game_definitions`,
`emit_constant_declarations(Some(oracle))`, `emit_auto_randomness`, `emit_invariant`,
`emit_return_value_helpers`, `emit_randomness_mapping_condition`, `emit_claim_assumptions`.

**Exploration** (`explore_paths`): all left `TerminalPath`s from `execute_streaming` (capped at
`max_paths`); per left path `push` + assert its `decls`/`constraints`/`return_constraint`; per
right path `push` + assert that; then `check_pair`; `pop`; `pop`.

**`check_pair`:**
- if `check_right` (default): `check-sat` — `Unsat` ⇒ `Verdict::Unreachable`, skip the goal.
- `push`; assert `emit_claim_goal_negated`; `check-sat` — `Unsat` ⇒ `Verified`, `Sat` ⇒
  `GoalFails` + `get_model` → `models/<id>.smt2`, `Unknown` ⇒ `Inconclusive` (+ model if
  obtainable); `pop`.

**Branch pruning — what `--check-left` / `--no-check-right` actually do.** Story 05's executor has
no branch-point callback, so the finest pruning available is *per path* — which is exactly the
vacuity check the overview already mandates at every terminal pair. Therefore:

- **Vacuity always runs by default** and is what distinguishes `Unreachable` from `Verified`.
- `--check-left` adds a per-left-path `check-sat` after asserting the left encoding; `Unsat` ⇒
  the left path is recorded (`reachable: false`) and its right subtree is not explored. Changes
  no verdict (a pruned left path's pairs were all `Unreachable`). Verified in
  `check_left_prunes_abort_paths_without_changing_verdicts` and by hand on `kem-dem` PKGEN
  (2 left paths → 1 pruned, 6 right → 3, verdicts unchanged).
- `--no-check-right` **skips the vacuity `check-sat`** and runs the goal check on every right
  path. It never adds a `GOAL FAILS` (an `unsat` context can't make `(not goal)` `sat`); it only
  makes unreachable pairs fall through to `Verified` instead of `Unreachable`. Documented in
  `--help` and the module docs as a diagnostic escape hatch, not the recommended mode.

**`--timeout`** → `Cvc5LibBackend::new(true, timeout)` **and** `solver.set_option("tlimit-per",…)`.
A timed-out `check-sat` returns `Unknown` ⇒ explored, never pruned, never `Verified`. On
`kem-dem` PKENC `same-output`, `--timeout 1` turns the two real goal checks into `Inconclusive`
(the 94 vacuity-unsat pairs become `Verified` because vacuity also times out — that is expected:
we can no longer prove them unreachable, but the claim still holds on them).

**`--max-paths`** counts left paths + right paths per left path; on exceeding it, `partial = true`,
exploration stops, all artifacts are still written, `is_ok()` is false (exit non-zero).

**Push/pop discipline:** every `push` has a matching `pop` on the normal path; the `max_paths`
break pops what it opened before returning. On a solver *error* the run aborts and the solver is
dropped, so an unbalanced stack does not matter.

## 5. Artifacts written

Under `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/` (or `--out`):

- `transcript.smt2` — every command incl. `(push 1)`/`(pop 1)`/`(check-sat)`/`(get-model)`,
  teed by story 01's transcript writer. **Replays coherently**: verified with system
  `cvc5 --incremental` on the PKGEN run — 7 `check-sat` → 1 `sat` + 6 `unsat`, matching the
  driver's own verdicts (1 reachable pair, 5 unreachable, 1 verified).
- `inlined.txt` — `render::side_by_side` of the two listings, independent line numbers.
- `models/<path-id>.smt2` — one per `GoalFails` / `Inconclusive`.
- stdout: `render_tree` (the §4.5 format).

The base frame is **not** stored on `DebugRun`; it is the head of `transcript.smt2` up to the
first `(push 1)`. Each `LeftPath`/`RightPath` carries `smt: Vec<String>` = its own asserted lines.

## 6. Acceptance criteria — status

All met. Notable hand-verification on `example-projects/kem-dem/kem-dem-cca-ssp` proofstep 0:

| oracle / claim | default | notes |
|---|---|---|
| PKGEN / same-output | 2 left, 6 right; 1 verified, 5 unreachable | matches `prove` (exit 0) |
| PKENC / {same-output, equal-aborts, invariant} | 6 left, 96 right; 0 GOAL FAILS | ~2.5 s |
| PKDEC / {same-output, equal-aborts, invariant} | 5 left, 65 right; 0 GOAL FAILS | ~1 s |
| PKENC / same-output, **invariant weakened** (drop `left.pk = right.pk` conjunct) | **2 GOAL FAILS** with `models/2.8.smt2`, `models/4.9.smt2` and full readable paths | restore → all green again |
| PKENC / lemma-kem-correctness | "claim is admitted — nothing to check", exit 0 | |

The high `unreachable` counts (94/96 for PKENC) are correct: without branch-level pruning every
left syntactic path is paired with every right one, and most pairs are genuinely contradictory
(e.g. left `assert-holds` vs. right `assert-fails` on a related condition). The vacuity check
catches them. `--check-left` tightens this; a real branch-hooked executor would tighten it
further (story-05 follow-up, see §8).

## 7. Tests

`src/debug/driver.rs` `mod tests` (`#[cfg(all(test, feature = "cvc5-lib"))]`):

| test | fixture | checks |
|---|---|---|
| `per_path_dsa_agrees_with_the_oracle_function` | hello-world | the story-05 consistency check — per path `<return> = <oracle-fn>` is `unsat` to negate |
| `hello_world_same_output_is_all_green` | hello-world | end-to-end; `is_ok`; transcript has `(check-sat)`/`(push 1)`/`(pop 1)` |
| `kem_dem_pkgen_same_output_all_green` | kem-dem PKGEN | primary target; `goal_fails == 0`, `is_ok`, `unreachable > 0` (the verdict distinction is exercised) |
| `tiny_timeout_yields_inconclusive_never_a_false_pass` | kem-dem PKENC, `--timeout 1` | `inconclusive > 0`, `goal_fails == 0`, `!is_ok` |
| `no_check_right_keeps_the_same_goal_fails_set` | kem-dem PKGEN | `goal_fails` identical, `right_paths` ≥, `unreachable` ≤ |
| `check_left_prunes_abort_paths_without_changing_verdicts` | simple-KEM TestSender | `left_pruned > 0` under `no-abort`, no verdict change |
| `max_paths_stops_early_and_flags_partial` | simple-KEM TestSender, `--max-paths 1` | `partial`, `!is_ok` |

`src/debug/render.rs`: `columns_are_numbered_independently_and_aligned` (default build).

The kem-dem tests add ~8 s to `cargo test --features cvc5-lib`. `4WHS` / `yao` are never touched.

## 8. Notes for follow-up

- **Real branch-level pruning** needs a branch-point callback in story 05's `execute_streaming`
  (out of scope here — story 05 explicitly ships terminal-only streaming). With it, the driver
  could prune a shared branch prefix once instead of re-deriving `unsat` for every full path, and
  the `unreachable` counts would drop sharply. The current per-path vacuity is sound but chatty
  (~1 `check-sat` per pair).
- **`GameIdentifier::Const` / table-index consts in oracle expressions** — see §3, not handled,
  nothing hits it yet.
- **`cvc5lib.rs` `check_sat`** now parses `unknown (REASON)`. If story 01's other consumers care
  about the reason string, it is discarded here.
- **`--path` eager-eval bug**: `prove`/`proofsteps`/`latex` all do
  `p.path.unwrap_or(find_project_root()?)`, which runs (and can fail on) `find_project_root` even
  when `--path` is given. `debug` uses a `match` instead. The others are unchanged (out of scope).
- `DebugRun` is not yet `Serialize` — story 07 adds it.
- Disk on the dev machine is ~97 % full; `rm -rf target/debug/incremental` reclaims ~2 GB, and
  `cargo clean -p cvc5-sys` forces a bindgen rebuild if `target/debug/build/cvc5-sys-*/out` is
  ever deleted.

## 9. Commit message

```
Story 06: `domino debug` — solver-guided symbolic-execution debugger

Adds `domino debug --proof --proofstep --oracle --claim`, behind the
`cvc5-lib` feature. It runs the debug transform pipeline, inlines the
oracle for both game instances, symbolically executes the left oracle to
every terminal (story 05), and for each left terminal explores the right
oracle, asking cvc5 at every terminal pair whether the pair is reachable
(vacuity) and whether the claim goal holds. Failures are reported pinned
to a concrete execution path on both sides, with a model.

Driver in `src/debug/driver.rs` (generic over `SmtSolverBackend`, no cvc5
dependency of its own): base frame at solver level 0, then a push/pop tree
mirroring left paths × right paths. `--check-left` prunes unreachable left
paths; `--no-check-right` skips the vacuity check; `--timeout` maps to
cvc5 `tlimit-per` (a timeout is explored, never pruned, never verified);
`--max-paths` bounds exploration. Verdicts: Verified / Unreachable /
GoalFails{model} / Inconclusive{model}. Artifacts: transcript.smt2,
inlined.txt, models/<id>.smt2, and a text tree on stdout.

Two transforms of the theorem: EquivalenceTransform (treeified) for the
EquivalenceContext base frame — emit_game_definitions needs treeify — and
DebugTransform (no treeify) for the executor. They agree because samplify
runs before treeify; a per-path consistency check against the monolithic
oracle function is a test.

Also:
- src/debug/exec.rs: seed package consts referenced in oracle expressions
  into the symbolic store (`(<pkg-consts-…> (<pkgconsts-…> <<game-consts-…>>))`),
  a story-05 gap — `subst` used to emit them as undeclared bare atoms.
- EquivalenceContext::generate_game_or_package_invariant_claims lifted out
  of EquivalenceSmtDriver so the debug driver can enumerate the same claim
  set; verify_fn.rs delegates to it (no behaviour change).
- cvc5lib.rs: accept `unknown (TIMEOUT)` from check-sat.

cargo test --workspace and --workspace --features cvc5-lib both pass;
clippy clean; `domino prove` output unchanged.

Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01BrBZJz8hq9fqSkecgKfM6H
```
