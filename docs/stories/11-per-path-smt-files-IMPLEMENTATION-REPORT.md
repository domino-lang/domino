# Story 11 — Implementation report: per-path SMT files instead of one huge transcript

**Status:** done, uncommitted. Branch `amir/symbolic-execution-debugger`.
**Builds on:** stories 06 (`src/debug/driver.rs`), 07 (`report.rs` / `trace.json`), 09
(incremental flush / out-dir layout), 10 (`count_terminals`, `TRACE_SCHEMA = 3`).
**Blocks / feeds:** story 13 (renders the same negated goal — see §4), story 14 (calls
`SmtWriter` from worker threads — it is `Send + Sync` and stateless apart from `root`/`mode`).

`TRACE_SCHEMA` went **3 → 4.** Whichever of 12 / 13 lands next bumps 4 → 5.

---

## 1. What shipped

| File | Change |
|---|---|
| `src/debug/smtout.rs` | **new** module. `SmtOut` (`none` / `failures` / `all` / `deltas`, kebab-case `Serialize`), `SmtWriter { root, mode, meta, base_body }` with `new` / `write_left` / `write_pair`. `Send + Sync`, only creates dirs and truncate-writes files. |
| `src/debug/mod.rs` | `pub mod smtout;` |
| `src/debug/driver.rs` | `DebugOptions` gained `smt_out: SmtOut` (default `Failures`) + `transcript: bool` (default `false`). `OptionsView` mirrors both (`smt`, `transcript`). `TRACE_SCHEMA = 4`. The negated claim goal is **hoisted**: computed once in `run_debug_command` as a local `goal_negated: SmtExpr` + `goal_smt: String`, threaded down; `check_pair` takes `&SmtExpr` instead of re-deriving from `eqctx`/`claim`/`oracle` per pair. Solver is built with `new_smtsolver_with_transcript` only under `--transcript`, else `new_smtsolver`. `SmtWriter` constructed right after `base_frame_smt` is rendered; `write_left` per explored left path, `write_pair` per explored right path (in the `on_right` closure). `--smt all` prints a one-line stderr size warning when `left_total × right_total > 50`. |
| `src/debug/report.rs` | `synthetic_run` test fixture carries the two new `OptionsView` fields; schema asserts 3 → 4; viewer header renders `smt: <mode>` and `transcript: on/off` chips. |
| `crates/domino/src/cli.rs` | `SmtOutArg` (`clap::ValueEnum`, same pattern as `ProgressMode`); `Debug` gained `--smt <none\|failures\|all\|deltas>` (default `failures`) and `--transcript` (flag). |
| `crates/domino/src/main.rs` | maps `SmtOutArg → SmtOut`, sets both opts; after the tree prints `smt: <out>/smt/` (unless `none`) and `transcript: <out>/transcript.smt2` (only with `--transcript`). |
| `docs/stories/07-…md` | file-layout note: `smt/` is the per-path artifact, `transcript.smt2` is opt-in. |

Verdicts, path counts and solver-call counts are unchanged — this story only writes files and
moves one `emit_claim_goal_negated` call earlier.

## 2. The `smt/` layout (final)

```
smt/
  base.smt2            preamble + the base frame (declarations, game defs, invariants, claim assumptions)
  <L>/
    left.smt2          left path #<L>'s own decls / constraints / return constraint — always a delta
    <R>.smt2           pair #<L>.<R>
```

`<L>` / `<R>` are **the numeric ids `trace.json` / the HTML show**: left path `#3` → `smt/3/`,
right path `#3.7` → `smt/3/7.smt2` (`<R>` is `rid.rsplit('.').next()`). Pinned by
`smt_tree_ids_match_the_trace`.

### `base.smt2` preamble

`domino debug`'s lib backend sets solver options through the API, not the SMT text, so a bare
`cvc5 smt/3/7.smt2` would get neither. `SmtWriter::new` prepends, when the base frame does not
already carry them:

```
(set-option :incremental true)      ; the pair file has push/pop + two check-sats
(set-option :produce-models true)   ; for (get-model)
```

**Both are needed** — without `:incremental` cvc5 rejects the `(push 1)` around the goal
("cannot push when not solving incrementally"). The story's §6 note only mentioned
`produce-models`; `:incremental` was found by actually running the emitted file.

### Self-contained pair file (`failures` / `all`)

Header comment (theorem/proofstep/games, oracle/claim, both path step-summaries, the recorded
verdict, a `run:` line and what the two `check-sat`s mean), then:

```
; ---- base frame ----      <base.smt2 body, verbatim>
; ---- left path #<L> ----  <left.smt joined by \n>
; ---- right path #<L>.<R> ----  <right.smt joined by \n>
; ---- vacuity ----         (check-sat)
; ---- negated goal ----    (push 1) <goal_smt> (check-sat) (get-model) (pop 1)
```

First `(check-sat)` = vacuity (`unsat` ⇒ pair unreachable); second = negated goal (`sat` ⇒ claim
fails). `(get-model)` is **unconditional** (matches the story template); on a `verified` pair the
second `check-sat` is `unsat` and cvc5 prints a benign `(error "cannot get model unless after a
SAT or UNKNOWN response.")` and continues — only relevant under `--smt all`, since `failures`
never writes verified-pair files.

### `deltas` mode

Pair file carries **neither** the base frame **nor** the left path — only the right path plus the
vacuity + goal block. Its `run:` line is the reassembly recipe
`cat smt/base.smt2 smt/<L>/left.smt2 smt/<L>/<R>.smt2 | cvc5 --lang smt2 -`. `left.smt2` is a
delta in every mode (asserted `!left.contains("set-logic")` in a test).

### Coverage predicate (`SmtOut::covers`)

| mode | `base.smt2` | `left.smt2` | pair `.smt2` |
|---|---|---|---|
| `none` | — | — | — |
| `failures` (default) | ✓ | ✓ (every explored left path) | only `goal-fails` / `inconclusive` |
| `all` | ✓ | ✓ | every explored pair (self-contained) |
| `deltas` | ✓ | ✓ | every explored pair (delta only) |

## 3. Goal SMT — passed as a local, not on `DebugRun`

Story 13's `DebugRun.goal_smt` did **not** land here. `emit_claim_goal_negated(&claim, oracle)`
is computed once in `run_debug_command` next to `base_frame` and threaded as
`goal_negated: &SmtExpr` (for `check_pair`, `.clone()` onto the solver) and `goal_smt: &str` (for
`SmtWriter::write_pair`). `check_pair` lost its `eqctx` / `claim` / `oracle` params;
`handle_left_path` / `handle_right_path` lost `eqctx` / `claim` / `oracle` too. **Story 13:** when
you add `DebugRun.goal_smt`, set it from this same local and drop the `goal_smt` thread-through
(keep `goal_negated` for the solver, or store both).

## 4. `TRACE_SCHEMA` + `OptionsView`

`pub const TRACE_SCHEMA: u32 = 4;` — two new `OptionsView` fields:

```rust
pub smt: SmtOut,       // "none" | "failures" | "all" | "deltas"   (kebab-case)
pub transcript: bool,
```

`trace.json` for a default run now has `"options": { …, "smt": "failures", "transcript": false }`.
The viewer reads `o.smt == null ? "failures" : o.smt` and `o.transcript ? "on" : "off"`
defensively, so a schema-3 trace still opens.

## 5. Measured — `kem-dem` `kem-dem-cca-ssp`, proofstep 0, `PKENC` / `same-output`

`base.smt2` is **540 KB** here (the story's "~3.5 MB" estimate was for a different project / the
un-narrowed frame). With the default pruning `PKENC` reaches 4 left paths and **2** surviving
right pairs, so:

| mode | `smt/` total | files | notes |
|---|---|---|---|
| `failures` (green run) | 616 KB | 5 | `base.smt2` + 4 × `left.smt2`, **no pair files** (all verified) |
| `deltas` | 672 KB | 7 | + 2 tiny pair deltas (~28 KB each) |
| `all` | 1.8 MB | 7 | + 2 self-contained pair files (~640 KB each) |
| `--transcript` | `transcript.smt2` 652 KB | — | absent without the flag |

`--smt all` estimate on the **un-pruned** tree (96 pairs): ≈ 96 × 620 KB ≈ **58 MB**. The
`> 50`-pair stderr warning fires there (`6 × 16 = 96`).

### Killer test — `cvc5` binary on an emitted **failure** file

Weakened `theorem/invariant.smt2` (dropped `(= left.MON_CCA_PKE.pk right.MOD_CCA_PKE.pk
right.KEM.pk)`), reran `domino debug … --oracle PKENC --claim same-output` (default `--smt
failures`): 2 `GOAL FAILS`, files `smt/1/1.smt2` and `smt/2/1.smt2` written.

```
$ cvc5 --lang smt2 .../smt/1/1.smt2
sat            # vacuity — pair reachable
sat            # negated goal — claim FAILS   (matches trace.json verdict "goal-fails")
( … model … )
```

`deltas` reassembly on the same failing pair:

```
$ cat smt/base.smt2 smt/1/left.smt2 smt/1/1.smt2 | cvc5 --lang smt2 -
sat
sat
```

`all` on the green `PKGEN` run: a `verified` pair file gives `sat` then `unsat` (+ the benign
get-model error line). Invariant restored afterwards (`git diff --stat` clean).

## 6. Tests

`--features cvc5-lib`, `src/debug/driver.rs` (`#[cfg(all(test, feature = "cvc5-lib"))]`):

- `hello_world_same_output_is_all_green` — reworked: asserts `transcript.smt2` **absent** by
  default, `smt/base.smt2` + `smt/<L>/left.smt2` present.
- `transcript_flag_re_enables_the_monolithic_transcript` — `--transcript` ⇒ the story-06
  assertions on `transcript.smt2` still hold.
- `smt_none_writes_no_smt_directory`.
- `emitted_pair_file_reproduces_the_recorded_verdict` — re-feeds `base.smt2 ++ lp.smt ++ rp.smt`
  to a fresh lib solver, checks vacuity + goal answers match `rp.verdict` (this is the
  self-containment / "`reported_*` really are prefixes" property).
- `smt_tree_ids_match_the_trace` — a file exists for every left path and every covered pair, ids
  matching `trace.json`.
- `smt_failures_covers_only_failing_pairs` — a fully-green run gets no pair files.
- `smt_deltas_files_are_headerless_and_reassemble` — pair file has no `set-logic`, has the `cat`
  recipe; reassembly re-derives the vacuity answer.
- `emitted_pair_file_runs_under_the_cvc5_binary` — **`#[ignore]`** (needs `cvc5` on `PATH`):
  shells out to the real binary, second `check-sat` matches the verdict. Passes.
- `report::tests` schema asserts bumped 3 → 4; `synthetic_run` carries the new fields.

```
cargo build   --workspace                       # clean, no warnings
cargo build   --workspace --features cvc5-lib    # clean, no warnings
cargo clippy  --workspace [--features cvc5-lib]  # clean
cargo test    --workspace                        # 128 + 2 pass, 4 ignored (pre-existing)
cargo test    --workspace --features cvc5-lib    # 148 + 2 pass, 5 ignored (4 pre-existing + this story's)
```

`--features cvc5-lib` test link is memory-heavy: `CARGO_BUILD_JOBS=2 cargo test -j2`.

## 7. State handed to the next story

- **`smt/` layout**: `smt/base.smt2`, `smt/<L>/left.smt2`, `smt/<L>/<R>.smt2`; `<L>`/`<R>` are
  the HTML/`trace.json` numeric ids. Header format and section markers: see §2.
- **`SmtOut`** variants `None | Failures | All | Deltas`; default `Failures`. `SmtWriter` is
  `Send + Sync`, stateless apart from `root` / `mode` / `meta` / `base_body` — **story 14 calls
  `write_left` / `write_pair` from worker threads directly, no channel needed.**
- **Goal SMT** is a **local** in `run_debug_command` (`goal_negated: SmtExpr`, `goal_smt:
  String`), **not** on `DebugRun`. Story 13 adds `DebugRun.goal_smt` from this same value and can
  drop the `goal_smt: &str` thread-through.
- **`TRACE_SCHEMA = 4`.** New `OptionsView` fields: `smt: SmtOut` (kebab-case), `transcript:
  bool`.
- `transcript.smt2` is opt-in (`--transcript`); the story-06 transcript test moved to
  `transcript_flag_re_enables_the_monolithic_transcript`.
- The base-frame preamble adds `:incremental` **and** `:produce-models` when absent — a bare
  `cvc5 <file>` needs both. Do not remove `:incremental` thinking `produce-models` alone
  suffices.
- Story 12 still needs to replace `DebugRun.partial: bool` with `StopReason` (unchanged by this
  story — the `smt/` files are written incrementally as pairs finish, so a partial run already
  leaves a usable `smt/` tree).
