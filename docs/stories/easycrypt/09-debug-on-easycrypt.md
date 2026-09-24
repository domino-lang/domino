# Story 09 — `domino debug --easycrypt`

> **SUPERSEDED — do not implement.** The second design session (2026-09-23, owner requirement
> `docs/easycrypt-interaction-and-branching.md`) replaced this story's approach, which ran the
> sequential left-then-right exploration on the EasyCrypt listing. `domino debug --easycrypt` now
> means **lockstep execution**:
>
> - `22-plumbing-decision-points.md` — the IR keeps plumbing branches;
> - `23-lockstep-execution.md` — the engine, the CLI, both claims and stuck points;
> - `24-joint-tree-viewer.md` — the HTML.
>
> What survives from this story:
>
> - its §2.2 facts about `inline_oracle_ec` and the pairing with the Domino game instance;
> - its correctness idea, that the EasyCrypt run must agree with a Domino run. That check is now
>   the one-directional consistency test in story 23 §4.
>
> The body is kept for history.

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 08 (lowering + EasyCrypt listings).
**Blocks:** nothing. Last story of the epic.

---

## 1. Why this story exists

The owner's first version of the debugger-on-EasyCrypt is deliberately modest:

> In this first version, let's just run the debugger on the EasyCrypt code we have in our data
> structures and display the user the verified and pruned paths as we do now but just on inlined
> easycrypt code we generate instead of inlined Domino code.

So: no new analysis, no tactic generation. The existing exploration, verdicts, pruning, summary and
HTML viewer, driven by the EasyCrypt listing from story 08.

## 2. Inherited from earlier stories

### 2.1 The debugger driver (`src/debug/driver.rs`, epic `docs/stories/00-overview.md`)

```rust
pub const TRACE_SCHEMA: u32 = 8;
pub struct DebugOptions { … }
pub enum DebugError { … }
pub struct DebugRun { schema, … }
pub struct LeftPath { … }  pub struct RightPath { … }  pub struct PrunedBranch { … }
pub struct SiteView { … }  pub struct StepView { … }   pub struct TerminalView { … }
pub enum Verdict { … }     pub struct Summary { … }    pub enum StopReason { … }
pub fn run_debug_command<P, B>(…) -> Result<…, DebugError>;
pub fn render_tree(run: &DebugRun) -> String;
```

Outputs live under `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`: `index.html`,
`inlined.txt`, `trace.json`, `summary.txt`, per-failure models and an `smt/` tree. Story 17 put the
concise report on stdout and the per-path tree in `summary.txt`; story 16 paints executed lines.

### 2.2 From story 08

`inline_oracle_ec`, the provenance rule (state places and expressions are the **Domino** ones; the
listing text is EasyCrypt), the elimination of `abort_flag`/`ec_result`, and the fact that
`treeify` makes the EasyCrypt listing have more syntactic paths than the Domino one.

**Corrected by the story 08 session — read `08-ec-ir-lowering-IMPLEMENTATION-REPORT.md` first.**
The last clause above, and every mention of `treeify` duplication in this file (§3.3 "modulo the
path multiplicity `treeify` introduces", §6 "Path explosion"), is stale: since story 16 the export
pipeline is `EasyCryptTransform` (`easycryptify`), which never duplicates a statement. The facts
that replace it:

- `pub fn inline_oracle_ec(game_inst: &GameInstance, oracle_name: &str) -> Result<InlinedOracle,
  EcExportError>` in `src/writers/easycrypt/lower.rs`. `game_inst` must come from
  `EasyCryptTransform`. `render_side_by_side_easycrypt` in `src/debug/render.rs` shows how.
- **Pair the IR with the Domino game instance.** Run the executor with the `DebugTransform` game
  instance and its `sample_info`, exactly as for a Domino listing — not the easycryptified one
  (whose signatures are `Maybe(T)`). The state places, sample ids and entry-frame `Return` values
  are the Domino ones, and `InlinedOracle::return_type`/`args`/`entry_pkg_inst` equal the Domino
  listing's. `no_path_reads_an_unbound_local_and_the_domino_game_instance_pairs_with_it` runs this
  pairing (no solver).
- **The EasyCrypt listing still has more syntactic paths, for a different reason:** each inlined
  call that can return adds one structurally present but infeasible child — the caller's
  `if (!(ec_rN = None))` else side, reachable only if the callee returned `None` without aborting.
  kem-dem `PKENC`: 12 vs 6 (`Game_MON_CCA_PKE`), 31 vs 16 (`Game_MOD_CCA_PKE_Real_KEM`). Pruning
  should remove every one. A *feasible* extra path would be a lowering bug.
- **Story 16 §8's warning (infeasible paths reading unassigned locals, illegal `<pkg#N::x>`
  symbols) does not arise for this IR:** every point that sets `ec_done` is lowered to a terminal,
  so an `if (!ec_done)` body is reached only on paths that assigned what it reads. The test above
  checks that no path mentions an unbound frame-local.
- `frame_lines` for an EasyCrypt call is `(call line, "ec_rN <- ec_result…;" line)`; there are no
  braces. `then_lines`/`else_lines`/`arg_lines` are as in `ir.rs`. The unlabelled rows (the `var`
  block, `ec_result <- None;`, `ec_done <- …` plumbing, the `if (!ec_done) {`/`}` guard, the
  router's `if (!abort_flag) {` and the call comment) are never painted, since painting is
  label-driven; decide whether that is acceptable for the viewer.

## 3. Work to do

### 3.1 The flag

Add `--easycrypt` to `Commands::Debug` (`crates/domino/src/cli.rs`). With it:

- the left and right `InlinedOracle`s come from `inline_oracle_ec` instead of `inline_oracle`;
- **everything else is unchanged** — the base frame, assumptions, claim goal, vacuity check,
  pruning, timeouts, `--max-paths`, `Ctrl-C`, progress, SMT file output, `trace.json`, HTML.

Because the IR denotes the same places and expressions (story 08 §3.2), the existing
`EquivalenceContext` frame and claim machinery apply without modification. If that turns out to be
false for some construct, **stop and report it** rather than special-casing the encoder.

### 3.2 Output changes

- `inlined.txt` and the HTML listings show EasyCrypt code; the header of each says so
  (`listing: EasyCrypt` vs `listing: Domino`), as does `summary.txt` and the stdout report.
- `trace.json` gains one field recording which listing was used, e.g.
  `"listing": "easycrypt" | "domino"`. Bump `TRACE_SCHEMA` to **9** and record it.
- The output directory gains a suffix so the two runs don't overwrite each other:
  `…/<claim>/` for Domino and `…/<claim>-ec/` for EasyCrypt. Record the exact choice.

### 3.3 The correctness signal

The two listings describe the same game, so for a given proofstep/oracle/claim the **verdict
summary must agree**: same set of `goal fails` / `verified` / `unreachable` / `inconclusive`
outcomes, modulo the path multiplicity `treeify` introduces. Add an integration test on
`kem-dem` `PKENC` `same-output` that runs both and asserts the aggregate verdict matches (e.g. both
find zero failures, or both find failures). A mismatch is a bug in the lowering, not something to
paper over in the report.

## 4. Acceptance criteria

- [ ] `domino debug --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim
      same-output` completes on `example-projects/kem-dem/kem-dem-cca-ssp` and writes the full
      artifact set, with EasyCrypt code in `inlined.txt` and in both HTML listings.
- [ ] The same command on `example-projects/hello-world` (`UsefulOracle`) works end to end.
- [ ] Verdict aggregate matches the Domino-listing run for `kem-dem` `PKENC` `same-output` and for
      `PKDEC` (which has abort paths); the path counts may differ and the report says by how much.
- [ ] Executed-line painting, pruned-branch cut lines, the collapsible panes and the path tree all
      work against the EasyCrypt listing (story 16's rules are listing-agnostic — verify, don't
      assume).
- [ ] `trace.json` carries the listing field; `TRACE_SCHEMA` is 9; an unchanged project produces
      byte-identical `trace.json` and `index.html` across two runs.
- [ ] Without `--easycrypt`, every output is byte-identical to today.
- [ ] `cargo build/test/clippy --workspace` clean, including `--features cvc5-lib`.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
D=$PWD/target/debug/domino

cd example-projects/kem-dem/kem-dem-cca-ssp
$D debug --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
$D debug             --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
# compare the two concise stdout reports: verdict aggregates must agree

open _build/debug/*/*/PKENC/same-output-ec/index.html
```

> **Never** run `debug` against `example-projects/4WHS` or `example-projects/yao`. For 4WHS, use
> `domino easycrypt` (allowed — no solver) and read the generated files.

## 6. Notes / risks

- **Path explosion.** `treeify` duplication multiplies EasyCrypt paths. `--max-paths` and `Ctrl-C`
  already exist; if `PKENC` becomes unpleasantly slow, say so in the report with numbers rather
  than adding a new limiter.
- **Don't rewrite the encoder.** If a lowered construct does not encode, that is story 08's
  provenance rule leaking — fix it there.
- **No tactic generation.** Turning paths into `sp`/`rcondt`/`match` scripts is the obvious next
  epic; it is explicitly not this story. Note ideas under "Notes for follow-up".
- **The HTML is a Rust raw string literal** (`const TEMPLATE: &str = r##"…"##`) — keep the `r##`
  delimiters.

## 7. State handed to the next story

Record in `09-…-IMPLEMENTATION-REPORT.md`: the flag, the output directory convention, `TRACE_SCHEMA`
9 and the new trace field, the verdict-agreement results and path-count comparison for `kem-dem`
`PKENC`/`PKDEC`, run times, and a list of what a future tactic-generation epic would need from the
trace.
