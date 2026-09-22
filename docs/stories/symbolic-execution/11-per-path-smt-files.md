# Story 11 — Per-path SMT files instead of one huge transcript

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 06 (`src/debug/driver.rs`), story 09 (incremental flush / out-dir layout).
**Interacts with:** story 13 (the HTML shows the same goal assertion this story writes into the
files) and story 14 (parallel workers write these files from several threads).
**Blocks:** nothing.

---

## 1. Why this story exists

`run_debug_command` opens `transcript.smt2` (`driver.rs:544`) and hands it to
`backend.new_smtsolver_with_transcript(...)`, so **every** byte the driver ever sends to cvc5 —
the ~3.5 MB base frame once, then every push/pop, every path delta and every `check-sat` for
every one of ~200 pairs — lands in a single file. It is enormous, it is write-ordered rather than
path-ordered, and it is nearly useless for the thing you actually want: *"give me the exact query
for pair `#3.7` so I can run cvc5 on it myself."*

### What the owner asked for

> Instead of a huge transcript file, you output the left path, and right paths, and full assertion
> (including left and right paths so one can run cvc5 on it actually). You can use directories to
> organize it. There could be an `smt` directory under which comes the numeric left path id (the
> same you assign in html) and then inside that you can put left path. Then inside that directory
> could be smt files for numeric right path ids. Allow the user to decide an option whether this
> transcript is generated or not. But anyway, you didn't need to generate a huge smt transcript
> file.

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **Layout** | `smt/base.smt2`, `smt/<L>/left.smt2`, `smt/<L>/<R>.smt2` — `<L>` and `<R>` are the **numeric ids the HTML already shows** (left path `#3` → `smt/3/`, right path `#3.7` → `smt/3/7.smt2`). |
| **Pair files are self-contained** | `cvc5 smt/3/7.smt2` runs, with no concatenation and no other file, and reproduces that pair's verdict. That is the whole point of the story. |
| **Coverage is a flag** | `--smt <none\|failures\|all\|deltas>`, default **`failures`** — self-contained files for the pairs you care about, without writing the base frame ~200 times. |
| **The monolithic transcript** | Off by default. `--transcript` re-enables `transcript.smt2` for debugging the driver itself. |
| **Verdicts** | Unchanged. This story only writes files. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 What the driver asserts, in order (`src/debug/driver.rs`)

1. `base_frame(&eqctx, oracle, &claim)` (`:586`) — base declarations, theorem paramfuncs, game
   definitions, constant declarations for this oracle, auto-randomness, invariant, return-value
   helpers, randomness-mapping condition, and the **claim assumptions** asserted positively. Its
   rendered text is already kept on the run as `DebugRun.base_frame_smt` (`:165`), because
   `index.html` is self-contained.
2. Per left path, at its terminal: `write_path_delta` (`:954`) writes
   `path.decls[reported_decls..]`, `path.constraints[reported_constraints..]`, then
   `path.return_constraint`. The `reported_*` watermarks exist because `SolverPruner` (`:980`)
   already asserted the branch prefix incrementally. **The full path is always
   `decls ++ constraints ++ return_constraint`** — `render_path_smt` (`:1211`) renders exactly
   that, and it is what `LeftPath.smt` / `RightPath.smt` already carry (`:288`, `:306`).
3. Per right path, at its terminal: the same, on top of the left path.
4. `check_pair` (`:920`): an unconditional **vacuity** `check-sat`, then `push`,
   `eqctx.emit_claim_goal_negated(claim, oracle)` (`:935`), `check-sat`, model on `sat`/`unknown`,
   `pop`.

So a self-contained pair query is exactly:

```
base_frame  ++  left.decls ++ left.constraints ++ left.return_constraint
            ++  right.decls ++ right.constraints ++ right.return_constraint
            ++  (check-sat)                     ; vacuity
            ++  (push 1) (assert (not <goal>)) (check-sat) (get-model) (pop 1)
```

Nothing else is on the solver stack — the `SolverPruner` prefix is a **prefix of the path's own
decls/constraints**, never anything extra. Assert that in a test (§4).

### 2.2 Output directory today

`out_dir` defaults to `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/` (`driver.rs:498`)
and currently holds `transcript.smt2`, `inlined.txt`, `trace.json`, `index.html` and
`models/<rid>.smt2` (written by `write_model`, `:1148`).

### 2.3 Options plumbing

`DebugOptions` (`:85`) → `OptionsView` (`:223`) → `trace.json`; `TRACE_SCHEMA` at `:162` (**3**
after story 10 — if story 10 has not landed, it is `2`; bump by one from whatever you find).
CLI flags live in `crates/domino/src/cli.rs:63` (`struct Debug`) and are mapped in
`crates/domino/src/main.rs:136`.

### 2.4 The test that pins the transcript

`driver.rs:1543-1548` reads `transcript.smt2` back and asserts it contains `(check-sat)`,
`(push 1)` and `(pop 1)`. That test must move to the `--transcript` path (or become a
per-path-file test) — do not just delete the coverage.

## 3. Work to do

### 3.1 New module `src/debug/smtout.rs`

```rust
//! Per-path SMT files (story 11): a `smt/` tree of runnable cvc5 inputs.

/// Which pairs get a self-contained `.smt2` file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SmtOut {
    /// Write nothing.
    None,
    /// Self-contained files for `goal-fails` and `inconclusive` pairs only (default).
    Failures,
    /// Self-contained files for every explored pair. Writes ~one base frame per
    /// pair — for `kem-dem` `PKENC` that is roughly 3.5 MB × 96 ≈ 340 MB.
    All,
    /// `base.smt2` + per-path deltas only. Small; reassemble with
    /// `cat smt/base.smt2 smt/3/left.smt2 smt/3/7.smt2 | cvc5 --lang smt2 -`.
    Deltas,
}

pub struct SmtWriter { root: PathBuf, mode: SmtOut }

impl SmtWriter {
    /// Creates `smt/` and writes `smt/base.smt2` (unless `mode == None`).
    pub fn new(out_dir: &Path, mode: SmtOut, base_frame_smt: &str) -> std::io::Result<Self>;

    /// Writes `smt/<lid>/left.smt2`: the left path's own decls, constraints and
    /// return constraint (never the base frame). Called once per explored left
    /// path, before its right sweep.
    pub fn write_left(&self, lid: &str, left: &LeftPath) -> std::io::Result<()>;

    /// Writes `smt/<lid>/<r>.smt2` for right path `<lid>.<r>` when `mode`
    /// covers `verdict`. `<r>` is the numeric tail of the right id.
    pub fn write_pair(
        &self, lid: &str, rid: &str,
        left: &LeftPath, right: &RightPath, goal_smt: &str,
    ) -> std::io::Result<()>;
}
```

Content of a **self-contained** pair file (`Failures` / `All`):

```smt2
; domino debug — theorem <T>, proofstep <N>, <LeftGame> == <RightGame>
; oracle <O>, claim <C>
; left path #3   L12 then -> L27 return
; right path #3.7  L14 else -> L36 return
; verdict recorded by `domino debug`: goal-fails
;
; run:  cvc5 --lang smt2 <this file>
;   first  (check-sat)  is the vacuity check   — `unsat` means the pair is unreachable
;   second (check-sat)  is the negated goal    — `sat` means the claim FAILS on this pair

; ---- base frame -------------------------------------------------------
<base_frame_smt>

; ---- left path #3 -----------------------------------------------------
<left.smt joined by newlines>

; ---- right path #3.7 --------------------------------------------------
<right.smt joined by newlines>

; ---- vacuity ----------------------------------------------------------
(check-sat)

; ---- negated goal -----------------------------------------------------
(push 1)
<goal_smt>
(check-sat)
(get-model)
(pop 1)
```

In `Deltas` mode the same file is written **without** the base frame and without the left path,
with the header's `run:` line replaced by the `cat … | cvc5` recipe. `left.smt2` is written in
every mode except `None`, always as a delta.

`<goal_smt>` is `eqctx.emit_claim_goal_negated(claim, oracle).to_string()` — hoist that call out
of `check_pair` (`driver.rs:935`) and compute it **once** in `run_debug_command`, next to
`base_frame`; pass it down. (Story 13 puts the same string on `DebugRun` for the viewer; if 13
landed first, reuse `run.goal_smt` instead of re-deriving it.)

### 3.2 Driver wiring — `src/debug/driver.rs`

- `DebugOptions` gains `pub smt_out: SmtOut` (default `SmtOut::Failures`) and
  `pub transcript: bool` (default `false`); mirror both in `OptionsView` and **bump
  `TRACE_SCHEMA`** by one.
- `run_debug_command`: build the solver with `backend.new_smtsolver_with_transcript(file)` only
  when `opts.transcript`; otherwise `backend.new_smtsolver()`. Construct the `SmtWriter` right
  after `base_frame_smt` is rendered.
- `handle_left_path`: after the `LeftPath` view exists and before/after the right sweep, call
  `writer.write_left(lid, &left_view)`.
- `handle_right_path`: after the verdict is known, `writer.write_pair(...)`.
- IO errors surface as `DebugError::Io`, exactly like `report::flush`.
- Update the `transcript.smt2` test at `:1543` to run with `transcript: true`, and add the new
  per-path-file tests (§4).

### 3.3 CLI — `crates/domino/src/cli.rs` / `main.rs`

```rust
/// Which per-path SMT files to write under `<out>/smt/`. `failures` (the
/// default) writes a self-contained, directly runnable `.smt2` for each
/// goal-fails / inconclusive pair; `all` does it for every pair (large — one
/// copy of the base frame per pair); `deltas` writes only `base.smt2` plus the
/// small per-path deltas; `none` writes nothing.
#[clap(long, value_enum, default_value_t = SmtOutArg::Failures)]
pub(crate) smt: SmtOutArg,

/// Also write the raw incremental solver transcript to `transcript.smt2`
/// (large; for debugging `domino debug` itself).
#[clap(long)]
pub(crate) transcript: bool,
```

`SmtOutArg` is a `clap::ValueEnum` in `cli.rs` mapped to `SmtOut` in `main.rs` (same pattern as
`ProgressMode`). After the tree, print `smt: <out_dir>/smt/` when the mode is not `none`.

### 3.4 Docs

Update the "Output" row of `docs/stories/00-overview.md` §3 and the `07-…` story's file-layout
note: `transcript.smt2` is opt-in, `smt/` is the per-path artifact.

## 4. Acceptance criteria

- [ ] `--smt failures` (default) on a **failing** `kem-dem` run (weaken `theorem/invariant.smt2`
      by dropping `left.pk = right.pk`) writes `smt/base.smt2`, `smt/<L>/left.smt2` for every
      explored left path, and `smt/<L>/<R>.smt2` for exactly the goal-fails/inconclusive pairs.
- [ ] **The killer test**: for one such pair, `cvc5 --lang smt2 smt/<L>/<R>.smt2` runs to
      completion and prints `sat` for the second `check-sat` — matching the verdict in
      `trace.json`. Add this as an ignored-by-default integration test *and* a manual step in the
      implementation report with the pasted output.
- [ ] With `--smt all` on `PKGEN` (small), every explored pair has a file, and a `verified` pair's
      file yields `unsat` on the second `check-sat` and a non-`unsat` first `check-sat`.
- [ ] `--smt deltas` writes no base frame into the per-pair files, and
      `cat smt/base.smt2 smt/<L>/left.smt2 smt/<L>/<R>.smt2 | cvc5 --lang smt2 -` reproduces the
      same two answers.
- [ ] `--smt none` writes no `smt/` directory at all.
- [ ] `transcript.smt2` is **absent** unless `--transcript` is passed; with `--transcript` the
      old story-06 assertions on it still hold.
- [ ] Unit test: for a small project, `base_frame ++ left.smt ++ right.smt` is exactly the text
      the driver sent to the solver for that pair (i.e. the `reported_*` watermarks really are
      prefixes and nothing else is on the stack) — compare against a `--transcript` capture.
- [ ] File sizes are reported in the implementation report for `PKENC`: `smt/` under `failures`,
      under `deltas`, and the estimate under `all`.
- [ ] `trace.json` schema bumped; `options.smt` and `options.transcript` present.
- [ ] `cargo build`/`test`/`clippy --workspace` and `--features cvc5-lib` all clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
find $O/smt -type f | head; du -sh $O/smt; ls $O/transcript.smt2 2>&1   # absent

# make it fail, then run the emitted query by hand
git diff --quiet theorem/invariant.smt2 && sed -i.bak '/left.pk = right.pk/d' theorem/invariant.smt2
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
F=$(find $O/smt -name '*.smt2' -path '*/[0-9]*' | head -1); echo $F
cvc5 --lang smt2 "$F"          # expect: <vacuity answer> then sat
mv theorem/invariant.smt2.bak theorem/invariant.smt2

$D debug … --oracle PKGEN --claim same-output --smt all --transcript
$D debug … --oracle PKGEN --claim same-output --smt none
```

Smaller smoke tests first: `test-projects/test-splitinvoke`, `example-projects/hello-world`.

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release`.

## 6. Notes / risks

- **Size.** `--smt all` writes one base frame per pair. Print a one-line stderr warning when
  `all` is combined with a run that explores more than ~50 pairs, and say the size in the docs.
  Do not silently compress or dedupe — a file you have to post-process is not "runnable".
- **`get-model` needs `produce-models`.** The `cvc5-lib` backend sets it (`Cvc5LibBackend::new(true, …)`);
  the emitted file must set it too — take the `(set-option …)` / `(set-logic …)` preamble from
  whatever `base_frame` already contains and, if it does not contain them, emit
  `(set-option :produce-models true)` at the top of the file. Verify by actually running cvc5.
- **Ids must match the HTML.** `smt/3/7.smt2` ⇔ `#3.7` in `index.html` and `render_tree`. A
  mismatch here makes the whole feature untrustworthy; assert it in a test that walks `trace.json`
  and checks a file exists for every covered verdict.
- **Thread-safety.** Keep `SmtWriter` `Send + Sync` and stateless apart from `root`/`mode` (it
  only creates directories and truncate-writes files) — story 14 calls it from worker threads.
- **Do not widen scope.** No zip/tar bundling, no `--smt` filtering by path id, no rewriting
  `models/` (it stays as is).

## 7. State handed to the next story

Record in `docs/stories/11-…-IMPLEMENTATION-REPORT.md`:

- The final `smt/` layout, the exact header format, and the `SmtOut` variants.
- Whether the goal SMT was hoisted onto `DebugRun` (story 13's `goal_smt`) or passed as a local.
- Measured sizes and the pasted `cvc5` run on an emitted failure file.
- The new `TRACE_SCHEMA` value and the two new `OptionsView` fields.
