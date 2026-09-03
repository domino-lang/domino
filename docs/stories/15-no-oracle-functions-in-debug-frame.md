# Story 15 — Drop the oracle function definitions from the debugger's base frame

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 04 (`emit_constant_declarations(Some(o))`), story 05 (the DSA encoding that
replaced the oracle functions), story 06 (`base_frame` in `src/debug/driver.rs`), story 11
(`smt/base.smt2`).
**Blocks:** nothing. Independent of 12, 13 and 14 — but land it **before** 14 if you can: story 14
builds one base frame per worker thread, and this story makes that frame ~4× smaller.

---

## 1. Why this story exists

`domino debug` never evaluates an oracle function. Story 05 replaced

```smt
(assert (= <return-Game_X-PKENC> (<oracle-Game_X-…-PKENC> <state> <consts> <args>)))
```

with a per-path DSA encoding, and story 04 added `emit_constant_declarations(Some("PKENC"))` so
that one constraint is skipped. But the **definitions** of every oracle function of both games are
still emitted at solver level 0, and the return constraints of every *other* exported oracle still
call them. Nothing in the run ever reads either.

Measured on `example-projects/kem-dem/kem-dem-cca-ssp`, `PKENC` / `same-output`
(`_build/debug/…/smt/base.smt2`):

| | lines | bytes |
|---|---:|---:|
| whole base frame | 3826 | 551 354 |
| `(define-fun <oracle-…>)` blocks (28 of them, both games) | 1594 | 400 752 |
| share that is dead weight | **42 %** | **73 %** |

On top of that the frame carries `(assert (= <return-…-PKGEN> (<oracle-…-PKGEN> …)))` and the same
for `PKDEC`, on both sides — four asserts whose only purpose is to pull two more monolithic terms
into every single `check-sat`.

That frame is paid for three times over:

- **the solver** re-processes it at level 0 and carries it through every push/pop pair — one
  vacuity check plus one goal check per terminal pair (96 pairs for `PKENC`);
- **the artifacts** — `DebugRun.base_frame_smt` (`driver.rs:224`) is embedded verbatim in
  `trace.json` (785 KB) and in `index.html` (903 KB), and `--smt all` writes one copy of the frame
  per pair (story 11 measured ≈340 MB for `PKENC`);
- **the pipeline** — `smt_oracle_function_definitions` is the *only* consumer of `treeify` in the
  debug path, so the driver runs the whole transform pipeline **twice** (`EquivalenceTransform`
  for the context, `DebugTransform` for the executor) purely to produce SMT nobody reads.

### What the owner asked for

> Oracle SMT should not be generated for the debugger. The only thing needed is game state
> constants and data types, not oracle functions.

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **What stays** | Every datatype and every constant: `smt_composition_randomness`, package consts / state / **return** datatypes, theorem consts, game consts, game state, both const-mapping function families, and everything `emit_constant_declarations` declares for the debugged oracle. |
| **What goes** | `smt_oracle_function_definitions` (all of it), and the `<return-…>` declare+constrain blocks of every export **other than** the debugged oracle. |
| **Return datatypes stay** | `smt_package_return_definitions` emits `declare-datatype <OracleReturn_…_PKDEC>`; a hand-written lemma can take a `return-right` of that sort (kem-dem does — see §2.5). They are data types, not oracle code. |
| **Escape hatch** | `--with-oracle-functions` restores exactly today's frame (and today's treeified transform). Off by default; it exists so a suspicious verdict can be re-run against the monolithic encoding. |
| **`prove` is untouched** | `verify_fn.rs` keeps emitting the full frame, byte-identical. This story is a *narrowing of the debugger's* frame, not a change to the encoding. |
| **Single transform** | With the flag off, the driver runs `DebugTransform` **once** and builds the `EquivalenceContext` on it. |
| **Verdicts must not move** | Any verdict change on the acceptance projects is a bug in this story, not an accepted consequence. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 The base frame — `src/debug/driver.rs:690`

```rust
fn base_frame<'a>(eqctx: &'a EquivalenceContext<'a>, oracle: &str, claim: &Claim) -> Vec<SmtExpr> {
    let mut base = vec![SmtExpr::Comment(" domino debug — base frame ".to_string())];
    base.extend(eqctx.emit_base_declarations());        // set-logic, Bits/Maybe/Tuple/SampleId hacks
    base.extend(eqctx.emit_theorem_paramfuncs());
    base.extend(eqctx.emit_game_definitions());         // <- datatypes AND oracle functions
    base.extend(eqctx.emit_constant_declarations(Some(oracle)));
    base.extend(eqctx.emit_auto_randomness(oracle));
    base.extend(eqctx.emit_invariant(oracle));
    base.extend(eqctx.emit_return_value_helpers(oracle));
    base.extend(eqctx.emit_randomness_mapping_condition(oracle));
    base.push(SmtExpr::Comment(" claim assumptions ".to_string()));
    base.extend(eqctx.emit_claim_assumptions(claim, oracle));
    base
}
```

The result is written to the solver once, stored in `DebugRun.base_frame_smt`, and re-used by
`SmtWriter` for `smt/base.smt2` and for every self-contained pair file (story 11). Only the two
marked lines change.

### 2.2 The double transform — `src/debug/driver.rs:506`

```rust
let (theorem_eq,  auxs_eq)  = EquivalenceTransform.transform_theorem(theorem)?;  // with treeify
let mut eqctx = EquivalenceContext::new(eq, &theorem_eq, &auxs_eq);
eqctx.load_invariants(project)?;

let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(theorem)?;        // no treeify
```

`transform_game_inst_common` (`src/transforms/theorem_transforms.rs:98`) is shared by both, with
`run_treeify` as the *only* difference, and `treeify` runs **last but one** — after `type_extract`,
`samplify` and `sample_max_counter_extractor`. So `GameInstAux { types, sample_info, max_offsets }`,
the export list, the oracle signatures, every datatype and every constant name are identical
between the two transforms. `treeify` only rewrites statement bodies, and the only thing that
compiles statement bodies is `smt_oracle_function_definitions`.

Today's comment at `:498` says exactly that; when the flag is off it stops being true and must be
rewritten, not deleted.

### 2.3 `emit_game_definitions` — `src/writers/smt/contexts/equivalence/emit.rs:659`

```rust
left_writer.smt_composition_randomness()
    .chain(right_writer.smt_composition_randomness())
    .chain(self.smt_package_const_definitions())
    .chain(self.smt_package_state_definitions())
    .chain(self.smt_theorem_const_definition())
    .chain(self.smt_game_const_definitions())
    .chain(self.smt_game_state_definitions())
    .chain(self.smt_theorem_game_const_mapping_definitions())
    .chain(self.smt_game_pkg_const_mapping_definitions())
    .chain(self.smt_package_return_definitions())
    .chain(self.smt_oracle_function_definitions())   // <- the only entry to drop
```

`smt_oracle_function_definitions` (`:1391`) is the sole caller of
`CompositionSmtWriter::smt_define_nonsplit_oracle_fn`, which is the sole consumer of treeified
bodies in this path.

### 2.4 `emit_constant_declarations` / `build_returns` — `emit.rs:901` and `:1443`

`build_returns` loops over `game_inst.game().exports` and, per export, pushes **nine** entries in
this fixed order:

```
declare <return-G-O>                         ; the OracleReturn datatype value
[ assert (= <return-G-O> (<oracle-…-O> …)) ] ; skipped when skip_return_constraint_for == Some(O)
declare return-value-G-P-O                   ; constrained off <return-G-O>
assert  (= return-value-… (…-return-value-or-abort <return-G-O>))
declare <return-is-abort-G-P-O>
assert  (= <return-is-abort-…> (match return-value-… …))
declare <<game-state-G-new-O>>
assert  (= <<game-state-G-new-O>> (…-game-state <return-G-O>))
```

Story 04's `skip_return_constraint_for: Option<&str>` drops exactly the one bracketed assert, for
the debugged oracle, on both sides. Every other export keeps its full block — that is what still
references the oracle functions.

Nothing in the debug frame reads another export's block: the claim assumptions, the negated goal
and the generated relations all take `<<game-state-G-old>>`, `<return-G-PKENC>`,
`return-value-G-…-PKENC` and the `<arg-G-PKENC-…>` constants. Verified by grepping a real
`smt/base.smt2` for `PKDEC` and `PKGEN` outside their own define/declare blocks: no hits.

Two `#[cfg(test)] mod story04_tests` tests pin this API (`emit.rs:1616`):
`emit_constant_declarations_none_matches_golden` (golden
`testdata/story04/emit_constant_declarations_none.smt2`) and
`skip_return_constraint_drops_exactly_two_asserts`. Both must keep passing — the first
**byte-identically**.

### 2.5 Why the return *datatypes* must stay

`example-projects/kem-dem/kem-dem-cca-ssp/theorem/invariant.smt2:74` defines

```smt
(define-lemma <relation-lemma-kem-correctness-Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-PKDEC>
    (old-state-left old-state-right return-left return-right (ek_ctxt (Tuple2 Bits_kctl Bits_dctl))) …)
```

`emit_invariant("PKENC")` emits the whole file, so this `PKDEC` lemma lands in a `PKENC` run and
its `return-right` parameter is typed with the `PKDEC` `OracleReturn` **sort**. Drop
`smt_package_return_definitions` and cvc5 fails with an unknown sort. Drop only the `PKDEC`
*constants* and nothing breaks — the lemma's parameters are bound, not global.

### 2.6 The cross-check test — `src/debug/driver.rs:1620`

`per_path_dsa_agrees_with_the_oracle_function` builds a full frame by hand (`EquivalenceTransform`
+ `emit_game_definitions()` + `emit_constant_declarations(None)`), asserts the DSA return
constraint negated, and expects `unsat` per left path. It is the only thing in the repo that proves
the per-path encoding agrees with the monolithic one, so it **keeps** the full frame and keeps
running both transforms. Update its comment: it no longer mirrors `run_debug_command`'s split, it
is a *reference* check against the encoding `prove` uses.

### 2.7 Options plumbing

`DebugOptions` (`driver.rs:86`) → `OptionsView` (`:267`, serialised into `trace.json`) →
`crates/domino/src/cli.rs::Debug` → `crates/domino/src/main.rs`. `TRACE_SCHEMA` is **5**
(`driver.rs:172`); adding a field to `OptionsView` is a schema change, so bump by one from whatever
you find and say the number in your report.

## 3. Work to do

### 3.1 `emit.rs` — make the oracle functions optional

```rust
/// Whether `emit_game_definitions` includes the monolithic
/// `(define-fun <oracle-…>)` bodies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OracleFns {
    /// `prove`, and `domino debug --with-oracle-functions`.
    Include,
    /// `domino debug`: datatypes and constants only. The bodies need `treeify`
    /// and the debugger reads them nowhere — it encodes each path itself (story 05).
    Omit,
}

impl<'a> EquivalenceContext<'a> {
    /// Unchanged behaviour: `emit_game_definitions_with(OracleFns::Include)`.
    pub(crate) fn emit_game_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a { … }

    pub(crate) fn emit_game_definitions_with(
        &'a self,
        oracle_fns: OracleFns,
    ) -> impl Iterator<Item = SmtExpr> + 'a { … }
}
```

Keep **one** chain (no copy-paste — the two must never drift); make the last link conditional:

```rust
.chain(
    matches!(oracle_fns, OracleFns::Include)
        .then(|| self.smt_oracle_function_definitions())
        .into_iter()
        .flatten(),
)
```

Everything before it is emitted in both modes, in the same order.

### 3.2 `emit.rs` — `ReturnConsts` replaces `Option<&str>`

```rust
/// Which exports get the `<return-…>` / `return-value-…` / `<return-is-abort-…>` /
/// `<<game-state-…-new-O>>` block of [`build_returns`], and which of them are
/// constrained off the monolithic oracle function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReturnConsts<'a> {
    /// Every export, fully constrained. `prove`. (Old `None`.)
    All,
    /// Every export, but `o`'s `<return-o>` is left unconstrained for the caller
    /// to constrain per path. (Old `Some(o)`.) `domino debug --with-oracle-functions`.
    AllExcept(&'a str),
    /// Only `o`'s block, with `<return-o>` unconstrained — so nothing in the
    /// output names an oracle function. `domino debug` (default).
    Only(&'a str),
}

pub(crate) fn emit_constant_declarations(&self, returns: ReturnConsts<'_>) -> Vec<SmtExpr>;
```

- Thread it through to `build_returns(game_inst, returns)`. `Only(o)` `continue`s the export loop
  for every export whose **adversary-visible** name (`export.name()`, the same string story 04
  compares against — *not* `sig.name`) is not `o`; `AllExcept(o)` behaves exactly as `Some(o)` did.
- `All` must produce byte-identical output to today's `None` — the golden proves it.
- Everything outside the export loop (oracle args, old/new state constants, randomness counters and
  values, `build_rands`) is emitted in all three modes, unchanged. Only the per-export blocks are
  filtered.
- Update the one `prove` call site: `verify_fn.rs:129` → `ReturnConsts::All`.
- Update the doc comment on `emit_constant_declarations` and on `build_returns` (`:1435`), which
  currently describes `skip_return_constraint_for` in terms of `Some`/`None`.

### 3.3 `driver.rs` — the frame, the transform and the option

```rust
pub struct DebugOptions {
    …
    /// Emit the monolithic `(define-fun <oracle-…>)` bodies and every export's
    /// return constraint into the base frame, as `prove` does (story 15).
    /// Off by default: the debugger encodes each path itself, so the bodies are
    /// dead weight (~73 % of the frame's bytes) and they are the only reason to
    /// run `treeify`. Turn it on to cross-check a verdict against the monolithic
    /// encoding.
    pub with_oracle_functions: bool,
}
```

`base_frame` takes it (or takes an `OracleFns` + `ReturnConsts` pair — either is fine, keep the
signature small):

```rust
let (oracle_fns, returns) = if opts.with_oracle_functions {
    (OracleFns::Include, ReturnConsts::AllExcept(oracle))
} else {
    (OracleFns::Omit, ReturnConsts::Only(oracle))
};
base.extend(eqctx.emit_game_definitions_with(oracle_fns));
base.extend(eqctx.emit_constant_declarations(returns));
```

And the transform, at `:506`:

```rust
// `DebugTransform` (no `treeify`) drives both the executor and — unless
// `--with-oracle-functions` — the `EquivalenceContext`: `treeify` only matters
// for `smt_define_nonsplit_oracle_fn`, and nothing else in the base frame
// compiles a statement body. `samplify` / `sample_max_counter_extractor` run
// before `treeify`, so `sample_info`, argument names, `<return-…>` names,
// datatypes and game-state constants are identical either way.
let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(theorem)?;
let treeified = opts
    .with_oracle_functions
    .then(|| EquivalenceTransform.transform_theorem(theorem))
    .transpose()?;
let (theorem_ctx, auxs_ctx) = match &treeified {
    Some((t, a)) => (t, a),
    None => (&theorem_dbg, &auxs_dbg),
};
let mut eqctx = EquivalenceContext::new(eq, theorem_ctx, auxs_ctx);
eqctx.load_invariants(project)?;
```

`treeified` must be declared before `eqctx` so it outlives the borrow. Note the side benefit worth
a line in the report: with the flag off, the export-existence check
(`eqctx.left_game_inst_ctx()…`) and the symbolic executor now look at the *same* game instances.

`OptionsView` gains `with_oracle_functions: bool`; bump `TRACE_SCHEMA`.

### 3.4 CLI — `crates/domino/src/cli.rs` / `main.rs`

```rust
/// Also emit the monolithic oracle function definitions into the base frame
/// (as `domino prove` does). Off by default — the debugger encodes each path
/// itself, so they only make every query bigger. Use it to cross-check a
/// verdict against the monolithic encoding.
#[clap(long)]
pub(crate) with_oracle_functions: bool,
```

Map it in `main.rs` next to `transcript`. No change to stdout, to the tree rendering or to the
trailer.

### 3.5 Tests

In `emit.rs`'s test module (extend `story04_tests` or add a `story15_tests` alongside it — the
`with_eqctx` / `check_golden` / `render` helpers are already there):

1. `omitting_oracle_fns_drops_exactly_the_oracle_definitions` — `emit_game_definitions_with(Omit)`
   is a subsequence of `Include`'s output, and every entry it drops renders as a `define-fun`
   whose name starts with `<oracle-`. Also assert the `Omit` output still contains a
   `declare-datatype <OracleReturn_…_PKDEC…>` entry (§2.5).
2. `only_returns_keeps_just_the_debugged_oracle` — `ReturnConsts::Only("PKENC")` is a subsequence
   of `AllExcept("PKENC")`, every dropped entry mentions an export other than `PKENC`, and no
   entry of the `Only` output contains the substring `(<oracle-`.
3. `return_consts_all_matches_the_story04_golden` — or simply keep
   `emit_constant_declarations_none_matches_golden` with `ReturnConsts::All` and the same golden
   file. Do not regenerate the golden; if it changes, `All` is wrong.

In `driver.rs`'s test module:

4. `base_frame_has_no_oracle_functions` — run the hello-world driver test path (or call
   `base_frame` directly) and assert `!base_frame_smt.contains("(define-fun <oracle-")` and
   `!base_frame_smt.contains("(<oracle-")`, and that it still contains `declare-datatype`,
   `<<game-state-…-old>>` and the claim assumptions comment.
5. `with_oracle_functions_restores_the_full_frame` — the same run with the flag on contains
   `(define-fun <oracle-`.
6. Verdict parity: extend the existing hello-world end-to-end test (or add one) that runs the same
   project/oracle/claim twice, with and without the flag, and asserts the two `Summary` values and
   the per-pair `Verdict` discriminants are equal.
7. `per_path_dsa_agrees_with_the_oracle_function` — unchanged behaviour, updated comment (§2.6).

### 3.6 Docs

- `docs/stories/00-overview.md`: story 15 is already listed; update the **Pipeline** and **Output**
  rows of §3 if your implementation deviates, and tick 15 off in §5.
- Module docs: `src/debug/driver.rs`'s header comment describes the two-transform split and the
  base frame — rewrite both paragraphs.
- `src/debug/smtout.rs`'s header quotes "~3.5 MB base frame"; update it with the measured number.

## 4. Acceptance criteria

1. `smt/base.smt2` from `domino debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim
   same-output` contains **no** `(define-fun <oracle-` and **no** `(<oracle-` application, and no
   `<return-…-PKGEN>` / `<return-…-PKDEC>` constant. It still contains every `declare-datatype`
   the old frame had, including the `PKDEC`/`PKGEN` `OracleReturn` sorts.
2. That file drops from 3826 lines / 551 KB to roughly 2200 lines / ~150 KB. Record the real
   numbers in the implementation report, together with the `trace.json` and `index.html` sizes
   (both embed the frame; expect each to lose ~400 KB).
3. **Verdicts are unchanged.** For `hello-world` (`UsefulOracle`, every claim) and
   `kem-dem-cca-ssp` proofstep 0 (`PKENC` and `PKGEN`, claims `same-output`, `equal-aborts`,
   `invariant`), the `summary.txt` counters and every pair verdict are identical to a run with
   `--with-oracle-functions`. Any difference is a bug in this story — investigate, do not accept.
4. `--with-oracle-functions` reproduces today's `smt/base.smt2` byte-for-byte (compare against a
   copy taken before the change).
5. `domino prove` is unaffected: `cargo test --workspace` green, the two story-04 goldens unchanged
   on disk, and `scripts/test-known-examples.sh` passes (this story touches code `prove` executes,
   so run it, as story 04 did).
6. The driver runs `EquivalenceTransform` only when the flag is set; with the flag off there is
   exactly one `transform_theorem` call in `run_debug_command`.
7. `trace.json` carries `options.with_oracle_functions` and the bumped `schema`.
8. Wall clock, recorded in the report: `kem-dem` `PKENC` / `same-output`, before vs after, same
   machine, `--smt none`. A speedup is expected but is not itself an acceptance criterion — the
   frame is processed once at level 0 and cvc5 may or may not carry it into each `check-sat`.

## 5. How to verify

```bash
cargo build --workspace                 # NOT `cargo build --release` — see the overview
cargo test --workspace
scripts/test-known-examples.sh          # this story touches prove-shared code

cd example-projects/kem-dem/kem-dem-cca-ssp

# keep a reference copy of today's frame before you change anything
domino debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
cp _build/debug/*/*/PKENC/same-output/smt/base.smt2 /tmp/base-before.smt2
cp _build/debug/*/*/PKENC/same-output/summary.txt   /tmp/summary-before.txt

# after the change
domino debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
B=_build/debug/*/*/PKENC/same-output
grep -c '(define-fun <oracle-' $B/smt/base.smt2     # expect 0
grep -c '(<oracle-'            $B/smt/base.smt2     # expect 0
wc -lc $B/smt/base.smt2 /tmp/base-before.smt2
diff <(grep -v '^elapsed' $B/summary.txt) <(grep -v '^elapsed' /tmp/summary-before.txt)  # expect no diff

# the escape hatch is byte-identical to the old frame
domino debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output \
  --with-oracle-functions
cmp $B/smt/base.smt2 /tmp/base-before.smt2

# a run whose pairs actually fail, to check models still resolve
domino debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKGEN --claim invariant
```

Never run `debug`, `prove` or `latex` against `example-projects/4WHS` or `example-projects/yao`
(overview §7).

## 6. Notes / risks

- **A hand-written `.smt2` naming another oracle's constants.** `Only(o)` removes
  `<return-G-OTHER>`, `return-value-G-P-OTHER`, `<return-is-abort-G-P-OTHER>` and
  `<<game-state-G-new-OTHER>>` from the frame. Nothing generated references them, and kem-dem's
  `invariant.smt2` does not (its lemmas take those values as parameters, §2.5) — but a project
  could. The failure mode is a loud cvc5 parse error on an unknown symbol at frame-writing time,
  not a wrong verdict, and `--with-oracle-functions` is the workaround. If you hit it in a real
  project, note it for follow-up rather than widening the scope here: the principled fix is to emit
  another export's block only when the loaded invariants mention it.
- **Do not also drop `smt_package_return_definitions`** (return *datatypes*) or
  `smt_composition_randomness` (`__sample-rand-*`, used by the randomness-mapping condition and by
  the executor's sampling encoding). Both are load-bearing.
- **`AllExcept` has no `prove` caller** after this story — only the debugger's escape hatch. Keep
  it: it is what makes the "same verdicts with and without the oracle functions" comparison a
  one-flag change instead of two independent knobs.
- **Model size.** `(get-model)` no longer has to print the other exports' `<return-…>` values,
  which are large terms. Failure models under `models/` should get noticeably smaller and more
  readable; mention the before/after of one model file in the report.
- **Story 14 interaction.** If 14 landed first, the base frame is built per worker thread; make
  sure the option reaches every worker and that only one transform runs per worker (or, better,
  that the frame is still built once and shared as text).

## 7. State handed to the next story

Fill in when done:

- `OracleFns` and `ReturnConsts` in `src/writers/smt/contexts/equivalence/emit.rs`, and the
  `emit_game_definitions_with` / `emit_constant_declarations` signatures.
- The `--with-oracle-functions` flag, `DebugOptions.with_oracle_functions`, `OptionsView` field and
  the new `TRACE_SCHEMA` number.
- Measured before/after: `base.smt2`, `trace.json`, `index.html`, one model file, wall clock.
- Whether `run_debug_command` still contains any `EquivalenceTransform` call on the default path
  (it should not).
