# Story 19 follow-up — implementation report: readable inlining in `domino html`

**Status:** done, ad hoc (requested in conversation, no story spec). Branch `amir/html-viewer`.
Follows `b2acefd2` (Story 19: `domino html`) and its two follow-ups.

The oracle cells of the HTML proof viewer had three problems:

1. **Proof parameters were ignored.** A column shown as `H [b ↦ false]` inlined the generic game,
   so its code still branched on `b`. This was limitation 1 of the Story 19 report.
2. **Redundancy.** Every call printed an `invoke` line, a `{ … }` frame, one `param <- arg;` line
   per argument, and a `bind <- e;  // return from X` line. The pipeline added `invoke-result-N`
   and `unwrap-N` temporaries on top of that.
3. **No scoping.** Callee locals kept their source names. A callee's `pk_` was printed as the same
   variable as its caller's `pk_`, and every frame's `invoke-result-1` shared one name.

The cells now come from a new renderer, `src/debug/view.rs`, written for a reader. The debugger's
labelled listing (`domino debug` / `domino inline`) is unchanged.

---

## 1. Before and after

`PKGEN` in `Game_MOD_CCA_PKE_Real_KEM` (kem-dem-cca-ssp). Before:

```
PKGEN() -> Bits(pkeyl) {
    assert ((MOD_CCA_PKE.pk == None));
    pk_ <- invoke KEMGEN()      // KEM.KEMGEN
    {
        assert ((KEM.sk == None));
        invoke-result-1 <- invoke KEM_GEN()      // Scheme_KEM.KEM_GEN
        {
            r <-$ Bits(kgenr) sample-name kem_gen;
            invoke-result-1 <- kem_gen(r);  // return from Scheme_KEM.KEM_GEN
        }
        (pk_, sk_) <- invoke-result-1;
        KEM.pk <- Some(pk_);
        KEM.sk <- Some(sk_);
        pk_ <- pk_;  // return from KEM.KEMGEN
    }
    MOD_CCA_PKE.pk <- Some(pk_);
    return pk_;
}
```

After:

```
PKGEN() -> Bits(pkeyl) {
    assert (MOD_CCA_PKE.pk == None);
    // inlined KEM.KEMGEN
        assert (KEM.sk == None);
        // inlined Scheme_KEM.KEM_GEN
            r <-$ Bits(kgenr) sample-name kem_gen;
            (pk_, sk_) <- kem_gen(r);
        KEM.pk <- Some(pk_);
        KEM.sk <- Some(sk_);
    MOD_CCA_PKE.pk <- Some(pk_);
    return pk_;
}
```

`PKENC` in the same game, in the column the path specializes to `[b ↦ false]`. The package
parameter `dem_idealization: b` has resolved `DEM.ENC`'s branch to `m0`. `key_idealization: false`
has resolved `Key.SET`'s branch. `Key.SET`'s parameter `k_` is replaced by the caller's `k`:

```
PKENC(m0: Bits(ptl), m1: Bits(ptl)) -> (Bits(kctl), Bits(dctl)) {
    assert (not ((MOD_CCA_PKE.pk == None)));
    assert (MOD_CCA_PKE.c == None);
    // inlined KEM.ENCAPS
        assert (not ((KEM.pk == None)));
        assert (KEM.c == None);
        // inlined Scheme_KEM.KEM_ENCAPS
            pk <- Unwrap(KEM.pk);
            r <-$ Bits(kencr) sample-name kem_encaps;
            (k, c_kem) <- kem_encaps(r, pk);
        KEM.c <- Some(c_kem);
        // inlined Key.SET
            assert (Key.k == None);
            Key.k <- Some(k);
    // inlined DEM.ENC
        assert (DEM.c == None);
        // inlined Key.GET
            assert (not ((Key.k == None)));
            k <- Unwrap(Key.k);
        // inlined Scheme_DEM.DEM_ENC
            c_dem <- dem_enc(k, m0);
        DEM.c <- Some(c_dem);
    c_ <- (c_kem, c_dem);
    MOD_CCA_PKE.c <- Some(c_);
    return c_;
}
```

Across all inlined listings in the kem-dem-cca-ssp page, the full rendering went from 1024 lines
to 517. The page went from 138 KB to 103 KB, and Full4WHS went from 918 KB to 714 KB.

## 2. What landed

| File | Change |
|---|---|
| `src/debug/view.rs` (new) | `render_oracle_view(game_inst, oracle, lossy, consts)`: the readable renderer, plus 5 tests. |
| `src/writers/html.rs` | Cells use `render_oracle_view` with the column's assignments. The listing cache is keyed by `(game, oracle, assignments)`. `strip_header` is removed (the view has no header line). The module doc is updated. |
| `src/transforms/theorem_transforms.rs` | `PipelineOptions::split_temporaries`: `ViewTransform` skips `deconstructinvoke` and `unwrapify`. |
| `src/debug/ir.rs` | Removed `render_oracle_listing` and `Inliner::render_loops`, which were view-only. `render_signature`, `render_pattern`, `render_type` and `resolve_const` are now `pub(super)` so the view can reuse them. |
| `src/debug/mod.rs` | `pub mod view;` |

## 3. Why a second renderer

The debugger's `Inliner` (`ir.rs`) builds the IR and the listing in one pass. Every `InlStmt`'s
label is its line number, and `Call` records `frame_lines` / `arg_lines`, which the debug report
uses to highlight executed rows. Removing the `invoke` line or the frame braces there would break
that 1:1 mapping and every pinned listing snapshot. The HTML page has no labels and no IR, so it
gets its own renderer that only produces text. It reuses the expression, type and pattern printers
from `ir.rs`, so both renderers print expressions the same way.

`render_oracle_listing` and `render_loops` existed only for the HTML page. They spliced a symbolic
loop's body into the IR once, producing an IR that was wrong by construction (limitation 3 of the
Story 19 report). Both are gone. `InlineError::NonUnrolledLoop` stays: the debugger still rejects
such loops.

## 4. How the view renders

`render_oracle_view` walks the transformed AST. Each oracle being rendered, whether the entry
oracle or an inlined callee, gets a `Frame` with:

- `names`: the display name of each of its locals;
- `aliases`: the parameters replaced by the caller's argument;
- `scope`: every name visible in the frame (its own names and all enclosing frames' names);
- `ret`: `Top` (a real `return`) or `Bind(Option<String>)` (the caller's bind target).

Every expression goes through `View::expr`. It renames locals, substitutes aliases, resolves
constants, applies the path's assignments, and folds Boolean structure.

### 4.1 Calls without `invoke`

A call prints `// inlined Instance.Oracle` and then the callee body, indented one level. The
indentation takes the place of the old `{ }` frame and shows where the callee ends. The callee's
`return e` prints as `bind <- e;`. A discarded result (`invoke O(…)` as a statement) prints
nothing, unless `e` contains an `Unwrap`: that can still abort, so it prints as `_ <- e;`.

**Early returns.** `returnify` only guarantees a return at the end of every path. It does not
rewrite `if c { return x } rest`. Printed as a flat assignment, such a return would appear to fall
through into `rest`. `normalize` rewrites the callee first:

```
if c { …; return x }          if c { …; return x }
rest…                   ⇒     else { rest… }
```

(and symmetrically for the `else` branch). This only moves code and never copies it. It is done
only when the branch ends in `return` or `abort` on every path *and* contains a `return`, so an
`assert` (`if c {} else { abort }`) is left alone. If a return is still not the callee's last
statement after that (a branch that only *sometimes* returns), the line is marked
`// returns from Instance.Oracle`. No example project reaches that fallback.

### 4.2 Scoping

`Frame::new` collects the frame's locals in order of first appearance: arguments, body locals,
loop variables and generated identifiers. A name keeps its spelling unless an enclosing frame's
`scope` contains it. In that case it becomes `name_2`, `name_3`, … (or `pk_2` for `pk_`), the first
spelling that is free in both the enclosing scope and the frame itself. Names that don't clash are
reserved first, so a callee with both `r` and `r_2` gets `r_3` for its clashing `r`, and its own
`r_2` keeps its name.

Package state needs no renaming: it prints as `Instance.field`. Constants print as their value or
their theorem-level name.

**Only enclosing frames count.** Two calls made in sequence from the same caller may both use `k`.
Neither is in the other's scope, each sits under its own `// inlined` comment, and in the flattened
program the second simply overwrites a dead variable. Renaming these as well would add suffixes
without making anything clearer.

Examples from Yao's `GARBLE`: `Enc.LENCN`'s `r` becomes `r_2` because `MODGB.GBL` has
`(l, r, op)`. `GBL`'s `for j` becomes `for j_2` inside `GARBLE`'s `for j`. `Keys.LGETKEYSOUT`'s
rebound parameter `i <- i + 1` becomes `i_2 <- (i + 1)`.

### 4.3 Parameter substitution

A parameter is replaced by its argument, with no `param <- arg;` line, when:

- the callee never assigns the parameter (including table writes, tuple patterns and loop
  variables), and
- the argument, in the caller's names, is an identifier or a literal.

This is sound because the argument cannot change while the callee runs. The callee cannot reach
the caller's locals, and compositions are acyclic, so it cannot reach the caller's package state
either. Compound arguments (`Unwrap(KEM.pk)`, `i + 1`) keep their binding line so they are not
repeated at every use.

### 4.4 Returning into the caller's variable

`return_names` handles the common `x <- …; return x` → `y <- invoke O()` pattern. If every `return`
of the callee returns the same local `x`, or the same tuple of locals, and the caller binds the
result to a local `y`, or a tuple of locals of the same arity, then `x` is printed as `y`. The
final `y <- x` disappears. This chains through nested calls, which is how
`(pk_, sk_) <- kem_gen(r)` lands in `PKGEN`'s variables through two frames.

Writing `y` before the callee returns is invisible. The callee can only read the caller's locals
through a parameter alias, and the rewrite is skipped if any alias names `y`. An abort discards
everything anyway. The rewrite is also skipped when the bind target is state or a table cell, when
`x` is a parameter, or when names repeat within a tuple.

### 4.5 Proof parameters and folding

`html.rs` passes each column's `ConstAssignment`s as `(theorem constant, literal)` pairs.
`View::constant` follows a constant through `resolve_const` (package parameter → game constant →
theorem constant):

- if it ends in a theorem constant the path assigns, it becomes that literal;
- if it ends in a literal (a value fixed in the game or by the game instance), it becomes that
  literal;
- otherwise it is left for the printer, which shows the name.

`fold` then simplifies bottom-up:

- `not` of a literal;
- `and` / `or` with literal operands (short-circuit to the absorbing value, drop neutral operands);
- `==` of two literals;
- integer `<`, `>`, `<=`, `>=` on literals.

A branch whose condition becomes a literal prints only the side that runs, at the same indentation.
An `assert` that folds to `true` disappears, and one that folds to `false` prints `abort;`.

The listing cache is now keyed by the assignments too, because the same game can appear on a path
twice with different values (4WHS: `H1_0 [b ↦ false] … H1_0 [b ↦ true]`). The assumption tabs and
the no-propositions tab have no assignments, so they show the generic code with `if (b)` intact.

### 4.6 Fewer temporaries

`deconstructinvoke` splits `(a, b) <- invoke O()` into an `invoke-result-N` temporary for the SMT
encoding. `unwrapify` hoists every `Unwrap` into an `unwrap-N` assignment. Neither is needed to
print code, so `ViewTransform` now skips both (`PipelineOptions::split_temporaries = false`).
Tuple binds and `Unwrap(…)` then appear where the source wrote them. In the lossy rendering,
`Unwrap(x)` prints as `x`. The later passes (`resolveoracles`, `samplify`, `loopunroll`,
`sample_max_counter_extractor`, `returnify`, `tableinitialize`) run unchanged on the unsplit code.
Every example project that loads renders without errors (§6).

### 4.7 Small things

- **Self-assignments are dropped.** An assignment, parameter binding or return whose two sides
  print identically (`x <- x`) is not printed. This can happen once aliases and return names line
  up.
- **`if` / `assert` conditions get one pair of parentheses**, not `((…))`.
- **The lossy rendering drops `sample-name …`.**
- **Loops `loopunroll` could not unroll print as `for` blocks**, with the loop variable renamed like
  any other local.

## 5. Unchanged behaviour

- `EquivalenceTransform` and `DebugTransform` still run `deconstructinvoke` and `unwrapify`
  (`split_temporaries: true`). `prove`, `debug`, `inline` and `latex` are unaffected.
- `inline_oracle` / `inline_oracle_rendered` output is byte-identical. The `ir.rs` snapshot tests
  and the `exec.rs` listing pins pass unchanged.
- The HTML page's headers, diagrams, bit captions and package pane are untouched. Only the cell
  contents and their cache key changed.

## 6. Verification

| Check | Result |
|---|---|
| `cargo clippy --workspace --all-targets` | 0 warnings |
| `cargo test --workspace` | 162 passed, 4 ignored (5 new in `debug::view`) |
| `cargo doc --no-deps` | no new warnings |
| `domino html --no-solver` over every example / test project that loads (32 pages) | no error cells, no `invoke`, no `invoke-result-N` / `unwrap-N`, no `if (true)` / `if (false)`, no `// returns from` fallback |

New tests in `src/debug/view.rs`:

- `snapshot_kem_dem_pkgen`: the output above, including the return naming through two frames.
- `kem_dem_pkenc_applies_proof_parameters`: without assignments the listing keeps `if (b)`; with
  `b ↦ false` it matches the `PKENC` snapshot above.
- `yao_garble_respects_scoping`: `r_2`, `for j_2`, `i_2 <- (i + 1)`, the substituted `(i, r)`, and
  no `invoke`.
- `normalize_moves_the_rest_after_an_early_return` and
  `normalize_leaves_asserts_and_partial_returns`: the early-return rewrite and the cases it must
  not touch.

Pages were checked by extracting the `<pre>` cells, not in a browser. The markup around the cells
did not change. `nprf`, `hello-world-hybrid`, `ae`, `ae-mini` and `rosenpass-basic` fail to load
(these errors predate this change) and were not exercised.

## 7. Known limitations

1. **`not ((x == None))` keeps its double parentheses** in the full rendering. They come from
   `render_expr_with`, which the debugger's listing shares and its tests pin. The lossy rendering
   prints `x != ⊥`.
2. **Folding is deliberately shallow.** Only literal Boolean structure, literal equality and
   integer comparisons are folded. An integer parameter used in a loop bound or in a `Bits(n)`
   type is not substituted.
3. **Partial early returns** (a branch that returns on some paths only, followed by more code)
   cannot be flattened without copying code. They print with a `// returns from` note.
4. **Sequential calls may reuse a name** (§4.2). This is by design, but a reader who wants every
   inlined variable unique across the whole listing would need a global name set instead of the
   per-scope one.
5. **No HTML snapshot test.** The renderer is tested directly; `html.rs` still has no test of its
   own. This was limitation 6 of the Story 19 report.
