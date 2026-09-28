# Story 19 follow-up — implementation report: hybrid hops in the HTML viewer

**Status:** done (requested in conversation). Branch `amir/html-viewer`, commit `a4702e97`.
Builds on `33998950` ("Fixes for hybrid gamehop", Christoph Egger), cherry-picked from
`amir/yao-restructure` (`f475054d`). Without that fix the proof search cannot cross a hybrid
hop.

## 1. The problem

The target was the Yao proof on `amir/yao-restructure`: theorem `HybridSecurity` in
`example-projects/yao`, with proposition `main: CoreReal ~ CoreIdeal`. Its hybrid is declared as

```
hybrid instance Hybrid hy = { HybridReal {params{… h: hy …}} HybridIdeal {params{… h: hy …}} }
```

and `gamehops { hybrid Hybrid { reduction { assumption Layer … } equivalence { … } } }`.

`domino html` drew the path the proof search finds:

```
CoreReal ─equivalence→ FirstHybrid ─hybrid→ LastHybrid ─equivalence→ CoreIdeal
```

The whole hybrid argument was one `hybrid` label. Its hover text was only the equivalence half,
written with internal names (`Hybrid$true$ == Hybrid$false$+`). The games the hybrid talks
about never appeared as columns. Nothing showed the `Layer` assumption either.

## 2. How the proof search crosses a hybrid

The parser expands `hybrid instance Hybrid hy = …` into three game instances. The loop
variable becomes the theorem constant `hybrid$loop`:

| Instance | Game | `h` |
|---|---|---|
| `Hybrid$false$` | `HybridReal` | `hybrid$loop` |
| `Hybrid$false$+` | `HybridReal` | `1 + hybrid$loop` |
| `Hybrid$true$` | `HybridIdeal` | `hybrid$loop` |

`GameHop::Hybrid` joins `Hybrid$false$` and `Hybrid$true$`, the sides of its reduction. Its
equivalence is `Hybrid$true$ == Hybrid$false$+`. `game_is_compatible` treats `hybrid$loop` as a
wildcard, so `Proof::try_new` makes these moves:

1. It matches `FirstHybrid` (`h: 0`) with `Hybrid$false$`.
2. `specialize` builds the far side with `h` kept as `hybrid$loop`.
3. That game is equivalent to `LastHybrid` (`h: d`), which is declared earlier, so the search
   uses `LastHybrid`.

The hop therefore stands for the whole loop, with the loop variable left free.

## 3. What the page shows now

A proposition tab still follows exactly the path `Proof::try_new` finds. Where that path
crosses a hybrid hop, the tab expands it into the loop step the hybrid proves:

```
CoreReal → equivalence → FirstHybrid
  ≙ ┆ hybrid Hybrid: Hybrid[false]_hy → reduction → Hybrid[true]_hy → equivalence → Hybrid[false]_hy+1 ┆
  ≙ LastHybrid → equivalence → CoreIdeal
```

- **Match links (`≙`)** say what the proof search matched: `FirstHybrid is Hybrid[false] with
  hy ↦ 0`, and `LastHybrid is Hybrid[true] with hy ↦ d`. The text appears on hover and in the
  column header. `loop_at` computes the value from the outer game's constant, where the hybrid's
  game has the loop variable.
- **Three grouped columns.** They are `H[false]` (hy), `H[true]` (hy) and `H[false]` (hy + 1).
  The reduction and the equivalence link them. The columns are dashed-grouped in the breadcrumb
  and tinted in the header ("loop step of hybrid Hybrid").
- **Direction.** When the path enters at the `H[true]` side (a proposition written right to
  left), the columns are reversed: `H[false]`(hy + 1), `H[true]`, `H[false]`.
- **Constants.** The inner columns take the entry game's constants the way `specialize` does
  (`proof::assignments`, now `pub(crate)`). `hybrid$loop` itself is left out.
- **Assumption frames.** The hybrid's reduction draws its dashed assumption frame on the
  `H[false]` and `H[true]` columns. The all-hops tab frames hybrid reductions as well.
- **Names.** Hybrid instances show as `H[false]` / `H[true]`, with the loop value as a subscript.
  `hybrid$loop` appears under its declared name: in the diagram caption (`h=hy + 1`), in the
  inlined listings (`(1 + hybrid$loop)` becomes `(hy + 1)`), and in the package pane. The
  rename is textual. It is safe because `$` cannot occur in a source identifier.
- **Hop list.** "All game hops" shows both halves of a hybrid:
  `Hybrid[false](hy) ~= Hybrid[true](hy) (Layer), Hybrid[true](hy) == Hybrid[false](hy + 1)`.

## 4. Changes

| File | Change |
|---|---|
| `src/parser/theorem.rs` | `ParseTheoremContext::hybrid_loop_vars` records each hybrid instance's loop-variable name; `handle_hybrid` passes it to `Hybrid::new`. |
| `src/gamehops/hybrid.rs` | `loop_var` field and accessor; `reduction()` accessor (the field was `#[allow(unused)]`). |
| `src/proof.rs` | `assignments` is now `pub(crate)`. |
| `src/writers/html.rs` | `Step::via` is now a `Link` (`Hop`, `Match`, `Reduction`, `Equivalence`) instead of `&GameHop`. `Step::hybrid` marks expanded columns. `hybrid_steps` does the expansion. `GameLabel` / `game_label`, `loop_var`, `loop_consts`, `loop_at` and `name_loop_var` handle naming. `hop_text` and the `hybrid_*_text` functions render the hops. `outlines` takes reductions from links and normalizes mapping names with `mapped_game`. New CSS covers the group, match links and tinted columns. |

Two details in `outlines`:

- **Mapping names.** A hybrid's reduction mapping keeps the source text `Hybrid[false]`, not the
  instance name `Hybrid$false$`. `mapped_game` converts it.
- **Hybrid columns match by name only.** For those columns the compatibility test is skipped,
  because `game_is_compatible` reaches `unimplemented!()` when the specific game has a constant
  that is neither a literal nor an identifier, such as `1 + hybrid$loop`.

## 5. Verification

- **Yao `HybridSecurity`**, run with `--no-solver` and with z3. The path is as in §3. No listing
  cell fails to render. `Layer` frames appear on exactly the `Hybrid[false]`/`Hybrid[true]`
  columns. The side pane's `LayerMap.h` reads `0`, `hy`, `hy`, `hy + 1`, `d` across the
  hybrid-related columns. `hybrid$loop` occurs nowhere on the page. A headless Chrome screenshot
  was checked visually.
- **`hello-world-hybrid`** (`Hybrid`: the loop-and-bit form `hybrid instance h i b`; `Hybrid2`:
  the two-game form). Both show `real ≙ h[false]_i → h[true]_i → h[false]_i+1 ≙ ideal`, with
  `identity` frames on the reduction's columns.
- **Reverse direction.** A copy of `Hybrid` with `main: ideal ~ real` gives
  `ideal ≙ h[false]_i+1 → equivalence → h[true]_i → reduction → h[false]_i ≙ real`.
- **No regressions.** Pages from the pre-change binary and the new one were compared for
  test-reductions, 4WHS, hello-world and the five kem-dem projects. Apart from the embedded CSS,
  every page is byte-identical.
- **Workspace checks.** `cargo clippy --workspace --all-targets`: 0 warnings.
  `cargo test --workspace`: 164 passed, 4 ignored.

## 6. Known limitations

1. **No automated test.** `html.rs` still has no tests. The cases above were checked by hand.
   `hello-world-hybrid` would make a small fixture.
2. **The loop's range is not checked.** The proof search accepts `LastHybrid` (`h: d`) as
   `Hybrid[true]` for any `hy`. Going from `Hybrid[false]` at 0 to `Hybrid[true]` at `d` takes
   `d + 1` layer reductions, and nothing checks that bound. The viewer reports what the search
   accepts. A range check would belong in `proof.rs`.
3. **Relies on internal names.** Hybrid instances are recognized by the parser's naming scheme
   (`H$false$`, `H$true$`, `H$false$+`), and the next step by the parser writing `1 + hybrid$loop`.
   If the parser changes either, `hybrid_instance`, `loop_value` and `name_loop_var` must follow.
4. **Only the first loop constant is labelled.** When several game constants are set from the
   loop variable, the name label uses the first. The caption lists all of them.
5. **The `≙` mark is small.** Its meaning is only in the hover text and the column header.
