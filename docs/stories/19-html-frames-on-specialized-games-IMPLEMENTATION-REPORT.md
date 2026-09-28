# Story 19 follow-up — implementation report: assumption frames on specialized path games

**Status:** done, bug fix (reported in conversation). Branch `amir/html-viewer`.
Follows `7361066c` (assumption frames) and `0c3475e8` (readable inlining).

## 1. The bug

In `prf-implies-indcpa-very-modular` (in `domino-examples`), proposition `Main: Gcpa0 ~ Gcpa1`
uses this reduction:

```
reduction Hybrid_b_1_1_0_1 Hybrid_b_1_1_1_1 {
    assumption XOR
    map Gxor0 Hybrid_b_1_1_0_1 { Xor: Xor }
    map Gxor1 Hybrid_b_1_1_1_1 { Xor: Xor }
}
```

The path `Proof::try_new` finds crosses it twice, but never through a game named
`Hybrid_b_1_1_1_1`:

```
… Hybrid_b_1_1_0_1 [b ↦ false] ─reduction→ Hybrid_0_1_1_1_1 ─equivalence→
  Hybrid_1_1_1_1_1 ─reduction→ Hybrid_b_1_1_0_1 [b ↦ true] …
```

`Hybrid_0_1_1_1_1` and `Hybrid_1_1_1_1_1` got no dashed XOR frame around their `Xor` package.
The `Hybrid_b_1_1_0_1` columns did.

## 2. Cause

When the search crosses a hop from a specialized game, `specialize` (`src/proof.rs`) builds the
other side with the same constant values. Here that is `Hybrid_b_1_1_1_1` with `bmsg: b` set to
`false`. If that game is equivalent to one already known, the search reuses it. The theorem
declares exactly that game as `Hybrid_0_1_1_1_1` (`bmsg: false`, all other bits `true`), so the
path uses that name. On the way back, `Hybrid_1_1_1_1_1` is `Hybrid_b_1_1_1_1` with `b = true`.

`outlines()` (`src/writers/html.rs`) framed a column only when its game's **name** equalled the
game a reduction mapping names (`mapping.construction_game_instance_name()`). A specialized
game declared under another name never matches.

The stale page the report came from showed no frames at all. It predated `7361066c`, which
introduced frames. Regenerating it showed the remaining bug above.

## 3. Fix

On a proposition tab, a column now matches a reduction mapping when its game **is, or is a
specialization of**, the mapped game. The test is `game_is_compatible(column_game,
mapped_game)`, the same one the proof search uses to decide that a hop applies to a specialized
game. It is now `pub(crate)` in `src/proof.rs`; its behaviour is unchanged.

- **Which hops count is unchanged.** They are still only the reductions into and out of the
  column (`tab.steps[c].via` and `tab.steps[c + 1].via`), so the looser match cannot pull in
  unrelated reductions.
- **The all-hops tab still matches by name.** Its columns are the theorem's own instances, and
  its hops name them directly. Compatibility there would frame, for example,
  `Hybrid_0_1_1_1_1` for every reduction on `Hybrid_b_1_1_1_1`, even though the theorem never
  uses that reduction for it.
- **Assumption tabs still have no frames.**

| File | Change |
|---|---|
| `src/writers/html.rs` | `outlines()`: a `maps_game` closure tests name equality, or `game_is_compatible` on proposition tabs. Doc comment explains why. |
| `src/proof.rs` | `game_is_compatible` is now `pub(crate)`. |

## 4. Verification

`domino html --no-solver` on `prf-implies-indcpa-very-modular`, tab `Main`, frames per column:

| # | Column | Before | After |
|---|---|---|---|
| 1 | `Hybrid_b_0_0_0_0 [b ↦ false]` | PRF | PRF |
| 2 | `Hybrid_b_1_0_0_0 [b ↦ false]` | PRF, Nonces | PRF, Nonces |
| 3 | `Hybrid_b_1_1_0_0 [b ↦ false]` | Nonces | Nonces |
| 4 | `Hybrid_b_1_1_0_1 [b ↦ false]` | XOR | XOR |
| 5 | `Hybrid_0_1_1_1_1` | — | **XOR** |
| 6 | `Hybrid_1_1_1_1_1` | — | **XOR** |
| 7 | `Hybrid_b_1_1_0_1 [b ↦ true]` | XOR | XOR |
| 8–10 | (mirror of 3–1, `b ↦ true`) | unchanged | unchanged |

`Gcpa0` / `Gcpa1` (columns 0 and 11) have no adjacent reduction and no frame, before and after.

`cargo clippy --workspace --all-targets`: 0 warnings. `cargo test --workspace`: 162 passed,
4 ignored. The page in that project's `_build/html/` was regenerated with the fix.

## 5. Known limitations

1. **No automated test.** `html.rs` still has no tests, and no project in this repository has a
   path that lands on a differently named specialization next to a reduction. The case was
   checked by hand on the external example.
2. **A column could match both sides of one reduction** if both mapped games generalize it.
   Reduction sides normally differ in the assumption's bit, so this does not happen in practice.
   If it did, both mappings would be framed; identical frames are deduplicated.
