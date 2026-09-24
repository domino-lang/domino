# Story 19 — Base case: keep the `smt` off the first oracle's goal

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 07 (proof skeleton), 15 (`arg` precondition).
**Blocks:** 27 (tactic generation builds on a skeleton whose base case is right).

---

## 1. Why this story exists

Every generated `Eq_*.ec` proof starts like this (`src/writers/easycrypt/proof.rs`, around line 470):

```
proc; inline.
call (: inv …); last first.

auto => />.
smt(emptyE map_empty).

(* d_PKGEN *)
+ proc; inline. admit.
…
```

A spike in the second design session (overview §8.1b) found that on kem-dem and hello-world,
**`auto => />.` already closes the base case**. The next line, `smt(emptyE map_empty).`, therefore
runs on whatever goal is now first, which is the **first oracle's** equivalence goal
(`d_PKGEN ~ d_PKGEN`). It fails there with `cannot prove goal (strict)`.

Stories 13 and 15 recorded this failure as a "known base-case gap". They blamed it on
game-state records that don't tie the two sides' `run` arguments together, and they built a test
tolerance around it:

- `assert_compiles_or_known_base_case_gap` in `src/writers/easycrypt/mod.rs` (doc comment around
  lines 105–130);
- the `KNOWN_BASE_CASE_GAPS` list in `src/writers/easycrypt/export.rs` (around line 578).

At least for kem-dem, that diagnosis is wrong.

## 2. Inherited from earlier stories

- The proof skeleton is built as `Vec<ProofLine>` in `proof.rs`; `plain_line`, `bullet_line`,
  `blank_line` exist. `render_lemma` (`render.rs`) owns `qed.`
- Files currently tolerated: `Full4WHS`'s `Eq_H0_H1_0.ec`, `Eq_H1_1_H2_0.ec`, `Eq_H3_1_H4.ec`, and
  kem-dem-cca-ssp's one hop (story 15 report §3).
- Files that compile clean today (every other `Simple4WHS`/`Full4WHS` proof): there, `auto => />`
  presumably does *not* close the base case and the `smt` does. **Verify this per file; don't
  assume it.**
- EasyCrypt: `~/.opam/easycrypt/bin/easycrypt`, now r2026.09 (overview §8.1b).

## 3. Work to do

1. Emit the base case as **one** tactic line, `auto => />; smt(emptyE map_empty).` `t1; t2`
   applies `t2` to every goal `t1` leaves, and to none if `t1` closed the goal. So the `smt` can
   never reach an oracle goal. Confirm that EasyCrypt accepts `; smt(…)` over zero goals. If it
   doesn't, use `auto => />; try smt(emptyE map_empty).` and record which form you used and why.
2. For each file in the tolerance list, compile it and classify the result:
   - **it now compiles** → move it to plain `assert_compiles`;
   - **it still fails in the base case** (the `smt` really runs on the base goal and fails) → keep
     it tolerated, with the actual remaining goal quoted in the report.
3. Rewrite the doc comment on `assert_compiles_or_known_base_case_gap` to state the corrected
   diagnosis. If nothing is tolerated any more, delete the helper and `KNOWN_BASE_CASE_GAPS`.
4. Append a short "Corrected by story 19" note to the implementation reports of stories 13 and 15
   where they state the old diagnosis. Don't rewrite their history.
5. Regenerate every golden that contains the base-case lines.

## 4. Acceptance criteria

- [ ] No generated proof contains `smt(emptyE map_empty).` as a line of its own.
- [ ] kem-dem-cca-ssp's `Eq_*.ec` compiles with plain `assert_compiles` (all oracles still
      `admit`).
- [ ] Every 4WHS proof is classified in the report as "compiles" or "genuine base-case failure,
      goal quoted".
- [ ] The tolerance helper is either deleted, or its doc comment and list match that
      classification exactly.
- [ ] `cargo build/test/clippy --workspace` clean; the tests that shell out to EasyCrypt ran for
      real (say so in the report).

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp && $D easycrypt
cd _build/easycrypt/* && rm -f *.eco && easycrypt compile -I . Eq_*[^s].ec
cd ../../../../4WHS && $D easycrypt      # export only — allowed on 4WHS
```

## 6. Notes / risks

- Don't widen the `smt` hints to make a genuinely failing base case pass. Report it instead, as
  story 07 required.
- This is a skeleton change only. Oracle bullets stay `+ proc; inline. admit.`

## 7. State handed to the next story

Record in `19-…-IMPLEMENTATION-REPORT.md`:

- the exact base-case line;
- the per-file classification;
- whether the tolerance helper survives.

Story 27 generates tactics after this line and assumes the first open goal after it is the first
oracle's.
