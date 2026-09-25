# Story 19 — implementation report

## Base-case line (exact)

```
auto => />; smt(emptyE map_empty).
```

One `plain_line` in `src/writers/easycrypt/proof.rs`. EasyCrypt accepts `; smt(…)` over zero goals
(kem-dem compiles with `auto => />` closing the base), so no `try` is needed. The first open goal
after this line is always the first oracle's; story 27 may rely on that.

## Per-file classification (EasyCrypt r2026.09, compiled for real)

Every proof compiles with plain `assert_compiles`; no file has a genuine base-case failure.

- kem-dem-cca-ssp: `Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM.ec` compiles.
- Simple4WHS: all compile (unchanged).
- Full4WHS: all nine compile, including the three formerly tolerated (`Eq_H0_H1_0.ec`,
  `Eq_H1_1_H2_0.ec`, `Eq_H3_1_H4.ec`).

## Tolerance helper

Deleted: `assert_compiles_or_known_base_case_gap` and `KNOWN_BASE_CASE_GAPS`.

## Other changes

- New assertion in the kem-dem export test that the base-case line is the one-line form and no
  line is a bare `smt(emptyE map_empty).`.
- "Corrected by story 19" notes appended to the reports of stories 13 and 15.
- No goldens contain the base-case lines.

## Verification

`cargo test --workspace`, clippy: see commit. The three `*_full_tree_compiles_in_dependency_order`
tests ran against the real `easycrypt` binary (~70 s for Full4WHS).
