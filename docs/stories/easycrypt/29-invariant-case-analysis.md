# Story 29 — Invariant case analysis on table writes (documented, not scheduled)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Status:** **design record only. Do not implement until the owner schedules it.** Schedule it
after story 27 has run on real projects and its report lists the `domino-verified-ec-failed`
invariant parts.
**Depends on:** 27.

---

## 1. The problem

The part of hand-written invariant proofs that takes the most effort (§8.1c: 433 `case` uses in
`ec4whs`) is pointwise reasoning about updated tables:

```
move => c. case (c = ctr{hr}) => [ceq|cneq].
+ rewrite ceq !get_set_sameE => /#.
rewrite !get_set_neqE => /#.
```

A relation that quantifies over a table's index (`forall k, T.[k] <> None => …`) usually defeats
plain `smt` after a write `T.[x] <- v`. The proof has to case on whether the quantified index is the
written one.

## 2. The recorded algorithm

The owner's `docs/ProvingAlgorithm.pdf`, for one invariant in one branch:

1. `rewrite /operatorname.`
2. If there is a `forall`: `move => v_1 … v_k`, taking `k` and the names from the goal.
3. If `rewrite !get_set_neqE /#.` solves it, stop.
4. While there are map updates (`<-`) in the goal:
   - try `rewrite get_set_sameE /=.`;
   - else try `rewrite get_set_neqE /=; 1: done.`;
   - else `rewrite get_setE`, copy the resulting `if` condition `C` into `case (C) => ieq.`, and in
     the first case `+ rewrite ieq get_setE /=.`; recurse from step 3 in each case, indented.
5. `smt().`
6. Give up: keep steps 1–2, then `admit`.

Story 27 already does steps 1–3, 5 and 6 (§3.5 of that story). This story adds **step 4**.

## 3. How it would be built

- **Mostly EasyCrypt-driven.** The JSON (story 25) exposes:
  - the map updates as operator applications in the formula tree (`fmap` set, `.[_ <- _]`);
  - after `rewrite get_setE`, the `if` condition as a subtree with a `pp`.

  So "copy the if condition" means taking that node's `pp`. Domino does **not** need to understand
  that a quantifier ranges over a table index.
- **Domino's contribution is optional guidance.** The symbolic effect of a joint path
  (`src/debug/effect.rs`, symbolic-execution story 18) lists which tables the path wrote, and at
  which keys. Use it to choose **which** update to case on first, and to skip the case split
  entirely where the path wrote no table the relation reads.
- The same `undo`-driven ladder applies: every rewrite and case split is tried and undone on
  failure. The case split is bounded by the number of updates in the goal.

## 4. Open questions for when it is scheduled

- Is the order of case splits significant for proof size in practice? Measure it on the
  `domino-verified-ec-failed` list from story 27.
- Should sized intro patterns (`&1 &2 27? nabort *`) and `do split; ~i..j` selection also be
  generated from the JSON's conjunct structure? Only if story 27's split by meaning turns out to be
  insufficient.
