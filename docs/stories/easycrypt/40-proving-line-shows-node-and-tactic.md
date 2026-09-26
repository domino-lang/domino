# Story 40 — The proving line shows oracle, `Ni/Total` and the current tactic

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35 (the `prove` command), 39 (the bar layout during an oracle).
**Blocks:** nothing.

---

## 1. Why this story exists

The owner: *"it would be nice for the translation progress bar to indicate node indices Ni to see
where in translation it is! … During the proof job, I also want to see what easycrypt tactic you
are applying in addition to the node … say Ni/Total nodes. So oracle, node, and current tactic."*

Today the bar's message changes only on `ExportEvent::GoalFinished`, i.e. after a node is done, and
shows `<oracle> N7 closed`. While a node is being proved — which is where the time goes — the bar
says nothing about where the walk is or what it is trying.

## 2. Inherited from earlier stories

- **Story 21 / 28:** `ExportEvent`, `BarExportObserver`, `PlainExportObserver`,
  `LiveHandle::activity`.
- **Story 33:** `Prover::node`, the innermost joint node being proved (`router` in the router
  prelude).
- **Story 27:** `OracleTree::new(&run.outcome)`, the joint tree of an oracle.

## 3. Work to do

- Two new events: `NodeStarted { oracle, node, total }`, where `total` is the number of joint nodes
  of the oracle's tree, and `SentenceSent { sentence }`, emitted by `Prover::send` before sending.
- **Bar mode:** one line, `PKENC  N7/23  smt(dec_enc).`, followed by the time spent on the current
  sentence. The tactic is its first line, cut to the terminal width. Before the walk reaches a joint
  node (rung 0, the router prelude) the node shows as `router`.
- `N7/23` names a node and says how big the tree is. It is not a percentage: nodes are not walked in
  id order, and pruned or closed subtrees are skipped.
- **Plain mode:** one line per `NodeStarted` (`  PKENC N7/23`), no sentence lines. Sentences are in
  the transcript.
- `GoalFinished` stays and still reports closed/admitted.

## 4. Acceptance criteria

- [ ] On a TTY the proving line updates on every sentence, and its node matches the `N<k>` of the
      admits the oracle ends with.
- [ ] A unit test of `PlainExportObserver` for `NodeStarted`, and of the bar message format with a
      multi-line sentence (only the first line shown).
- [ ] `--progress none`: unchanged; stdout byte-identical across modes.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt prove --theorem <T> --proofstep 0 -f --no-rung0
```
