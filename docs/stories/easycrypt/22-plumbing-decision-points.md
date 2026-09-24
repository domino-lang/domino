# Story 22 — Plumbing branches as decision points in the lowering

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first (§3 "Lockstep
rules", §8.1b).
**Branch:** `amir/easycrypt-export`
**Depends on:** 08 (lowering), 16/17/18 (`easycryptify`'s shape; 18 pruned dead `ec_done` writes).
**Blocks:** 23 (lockstep runs on this IR), 26 (alignment compares its decision skeleton).

---

## 1. Why this story exists

Lockstep execution (story 23) exists to walk the same decisions an EasyCrypt pRHL proof has to
make. EasyCrypt, after `proc; inline.`, has a real `if` for every **plumbing branch** (glossary:
`CONTEXT.md`): the `if (!ec_done) { … }` guards and the `if (!(ec_rN = None)) { … } else { … }`
call-result guards. Story 08's lowering deliberately **splices** the `ec_done` guards away: the
guard is always true on every IR path that reaches it, so the body is inlined into the enclosing
block and both lines are left unlabelled.

For the debugger that was fine. For a proof it is not: EasyCrypt will show a branch at that point
and the proof must step over it (`rcondt{i} ^if`). If lockstep execution never saw the branch, its
**decision skeleton** would differ from EasyCrypt's at every guarded continuation, and alignment
(story 26) would report a mismatch on nearly every oracle. The owner's concern was "mismatches
very often"; this story removes that source by construction.

## 2. Inherited from earlier stories

- `src/writers/easycrypt/lower.rs` (≈1000 lines), `pub fn inline_oracle_ec(game_inst,
  oracle_name) -> Result<InlinedOracle, EcExportError>`. Its module doc (lines ≈30–60) lists the
  elimination rules. `enum Shape` / `fn shape` (≈line 439) classifies statements; `lower_block`
  (≈line 673) emits them.
- `InlStmt::Branch { label, cond, then, els, is_assert, then_lines, else_lines }`
  (`src/debug/ir.rs:113`).
- The story 08 report, §2 (elimination table), §4 (path counts), and §6 (painting only covers
  labelled lines). **Story 18** (`18-dead-flags-and-assert-guards-IMPLEMENTATION-REPORT.md`) since
  pruned dead `ec_done` writes, flipped `if`s with an empty *then*, and dropped guards that a user
  `assert` already covers. kem-dem `PKENC`'s structural paths are now **10 / 28**
  (`Game_MON_CCA_PKE` / `Game_MOD_CCA_PKE_Real_KEM`) against Domino's 6 / 16. Oracles that still
  declare `ec_done` still have a live `if (!ec_done)` guard, so this story's work is unchanged in
  kind; there are just fewer guards. Start from these numbers.
- The IR is executed against the **Domino** (`DebugTransform`) game instance (story 08 §6). There
  is no Domino place for `ec_done`, and none may be invented.

## 3. Work to do

### 3.1 Mark plumbing branches

Add to `InlStmt::Branch` a field `plumbing: Option<Plumbing>`, with

```rust
pub enum Plumbing {
    /// `if (!ec_done) { … }` — guards a continuation after a point that could have exited.
    DoneGuard,
    /// `if (!(ec_rN = None)) { … } else { … }` — guards the use of an inlined call's result.
    CallResult,
}
```

Every Domino IR (`ir.rs`) branch has `plumbing: None`. The existing `ec_rN` guard branches get
`Some(CallResult)`.

### 3.2 Stop splicing `if (!ec_done)` guards

Lower each `if (!ec_done) { B }` to a labelled `InlStmt::Branch`:

- `cond` is the boolean literal **`true`**. On every IR path that reaches the guard, `ec_done` is
  false, because every point that sets it is already a terminal (story 08 §2). The literal states
  exactly that, and it introduces no place.
- `then` is `B`, `els` is empty, `plumbing: Some(DoneGuard)`, and `then_lines` covers `B`.

So the solver sees the condition as *determined*. Lockstep will take it on its side alone, which
is exactly EasyCrypt's `rcondt{i} ^if`.

### 3.3 What stays out of the IR

- The **router prelude** (`ec_result <- None; if (!abort_flag) { … }`) and the router tail
  (`if (ec_result = None) { abort_flag <- true; }`) stay out. Domino has no abort flag to decide
  them with. Stories 26/27 handle the prelude **by construction**: they know the router's shape
  because `game.rs` generates it, not because they match names in EasyCrypt's output. Record this
  explicitly in the module doc.
- Anything after a terminal. An IR path still ends at its `Return`/`Abort`. What EasyCrypt still
  shows after that point, such as guarded dead code or the router tail, is consumed by the proof's
  closing step. Alignment (story 26) treats a lockstep terminal as matching any remaining
  EasyCrypt skeleton on that side.

### 3.4 Listing and labels

The `if (!ec_done) {` row and its `}` row become labelled. `sites` stays 1:1 with labelled
statements. `domino inline --easycrypt` goldens change (story 08's
`testdata/easycrypt/story08/*.txt`); regenerate them and review the diff by hand. Plain
`domino inline` output must stay byte-identical.

### 3.5 Path counts

Each `DoneGuard` adds a structurally present, infeasible *else* child (literal `true`).
`count_terminals` therefore rises. Update `kem_dem_pkenc_path_counts` with the new numbers and
record them. The solver prunes every such child. Add a solver-free test that each `DoneGuard`
condition is the literal `true` and its `els` is empty.

## 4. Acceptance criteria

- [ ] No `if (!ec_done)` row in any `domino inline --easycrypt` listing is unlabelled. Each is a
      `Branch` with `plumbing: Some(DoneGuard)`.
- [ ] Every `ec_rN` guard is `plumbing: Some(CallResult)`; every Domino IR branch is `None`.
- [ ] `plumbing_variables_never_reach_the_ir` still passes: `ec_done` is not a place.
- [ ] `no_path_reads_an_unbound_local_and_the_domino_game_instance_pairs_with_it` and
      `executor_walks_every_structural_path` pass.
- [ ] Plain `domino inline` byte-identical, and `listing_compiles_as_an_easycrypt_procedure`
      passes.
- [ ] Path-count table (old vs new) in the report.
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D inline --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC | grep -n 'ec_done'
```

## 6. Notes / risks

- **Don't make `ec_done` a place.** Its only role in EasyCrypt is to skip code after an exit.
  The IR already models exits as terminals, so on IR paths the flag is constant, and a place would
  add a solver variable that is always false.
- The debugger's sequential exploration also reads this IR. Since story 09 is superseded, the
  only consumers are `domino inline --easycrypt` and lockstep. Sequential `domino debug` without
  `--easycrypt` uses the Domino IR and is unaffected.

## 7. State handed to the next story

Record in the report:

- the `Plumbing` enum and where it lives;
- the lowering rule for `DoneGuard`;
- the fact that router prelude and tail are out of the IR by design;
- the new path counts;
- the golden files that changed.
