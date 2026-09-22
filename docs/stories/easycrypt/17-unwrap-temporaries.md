# Story 17 — Removing the `unwrap_N` temporaries and their duplicate guards

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 16 (`easycryptify`). Cannot be started before it.
**Blocks:** nothing.

---

## 1. Why this story exists

Story 16 removed the *duplication* from the generated oracle bodies. What is left is noise of a
different kind: generated variables named after a counter, and the same test written several times
on one path.

`Send3` in `Pkg_KX_noprfkey.ec` declares **eight** of them:

```ec
    var unwrap_2 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_3 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_4 : (int * int * bits_n * bits_n * bits_n);
    var unwrap_5 : (int * int * bits_n * bits_n * bits_n);
    ...
```

`unwrap_2`, `unwrap_3`, `unwrap_4` and `unwrap_5` are all `oget sid`. Each carries its own
`if (sid = None)` guard. On a single path through the oracle, `sid` is tested for `None` three
times and `oget`-ed four times.

### 1.1 Where they come from

`unwrapify` (`src/transforms/unwrapify.rs:66`) exists for the **SMT** writer, which needs every
unwrap to be its own branch point. It walks each expression and replaces every `Unwrap(e)`
sub-expression with a fresh `Identifier::Generated("unwrap-N", ty)`, emitting
`unwrap-N <- Unwrap(e)` before the statement. The counter is per-oracle and 1-indexed.

**It does no deduplication.** In the Domino source

```
if (First[Unwrap(sid)] == None) {
    First[Unwrap(sid)] <- Some(ctr);
}
```

the condition and the table write are two separate expressions, so they get two names, two
bindings and — after story 16 — two guards, for one identical read.

EasyCrypt does not need any of this. It takes `oget sid` inline, so
`if (First.[oget sid] = None)` is legal and reads almost exactly like the Domino source.

### 1.2 The target

The `if (_mess = 2)` cascade of `Send3`, after story 16 and after this story:

```ec
    if (mess = 2) {
      if (!(sid = None)) {
        if (d_First.[oget sid] = None) {
          d_First.[oget sid] <- ctr;
        } else {
          if (d_Second.[oget sid] = None) {
            d_Second.[oget sid] <- ctr;
          }
        }
      }
    }
```

One guard, no temporaries, structurally identical to the Domino source. Story 16 leaves this
cascade at seven `if`s and four temporaries; this story takes it to three `if`s and none.

## 2. Inherited context

This story is self-contained; the implementation session starts with a fresh context.

### 2.1 What story 16 established

`easycryptify` (`src/transforms/easycryptify.rs`) is a Domino→Domino transform running last in the
EasyCrypt pipeline, after `tableinitialize`. It turns each `unwrap-N <- Unwrap(e)` into

```
if (not (e == None)) {
    unwrap-N <- Unwrap(e)
    <rest of the block, moved here>
} else {
    ec_done <- true          // dropped entirely when no guard reads it
}
```

**The invariant this story rests on:** that guard sits at exactly the position `unwrapify` put the
binding, which is exactly where Domino aborts. Story 16 never moves an abort. This story must not
either.

### 2.2 Facts about Domino compositions (confirmed by the owner)

- The composition graph is a **DAG**.
- An oracle **cannot call another oracle of its own package**.
- Packages **do not share state**.

Consequence, and it is the one that makes §3.2 simple: an `invoke` writes only the *callee's*
state, never the caller's. An intervening `invoke` therefore invalidates **nothing** the caller
reads, except the local it assigns its own result to.

## 3. The algorithm

Three rules. They share one analysis — "has anything `e` reads been written since?" — and differ
only in what they do with the answer.

The crucial separation: `unwrap-N <- Unwrap(e)` does two things, and only one of them may move.
It **aborts** (a control effect, at a specific point) and it **names a value** (pure). The guard
stays put; the value is what gets inlined.

### 3.1 Rule 1 — substitute the value, keep the guard

For a binding `unwrap-N <- Unwrap(e)` and a use of `unwrap-N` at a later point `U`: replace the use
with `Unwrap(e)` and delete the binding, provided §3.2 says `e` is unchanged between the two.

The guard story 16 generated stays exactly where it is. Only the temporary disappears. The writer
renders the inlined `Unwrap(e)` as `oget <e>`, which it already does today.

### 3.2 The invalidation analysis

Walking from the binding to the use, `e` is invalidated by:

- an assignment to any local `e` reads;
- an assignment to any **state field** `e` reads;
- a write to a table `T` when `e` reads `T[…]` — conservatively **any** write to `T`. (Proving
  `k ≠ k'` is out of scope; see §6.)

An `invoke` invalidates only the local it binds its result to — by §2.2 it cannot reach the
caller's state. A `Sample` invalidates only its own target.

If `e` is invalidated, the temporary stays. This is a correctness backstop, not a rare path: write
the test for it.

### 3.3 Rule 2 — drop a dominated guard

A second `Unwrap(e)` whose position is **dominated** by an earlier guard for the same `e`, with no
invalidating write between them, needs neither a guard nor a temporary: the earlier guard already
aborted on `e = None`, so the later test provably cannot fire.

"Dominated" here is the ordinary control-flow sense: every path reaching the later unwrap passes
through the earlier guard. In practice, after story 16 the earlier guard's body *contains* the
later unwrap, so domination is structural — the later unwrap is syntactically inside the earlier
guard's `then` block — and no dataflow framework is needed. **Implement it structurally and assert
the containment; do not build a general dominator analysis.**

This is the rule that collapses `Send3`'s four `Unwrap(sid)` sites to one guard. It works there
because the *first* use is unconditional (it is in the condition of the enclosing `if`), so the
surviving guard is the one Domino would have aborted at anyway.

### 3.4 Rule 3 — keep a temporary when it earns its place

Inlining is not unconditionally better. Keep the binding (but still drop the redundant *guards*
under rule 2) when:

- §3.2 invalidates the substitution; or
- `e` is large enough that repeating it hurts more than a name helps. Use a simple syntactic size
  threshold on the rendered expression and **write the chosen threshold into the implementation
  report** — this is the one genuinely arbitrary number in the story.

When a binding survives, name it after the expression rather than the counter where that is
unambiguous (`sid_v` for `Unwrap(sid)`); fall back to `unwrap_N` when the operand is not a plain
identifier or when the derived name would collide. A collision must be a hard error, not a silent
rename, consistent with the overview's naming decision.

### 3.5 Where this runs

Inside `easycryptify`, as a pass over the block **before** the guards of story 16 §3.3 are
generated — the analysis wants to see `unwrap-N <- Unwrap(e)` bindings in their original positions,
and rule 2's "dominated" test is cheapest when expressed on the statement tree story 16 is about to
build. Either order can be made to work; if the implementation finds the reverse order simpler
(rewrite first, then clean up), that is fine — but say which was chosen and why in the report.

Do **not** modify `unwrapify`. It serves the SMT writer, which needs exactly the bindings it emits
today.

## 4. Acceptance criteria

- [ ] `Send3` in `Pkg_KX_noprfkey.ec` declares **no `unwrap_N` variables** and tests `sid = None`
      **once**; its `if (_mess = 2)` cascade matches §1.2.
- [ ] Across `example-projects/4WHS`, no generated oracle contains two syntactically identical
      guard conditions on one path.
- [ ] A test where the unwrapped expression **is** invalidated between binding and use (a table
      write to the same table, and a reassigned local) keeps the temporary and keeps both guards.
- [ ] A test where the two uses are in **sibling branches** rather than nested: the guard must
      **not** be hoisted above the enclosing `if`, because that would abort on a path that never
      unwrapped.
- [ ] A test with an `invoke` between binding and use: substitution still happens (§2.2), and a
      comment in the test names the DAG/no-shared-state reason.
- [ ] A surviving temporary is named after its expression where unambiguous; a derived-name
      collision is a hard error with a span.
- [ ] The story 16 differential test (`#[ignore]`, cvc5) still passes on all four of its oracles.
- [ ] `cargo build/test/clippy --workspace` clean; goldens regenerated and eyeballed; output
      deterministic.

## 5. How to verify

```bash
cargo test --workspace easycrypt
cargo test --workspace -- --ignored easycryptify_matches_treeify
```

The differential test from story 16 §5.1 is the real safety net here — this story's rules are the
ones that can silently *remove* an abort, which is the failure mode that makes an oracle stronger
than it should be and would not show up as a compile error in EasyCrypt or a panic in Rust. Treat a
failure there as a bug in this story, never as a flaky test.

## 6. Notes / risks

- **The guard must never move.** Moving it *later* (past a state write) lets that write commit on
  an aborting path, where Domino would have skipped it — Domino keeps writes made *before* an
  abort, so this is observable. Moving it *earlier* (hoisting above an enclosing `if`) aborts on a
  path that never unwrapped at all. Rules 1 and 2 only ever *delete*; nothing relocates.
- **Table invalidation is deliberately blunt.** Any write to `T` invalidates every read of `T[…]`.
  Refining it with index disequality is listed as deferred in story 16 §7 and stays deferred.
- **The size threshold in §3.4 is a judgement call**, not a derived constant. Pick one, record it,
  and expect to revisit it once someone reads a large generated file.
- **Redundant *condition* elimination is still out of scope.** Rule 2 drops a duplicate guard for
  the same `Unwrap(e)`. It does **not** touch the separate case where an `assert c` and a later
  unwrap test the same thing (story 16 §1.2's duplicated `d_State.[ctr] = None`). The dominating-guard
  machinery here makes that cheap to add afterwards, which is exactly why it is tempting — it is
  still deferred (story 16 §7 item 2) and needs the owner's sign-off, not an implementer's
  judgement.

## 7. State handed to the next story

Record in `17-unwrap-temporaries-IMPLEMENTATION-REPORT.md`: the final `Send3` numbers against story
16 §1.1's table, the size threshold chosen for §3.4, the pass ordering chosen in §3.5 and why, how
many temporaries survived across the example projects and for which reason, and the golden paths
that changed.
