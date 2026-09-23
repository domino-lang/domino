# Story 18 — Dead `ec_done` writes and guards a user `assert` already covers

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 16 (`easycryptify`), story 17 (unwrap temporaries), story 08 (debugger IR
lowering, which reads `ec_done`). Cannot be started before them.
**Blocks:** nothing.

The owner has signed off on both parts. Part B is the item story 16 §7 (item 2) and story 17 §6
deferred "until the owner asks": the owner has now asked, **but only for the narrow case in §4**.
General redundant-condition elimination is still deferred.

**The parser is not changed.** `assert c` stays `if c {} else { abort }`
(`src/parser/package.rs:1271`). Everything in this story happens inside `easycryptify`. §3.3
explains why.

---

## 1. Why this story exists

After stories 16 and 17, `KX::Send4` in `example-projects/4WHS/_build/easycrypt/Full4WHS/Pkg_KX.ec`
reads:

```ec
    ec_result <- None;
    ec_done <- false;
    if (!(d_State.[ctr] = None)) {
      if (!(d_State.[ctr] = None)) {                 (* ← B: same test again *)
        state <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run4(state, msg);
        if (!(ec_r1 = None)) {
          d_return <- oget ec_r1;
          (state, msg_) <- d_return;
          d_State.[ctr] <- state;
          (_U, _u, _V, _ltk, acc, _k, _ni, _nr, _kmac, sid, _mess) <- state;
          if (acc = Some true) {
            if (!(sid = None)) {
              if (d_First.[oget sid] = None) {
                d_First.[oget sid] <- ctr;
              } else {
                if (d_Second.[oget sid] = None) {
                  d_Second.[oget sid] <- ctr;
                }
              }
            } else {
              ec_done <- true;                       (* live: read by the guard below *)
            }
          }
          if (!ec_done) {
            ec_result <- Some msg_;
            ec_done <- true;                         (* ← A: nothing reads it *)
          }
        } else {
          ec_done <- true;                           (* ← A *)
        }
      } else {
        ec_done <- true;                             (* ← A *)
      }
    } else {
      ec_done <- true;                               (* ← A *)
    }
    return ec_result;
```

Two independent kinds of noise, plus a third, smaller one in other packages (§1.3).

### 1.1 Part A — `ec_done` writes nothing reads

Only the write under `if (acc = Some true)` is ever read. It feeds the `if (!ec_done)` guard that
keeps `return msg_` from running once the `sid` unwrap has aborted. After each of the other four
writes, the only thing left is `return ec_result`.

They survive because of the rule at `src/transforms/easycryptify.rs:254-256`:

```rust
if !contains_done_guard(&out, &lowerer.ec_done) {
    out = drop_done(out, &lowerer.ec_done);
}
```

The rule is all or nothing. One `if (!ec_done)` anywhere in the oracle keeps **every** write. An
oracle with no guard, such as every procedure in `Pkg_Prot.ec`, loses all its writes, and its guards
lose their `else` arms. That is why `Prot` looks clean and `KX::Send3`/`Send4` do not, even though
the lowering treats their `assert`s the same way. The story 16 implementation report already
records this as a follow-up (`16-easycryptify-IMPLEMENTATION-REPORT.md`, §10, "Flagged oracles keep
`else { ec_done <- true; }` arms").

### 1.2 Part B — a guard the user's `assert` already covers

The Domino source is

```
assert not (State[ctr] == None);
state <- Unwrap(State[ctr]);
```

`guard_unwraps` (story 17) gives the `Unwrap` its own guard. It drops a guard only when an
**unwrap guard** for the same operand encloses it, and only unwrap guards record "facts"
(`easycryptify.rs`, `UnwrapGuards::block`, the `Unwrap` arm). A user's `assert` is parsed as
`if (not (State[ctr] == None)) {} else { abort }` (`src/parser/package.rs:1271`). That is exactly
the shape of the guard an unwrap gets, but it records nothing. So the test is emitted twice.

### 1.3 Empty *then* branches

`Pkg_CR.ec`'s `MAC` (and `PRF`, which has the same shape) comes from

```
y <- mac(k,nonce,i);
if b {
    assert ((MACinverse[y] == None) or (MACinverse[y] == Some((k,nonce,i))));
}
MACinverse[y] <- Some((k,nonce,i));
return y;
```

and renders as

```ec
    if (b) {
      if (d_MACinverse.[y] = None \/ d_MACinverse.[y] = Some (k, nonce, i)) {

      } else {
        ec_done <- true;
      }
    }
    if (!ec_done) {
      …
```

The `assert` is the last statement in its block, so the lowering has nothing to move into its
*then* branch. The `if b` is a join, so the flag is kept and `drop_done` never runs. `drop_done` is
the only place that flips an `if` with an empty *then*, so nothing does, and the writer prints a
blank *then*. That `ec_done <- true` is live, so Part A's pruning alone does not change it. §3.2's
flip does.

### 1.4 Numbers

In `Full4WHS/Pkg_KX.ec` (hand-counted from the current output, so verify them):

| | now | target |
|---|---|---|
| `ec_done <- true;` lines | 31 | 8 |
| `d_State.[ctr] = None` / `d_LTK.[kid] = None` tests repeated on one path | 6 (`NewSession`, `Send1`–`Send5`) | 0 |

The same duplicate appears in every `KX*` variant in `Full4WHS` and `Simple4WHS`, and in
`Pkg_PRF.ec` (`Eval` over `LTK[kid]`, `Get` over `H[kid]`). `Pkg_ReductionMac.ec` has 48
`ec_done <- true` lines, the most of any package, so it is a good file to eyeball.

## 2. Inherited context

This story is self-contained. The implementation session starts with a fresh context.

### 2.1 What `easycryptify` does (stories 16, 17)

`src/transforms/easycryptify.rs` is a Domino→Domino transform. It runs last in
`EasyCryptTransform` and gives every oracle one exit. The pipeline for one body is
`lower_oracle` (`easycryptify.rs:232`):

1. **`guard_unwraps`** (story 17). Every `x <- Unwrap(e)` gets an `assert`-shaped guard
   `if (not (e == None)) {} else { abort }` at the point where `unwrapify` bound it. `unwrap-N`
   temporaries are inlined as `Unwrap(e)`, which the writer renders as `oget e`. A guard is dropped
   when `e` is already in `facts`: the operands a structurally enclosing guard proved `Some`, with
   no write to anything `e` reads since. Facts flow into nested blocks. They never flow out of the
   block that established them, and `kill` removes them when something they read is written.
2. **`Lowerer::lower`** (story 16). For an `if` whose one branch always terminates (an `assert`,
   an unwrap guard, an invoke guard), the rest of the block is **moved** into the surviving branch.
   The terminating branch becomes `ec_done <- true`. Only a real join of two live paths, where at
   least one path may already have terminated, gets `if (!ec_done) { REST }` (the `_` arm,
   `easycryptify.rs:449-467`). Nothing is ever duplicated.
3. **`drop_done`**, only when there is no `if (!ec_done)` anywhere (`easycryptify.rs:1151`). It
   deletes every `ec_done <- …`. If a *then* branch held nothing but that write, it flips the `if` to
   `if (not c) { else-branch }` so the writer never prints an empty *then*.
4. A `debug_assert!(every_unwrap_is_guarded(&out))` (`easycryptify.rs:1081`) checks that every
   `Unwrap(e)` left in the body sits inside the *then* branch of an `if (not (e == None))`. It only
   recognises exactly `Not(Equals([e, None(_)]))`, with `None` second.

### 2.2 Who else reads `ec_done`

**The debugger IR lowering (story 08), `src/writers/easycrypt/lower.rs`.** Its `shape` function
(`lower.rs:451`) classifies:

- `ec_done <- true` as `Shape::SetDone`, which becomes an `InlStmt::Abort` at that line;
- `if (!ec_done) { … }` as a structural `DoneGuard`, whose body is spliced into the enclosing block.

A frame that falls off its end with `ec_result = None` has aborted. For the entry frame that is
the router's `abort_flag <- true` under `if (ec_result = None)`. For an inlined callee it is the
`ec_r<N> <- ec_result` line. Both are `InlStmt::Abort`s. That is what already happens today for
every oracle whose flag `drop_done` removed.

**The EasyCrypt writer** declares `ec_done` as an ordinary local
(`src/writers/easycrypt/package.rs:753`). If no statement mentions it, it is not declared.

### 2.3 Facts about Domino (confirmed by the owner, story 17 §2.2)

- The composition graph is a DAG. An oracle cannot call an oracle of its own package. Packages
  share no state. An `invoke` writes only the local it binds.
- By the time `easycryptify` runs, a `For` is a hard error (`UnsupportedLoopError`), so the
  bodies Part A analyses are **loop-free trees**.

## 3. Part A — remove `ec_done` writes that nothing reads

### 3.1 The rule

After lowering, compute backwards liveness of `ec_done` over the statement tree and delete every
write `ec_done <- v` that is dead afterwards. This **replaces** the all-or-nothing step. It
subsumes that step: with no guard, every write is dead, including the `ec_done <- false`
initialisation. So `contains_done_guard` and the filtering half of `drop_done` go away.

The only read of `ec_done` is the condition of a done guard, `if (not ec_done) { … }` with an empty
*else*. On a loop-free tree the analysis is one reverse pass:

```
prune(stmts, live_after) -> (stmts', live_before)
  live = live_after
  for stmt in stmts, last to first:
    ec_done <- v                      keep iff live;  live = false
    if (not ec_done) { B }            B' = prune(B, live).0;  live = true
    if c { T } else { E }             (T', lt) = prune(T, live); (E', le) = prune(E, live)
                                      live = lt || le
    anything else                     unchanged
  return (kept, live)
```

Start it with `prune(body, false)`: the trailing `return ec_result` does not read the flag.

`debug_assert!` that `ec_done` appears in no expression other than a done guard's condition, so a
future second reader cannot be silently pruned around.

### 3.2 Empty branches afterwards

Pruning can empty a branch, and the lowering already leaves an empty *then* whenever an `assert`
ends its block (§1.3). After pruning, apply one rule to **every** `if` in the body, recursively,
whatever made the branch empty:

- *then* empty and *else* not empty: flip to `if (not c) { else }`. When `c` is already `Not(c')`,
  use `c'` instead of stacking a second `Not`.
- *else* empty: nothing to do. The writer does not print an empty *else*.
- both empty: leave the `if` as it is. Do not delete `if`s in this story.

This **replaces** `drop_done`'s narrower rule, which flipped only a *then* that the flag removal
had emptied and kept an `if` that "already had an empty branch". That exception is exactly what
leaves §1.3's blank *then*, so drop it. Judge a branch's emptiness after that branch's own pruning.
Doing the flip in the same pass as the pruning is fine.

`MAC` after this story:

```ec
    if (b) {
      if (!(d_MACinverse.[y] = None \/ d_MACinverse.[y] = Some (k, nonce, i))) {
        ec_done <- true;
      }
    }
    if (!ec_done) {
      d_MACinverse.[y] <- (k, nonce, i);
      ec_result <- Some y;
    }
```

The negated disjunction must render with its parentheses, `!(A \/ B)`. Check this in the golden
output: the renderer handles precedence, but no test covers this shape today.

**Why this is safe for the other consumers.** The flip only swaps which branch is which. The
condition stays pure, and neither branch changes. The debugger IR (`lower.rs`) gets the same
`Branch` site with the arms swapped, so the path count does not change. `every_unwrap_is_guarded`
is unaffected. The *else* block moves as a whole, so every guard inside it still encloses the same
`Unwrap`s. The only guard shape the flip can remove is `if (not (e == None)) {} else { … }`
becoming `if (e == None) { … }`, and that guard's *then* was empty, so nothing depended on it. Keep
the `debug_assert!` anyway.

### 3.3 Why not change how `assert` is parsed

The obvious alternative is to parse `assert c` as `if (not c) { abort }`, so that no empty *then*
ever exists. **Do not do this.** The parsed shape is load-bearing:

1. **Four other readers recognise it.** `src/writers/tex/writer/block.rs:407` (`ite_is_assert`),
   `src/writers/pseudocode/writer.rs:268`, `src/writers/pseudocode/fmtwriter.rs:265` and
   `src/debug/ir.rs:590` all match "empty *then*, *else* is exactly `[Abort]`" and print it back
   as `assert (c);`. A change to the parser that missed one of them would show users an `if` they
   never wrote.
2. **An `assert not (e == None)` is the same statement as an unwrap guard.** Story 17's
   `assert_some` (`easycryptify.rs:768`) builds `if (not (e == None)) {} else { abort }`. Part B
   depends on the two being identical.
3. **The lowering puts the rest of the block in the *then* branch.** With the current shape, the
   `(_, Always)` arm gives `if (c) { REST } else { ec_done <- true }`. `every_unwrap_is_guarded`
   and Part B's facts both rely on `REST`, and every `Unwrap` in it, being in the *then* branch of
   `if (not (e == None))`. With `if (not c) { abort }`, `REST` would land in the *else* branch,
   and `assert not (e == None)` would carry a double negation. Undoing both would take a flip that
   today runs only when the flag is dropped. Every `assert` in an oracle that keeps its flag would
   come out inverted.

The empty *then* has one narrow cause (§1.3), so it is fixed where it arises, in `easycryptify`'s
output, by §3.2.

### 3.4 Target

`Send4` after Part A alone. Part B's change to the top is shown in §4.4.

```ec
    ec_result <- None;
    ec_done <- false;
    if (!(d_State.[ctr] = None)) {
      if (!(d_State.[ctr] = None)) {
        …
        if (!(ec_r1 = None)) {
          …
          if (acc = Some true) {
            if (!(sid = None)) {
              …
            } else {
              ec_done <- true;
            }
          }
          if (!ec_done) {
            ec_result <- Some msg_;
          }
        }
      }
    }
    return ec_result;
```

`AtLeast` is the case that shows why this has to be liveness and not "drop the `else` arms of the
outer guards". Its `else { ec_done <- true; }` arms at the current lines 462-467 sit **inside**
`if (b = false /\ …)`, and the `if (!ec_done) { ec_result <- Some false; }` after that `if` reads
them. They must stay. Only the write after `Some false` goes.

### 3.5 Consequence for the debugger. The owner should confirm this

A pruned `ec_done <- true` was an `InlStmt::Abort` site. After pruning, that path runs to the end
of its frame and aborts **at the frame's fall-through Abort** instead: the router's `abort_flag`
line for the entry procedure, and `ec_r<N> <- ec_result` for an inlined callee. The number of
paths does not change: no `if` is added or removed, so the branch structure is identical. The path
still records the guard `Branch` that went to its *else*, so the reason for the abort is still
visible. Only the line the abort is attributed to moves.

That is already how every flag-free oracle (all of `Prot`) behaves, so this makes the two kinds
consistent. It is still a user-visible change to `domino inline/debug --easycrypt`, so record it in
the report and update the tests that pin it (§5).

## 4. Part B — a user's `None` test counts as a fact

### 4.1 The rule

In `UnwrapGuards::block`'s `IfThenElse` arm (`easycryptify.rs:673`), recognise a condition of
exactly the shape `every_unwrap_is_guarded` accepts: `Not(Equals([e, None(_)]))`, two elements,
`None` second. `assert not (e == None)` and `if (e != None)` both parse to this
(`src/parser/package.rs:496`). Extract one helper for the shape and use it in both places. When
the condition has this shape, with operand `e`:

1. **Into the *then* block:** walk it with `facts ∪ {e}`. An `Unwrap(e)` inside it needs no guard
   of its own.
2. **After the `if`, in the rest of the enclosing block:** after the existing `kill` for what both
   branches write, add `e` to `facts` if the *else* block always terminates
   (`term_block(else) == Term::Always`) **and** nothing the *then* block writes is read by `e`. The
   only path that reaches the rest went through the *then* branch with `e` `Some`, and nothing
   changed that since.

Case 2 is the `assert`. Its *then* is empty, so the second condition holds trivially. Case 1 covers
user code such as `if (sid != None) { … Unwrap(sid) … }`.

Like story 17's rules, this only **deletes** a guard that would otherwise be emitted. It never
moves or creates one.

### 4.2 Why the unwrap-guard assertion still holds

Case 1 is structural: the dropped guard's `Unwrap(e)` sits inside the *then* of an
`if (not (e == None))`. Case 2 relies on the lowering. An `if` whose *else* is `Always` goes to the
`(_, Always)` arm of `Lowerer::lower`, or to `(Always, Always)` when the *then* also always
terminates, in which case the rest is dead and dropped. The `(_, Always)` arm moves the rest of the
block into that same `if`'s *then* branch. So every `Unwrap(e)` after an `assert not (e == None)`
ends up inside the `if (not (e == None))` the `assert` became, and `every_unwrap_is_guarded` holds
without changes. Keep the `debug_assert!`. It is the check that this argument is still true.

### 4.3 Explicitly out of scope

- **Conjunctions.** `AtLeast` tests `if (b = false /\ !(d_First.[sid] = None) /\ …)` and then
  `if (!(d_First.[sid] = None))` directly inside it. Covering that means splitting `And` conjuncts
  **and** teaching `every_unwrap_is_guarded` to accept a conjunct as a guard. Leave the duplicate
  in place and list it in the report.
- **The negated form** `if (e == None) { abort } else { … }`. The unwrap would then sit in an
  *else* branch, which `every_unwrap_is_guarded` does not accept. Deferred for the same reason.
- **Anything that is not a `None` test.** General implication between conditions stays deferred
  (story 16 §7 item 2), as do merging adjacent guards (§7 item 1) and table-index disequality
  (§7 item 3).

### 4.4 Target

`KX::Send4` after both parts:

```ec
    ec_result <- None;
    ec_done <- false;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run4(state, msg);
      if (!(ec_r1 = None)) {
        d_return <- oget ec_r1;
        (state, msg_) <- d_return;
        d_State.[ctr] <- state;
        (_U, _u, _V, _ltk, acc, _k, _ni, _nr, _kmac, sid, _mess) <- state;
        if (acc = Some true) {
          if (!(sid = None)) {
            if (d_First.[oget sid] = None) {
              d_First.[oget sid] <- ctr;
            } else {
              if (d_Second.[oget sid] = None) {
                d_Second.[oget sid] <- ctr;
              }
            }
          } else {
            ec_done <- true;
          }
        }
        if (!ec_done) {
          ec_result <- Some msg_;
        }
      }
    }
    return ec_result;
```

`KX::Send1` after both parts. It has no flag, and it matches the Domino source line for line:

```ec
    ec_result <- None;
    if (!(d_State.[ctr] = None)) {
      state <- oget d_State.[ctr];
      ec_r1 <@ O.d_Run1(state);
      if (!(ec_r1 = None)) {
        …
      }
    }
    return ec_result;
```

## 5. Acceptance criteria

Part A:

- [ ] In every generated oracle, every remaining `ec_done <- …` is live: some path from it reaches
      an `if (!ec_done)` with no other write in between. Assert this with a helper over the whole
      of `example-projects/4WHS` and `kem-dem-cca-ssp`, not only on the oracles named here.
- [ ] `Full4WHS/Pkg_KX.ec`'s `Send4` matches §4.4. `AtLeast` keeps its three `ec_done <- true`
      arms inside `if (b = false /\ …)` (§3.4).
- [ ] An oracle with no done guard is rendered exactly as it is today, except where §3.2's flip
      applies. All of `Pkg_Prot.ec` must be byte-identical.
- [ ] No generated oracle anywhere in the example projects has an `if` with an empty *then* and a
      non-empty *else*. `Pkg_CR.ec`'s `MAC` and `PRF` match §3.2's listing, including the
      parentheses in `!(A \/ B)`.
- [ ] Unit tests in `easycryptify.rs`'s `mod tests`, written in the existing `show` style: (a) a
      join followed by more code, where the inner abort's write is kept and the outer ones are
      dropped; (b) a write inside a branch that a later guard reads, which is kept; (c) a *then*
      branch that held only the write, which is flipped; (d) both branches emptied, where the `if`
      is kept; (e) an `assert` that ends its block inside a join (§1.3), whose `if` is flipped
      although its *then* was empty before pruning; (f) a flipped `if (not c)`, which becomes
      `if (c)`, not `if (not (not c))`.
- [ ] `src/parser/package.rs` is untouched, and the tex, pseudocode and Domino debug listings are
      unchanged (§3.3).
- [ ] Debugger tests are updated for §3.5, with the reason written in the test's comment:
      `executor_walks_every_structural_path` (`src/writers/easycrypt/lower/tests.rs`): its
      `expected` set of games that reach the router abort, and its comment "`Game_MON_CCA_PKE` keeps
      the flag, so each of its aborts is an explicit `ec_done <- true`". Path counts must **not**
      change. `every_ec_done_true_that_is_not_after_a_return_is_an_abort` must still pass
      unchanged.
- [ ] Doc comments updated: `EC_DONE` (`easycryptify.rs:50`, "Dropped from an oracle that has no
      such guard"), the module doc of `lower.rs` (lines 38-41: `ec_done <- true` is an abort only
      where it survives, otherwise the fall-through abort applies), and `drop_done`/its
      replacement.

Part B:

- [ ] No KX variant in `Full4WHS` or `Simple4WHS` tests `d_State.[ctr] = None` twice on one path
      in `Send1`–`Send5`. `NewSession` tests `d_LTK.[kid] = None` once. `Pkg_PRF.ec`'s `Eval` and
      `Get` each test their operand once.
- [ ] Unit tests: (a) `assert not (x == None); y <- Unwrap(x)` emits one guard; (b) the same with
      a write to `x` between the `assert` and the `Unwrap` keeps both guards; (c) `if (x != None)
      { … Unwrap(x) … }` emits no inner guard; (d) an `Unwrap(x)` in the **else** branch of
      `if (x != None)`, or after an `if (x != None)` whose *else* does not always terminate, keeps
      its guard; (e) a table operand, `assert not (T[k] == None); … T[j] <- v; … Unwrap(T[k])`,
      keeps the second guard, because any write to `T` invalidates it (story 17 §3.2).
- [ ] The `AtLeast` conjunction duplicate is still present, and the report lists it as deferred.

Both:

- [ ] The differential test passes: `cargo test --workspace -- --ignored easycryptify_matches_treeify`
      (`src/debug/easycryptify_differential.rs`, needs cvc5 on `PATH`).
- [ ] `cargo build/test/clippy --workspace` is clean, goldens are regenerated and eyeballed, and
      the output is deterministic.
- [ ] `domino easycrypt` still exports both 4WHS theorems and `kem-dem-cca-ssp`, and they still
      `easycrypt compile` where they did before.

## 6. How to verify

```bash
cargo test --workspace easycrypt
cargo test --workspace easycryptify
cargo test --workspace -- --ignored easycryptify_matches_treeify
```

Then regenerate `example-projects/4WHS/_build/easycrypt` and diff `Pkg_KX.ec` and
`Pkg_ReductionMac.ec` by eye, and `Pkg_CR.ec` for the flip. Every hunk should be a deleted
`ec_done <- true;`, an `else { }` arm that disappeared, a doubled guard that disappeared together
with one level of indentation, or an `if` with an empty *then* flipped into `if (!c) { … }`.
Anything else is a bug.

The differential test is the safety net for **both** parts. Part A wrongly deleting a live write
lets the tail after a join run on an aborted path. Part B wrongly dropping a guard removes an
abort, which makes an oracle stronger than it should be. Neither shows up as an EasyCrypt compile
error. Treat a differential failure as a bug in this story, never as flakiness.

## 7. Notes / risks

- **Order.** The parts are independent. B changes `guard_unwraps`, before lowering. A changes the
  step after lowering. Doing B first gives smaller golden diffs to review for A. Two commits are
  preferable to one.
- **§3.2's flip is the only restructuring in Part A.** It swaps two branches and adds or removes
  one `Not`. It must not be generalised to deleting `if`s or merging them.
- **Apart from that flip, Part A only deletes writes.** Moving or merging done guards, or removing
  an `if`, is out of scope. The path count checked in `executor_walks_every_structural_path` proves
  the branch structure did not change.
- **Part B must not widen `facts` beyond the operand of a `None` test.** It is tempting to also
  handle conjunctions here, but that requires changing `every_unwrap_is_guarded` in the same
  commit, and the owner has not asked for it.
- **Expression equality is structural** (`Expression` holds only its `kind`, no span), so the
  `assert`'s `State[ctr]` and the unwrap's `State[ctr]` compare equal. Test (a) of Part B pins
  this.

## 8. State handed to the next story

Record in `18-dead-flags-and-assert-guards-IMPLEMENTATION-REPORT.md`: the measured counts for
§1.4's table, both for `Pkg_KX.ec` and across the example projects; which oracles lost `ec_done`
entirely; which oracles §3.2's flip changed; the debugger tests changed for §3.5 and how; the
golden paths that changed; and the deferred duplicates that remain (at least `AtLeast`'s
conjunction).
