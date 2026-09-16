# Story 12 — Render `None` without a type annotation

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 01 (AST + renderer). Do **after** story 10, which moves the goldens.
**Blocks:** nothing.

---

## 1. Why this story exists

Every `None` the exporter emits carries an explicit type argument:

```
d_State.[ctr_] <- (d_U, u, d_V, kid, None<:bool>, None<:bits_n>, None<:bits_n>, None<:bits_n>,
                   None<:(int * int * bits_n * bits_n * bits_n)>, 0);
if (d_State.[ctr] = None<:(int * bool * int * bits_n * bool option * bits_n option * bits_n option
                           * bits_n option * (int * int * bits_n * bits_n * bits_n) option * int)>) {
```

`render.rs:509` renders `EcExpr::None_(ty)` as `format!("None<:{}>", render_type(ty))`
unconditionally, justified by a comment at `ast.rs:154`: *"always annotated; bare `None` is
ambiguous in most positions."*

**That is not true of the positions the exporter emits.** Verified against r2026.06-12-g7e192dd, a
file containing bare `None` in every context the 4WHS export actually produces compiles:

```
ec_result <- None;                                          (* typed local *)
if (d_H.[kid] = None) { … }                                 (* fmap get vs None *)
if (!(d_LTK.[kid] = None)) { … }
d_LTK <- if ltk = None then rem d_LTK kid else d_LTK.[kid <- oget ltk];
d_State.[kid] <- (kid, true, None, 0);                      (* inside a typed tuple *)
op f_none : bool option = None.                             (* op with a declared type *)
op rel (a b : int option) = a = None /\ b = None.           (* typed op parameters *)
```

Bare `None` fails only where *nothing* constrains it:

```
op bad = None.
(* [critical] this operator type contains free type variables *)
```

The exporter never emits that shape — every `op` it writes has a declared result type, and every
statement position assigns to or compares against something already typed. The annotation is pure
noise, and it is the dominant source of line width in the generated package files (4WHS's `KX.ec`
has 65 of them, several spanning an eleven-component tuple type).

## 2. Inherited from earlier stories

- `EcExpr::None_(EcType)` (`src/writers/easycrypt/ast.rs:156`) — the AST node.
- `render.rs:509` — the single rendering site.
- Construction sites: `types.rs:152` (`ExpressionKind::None`), `package.rs:281`, `:725`, `:909`,
  `:1143`, and `invariant.rs` for state-relation bodies.
- Golden `.ec` files under `testdata/easycrypt/story02`, `story03`, `story04`, `story06` all contain
  the annotated form.

## 3. Work to do

### 3.1 Keep the type, stop rendering it

The owner's decision (Q5): **keep `EcType` in `EcExpr::None_`** — story 08's lowering to
`src/debug/ir.rs` will want the type of an abort value — and change only `render.rs:509`:

```rust
EcExpr::None_(_) => "None".to_string(),
```

Rewrite the `ast.rs:154` doc comment to say the opposite of what it says now, and say *why*: the
type is retained for the debugger lowering, not for rendering; EasyCrypt infers it at every position
the exporter emits.

### 3.2 No fallback

Unconditional bare `None`, no heuristic for "ambiguous positions" (owner's decision, Q5). The
existing `assert_compiles` tests are the guard: if a future construct ever needs an annotation,
`easycrypt compile` fails loudly on that golden and the fix is targeted at that construct.

### 3.3 Goldens

Regenerate every `.ec` golden and its `.eco`. This is a large but entirely mechanical diff — nothing
but `None<:…>` → `None`. Review it as such: if any golden line changes in another way, that is a
bug in this story.

## 4. Acceptance criteria

- [ ] `grep -rn "None<:" _build/easycrypt/ testdata/easycrypt/` finds nothing after a full export
      and test run.
- [ ] Every exported file of 4WHS `Simple4WHS`, `hello-world`, `simple-KEM-example` and
      `kem-dem-cca-ssp` still compiles with `easycrypt compile -I .`.
- [ ] `EcExpr::None_` still carries its `EcType`, and `ast.rs`'s comment explains why.
- [ ] The golden diff contains no change other than the `None` spelling.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS
cd _build/easycrypt/Simple4WHS
grep -rn "None<:" . && echo "STILL ANNOTATED"
for f in Types.ec Interfaces.ec Variant_*.ec Comp_*.ec Eq_*_Invariants.ec Eq_*.ec; do
  easycrypt compile -I . "$f" || { echo "FAILED: $f"; break; }
done
```

## 6. Notes / risks

- **`Some` is unaffected.** `Some e` is never ambiguous; do not touch it.
- **`empty` is a separate question.** Empty-`fmap` literals are not part of this story; leave them
  exactly as they are, whatever they currently render as.
- **Do not also "simplify" `oget`.** Same reasoning: out of scope, and `oget` is not noise.
- **The `.eco` files are build artifacts.** Regenerate them the same way the existing goldens were
  produced rather than hand-editing.

## 7. State handed to the next story

Record in `12-…-IMPLEMENTATION-REPORT.md`: that `EcExpr::None_` retains its type for story 08, and
the list of projects re-verified to compile.
