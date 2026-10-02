# Story 43 — Invariant operators and the invariant `call` are laid out one fact per line

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 06, 07.
**Blocks:** 42 (done **before** 42, despite the number: 42's golden file and diff are reviewed in
this story's layout).

---

## 1. Why this story exists

The owner: *"I want you to prettify the generated operators with respect to newlines. Now it is
generated in one line which is not readable. It's also the same issue when using the call tactic
with invariant."*

Every `op` in `Eq_*_Invariants.ec` is rendered on one line. For 4WHS `Full4WHS`,
`Domino_invariant` of `H1_1 ~ H2_0` is a single line of about 700 characters, and the
`call (: inv {| … |} {| … |}); last first.` sentence in `Eq_*.ec` is a single line of about
2,000 characters. Neither can be read or reviewed. Story 42 will make both larger, which is why
this story comes first.

This story changes **layout only**. Every rendered term must parse back to the term it renders
today, with one deliberate exception (§3.1) that makes the renderer agree with EasyCrypt's grammar.

## 2. Inherited from earlier stories

- **Story 06:** `src/writers/easycrypt/invariant.rs` builds the invariant file as `EcItem`s:
  `EcItem::Record` for the two state types and `EcItem::OpDef` for every `Domino_<rel>`,
  `params_inv` and `inv`. `fold_and` (`invariant.rs`, near `// --- params_inv`) builds
  conjunctions. **"Do not reorder conjuncts"** (story 06 §6): a failed `smt` must be traceable to a
  line of the `.smt2`.
- **Story 07/15:** `src/writers/easycrypt/proof.rs` builds the invariant `call`:
  `build_side_record_lit` makes one `EcExpr::RecordLit` per side, and the sentence is
  `plain_line(format!("call (: {}); last first.", render_expr(&inv_app)))`.
- **Renderer:** `src/writers/easycrypt/render.rs`. `render_op_def` writes
  `op name (args) : ty = <render_expr(body)>.`; `render_expr`/`render_operand`/`prec`/`binop_info`
  are single-line and precedence-driven; `EcExpr::RecordLit` renders `{| f = v; … |}`.
- **Consumers of the `call` sentence:** `src/easycrypt/session.rs::split_sentences` already splits
  multi-line sentences (the `byequiv` precondition is one; see its test
  `sentences_end_at_a_dot_before_whitespace`). `src/easycrypt/check.rs` finds the sentence with
  `sentence.starts_with("call") && sentence.ends_with("last first.")`. The tactics driver reads the
  sentence back from the skeleton (`src/easycrypt/tactics/mod.rs`, "open the proof: everything up
  to `call (…); last first.`") and never renders a record itself.

## 3. Work to do

### 3.1 Fix the associativity of `/\` and `\/` first

`binop_info` marks `And` and `Or` as **left**-associative. `easycrypt/src/ecParser.mly` declares
`%right ORA OR` and `%right ANDA AND`. Today `fold_and` builds a left-nested chain
`((a /\ b) /\ c)`. The renderer prints it as `a /\ b /\ c`, and EasyCrypt reads that back as
`a /\ (b /\ c)`. The two are logically equivalent but are different terms. A right-nested chain is
printed with spurious parentheses (that is the `/\ (l.… /\ …)` in today's `Domino_invariant`).

- Mark `And` and `Or` right-associative in `binop_info`, as `Implies` already is.
- Make `fold_and` (and any other producer of `/\`/`\/` chains, `grep EcBinop::And`) fold to the
  **right**, so that the chains it builds still print without parentheses.
- Add the renderer unit tests: `a /\ (b /\ c)` renders flat; `(a /\ b) /\ c` keeps its
  parentheses; the same for `\/`.

### 3.2 A block renderer for operator bodies

Add a layout-aware renderer next to `render_expr`, e.g. `render_expr_block(e, indent) -> String`,
used **only** by `render_op_def` and the invariant `call` (§3.3). `render_expr` stays single-line
for everything else (oracle bodies, statements, `Types.ec`'s op signatures).

The rules are structural. **There is no column limit and no width-based wrapping.**

- The body of an `op` starts on the line after `=`, indented two spaces.
- A **chain** is a maximal run of the same operator among `/\`, `\/` and `=>`, as the term nests
  under §3.1's associativity. Every operator of a chain starts a new line, operator first. The first
  operand is padded to align with the others:

  ```
  op inv (l : H1_1_state) (r : H2_0_state) : bool =
       params_inv l r
    /\ l.`l_abort_flag = r.`r_abort_flag
    /\ (   !l.`l_abort_flag
        => Domino_invariant l r).
  ```

- A chain that is an operand of another operator is printed as its own parenthesised block,
  aligned as above (the `(   … => …)` line). Parentheses are exactly where `render_operand` puts
  them today. Layout never adds or removes them.
- A quantifier's body (`forall (x : t), body`) and a `let`'s body (`let x = v in body`) go on the
  next line, indented two spaces further than the quantifier or `let`.
- Everything else is printed on one line by the existing `render_expr`, however long it is. An
  atom, an application, an equality or a map access is never broken.
- Conjuncts are never reordered.

### 3.3 The invariant `call`

`call (: inv {| … |} {| … |}); last first.` is rendered with each record starting on its own line
and one field per line:

```
call (: inv
          {| l_pkg_Nonces_d_Nonces = Comp_H1.Pkg_Inst_Nonces.d_Nonces{1};
             l_pkg_Nonces_b = Comp_H1.Pkg_Inst_Nonces.b{1};
             …
             l_abort_flag = Comp_H1.Game_H1.abort_flag{1} |}
          {| r_pkg_Nonces_d_Nonces = Comp_H2.Pkg_Inst_Nonces.d_Nonces{2};
             …
             r_abort_flag = Comp_H2.Game_H2.abort_flag{2} |}); last first.
```

Write **one** record-literal block renderer and use it here. Story 42 nests a record literal inside
a field value (`l_pkg_KX = {| … |}`), and the renderer must already indent a nested literal under
its field. Add a unit test with a nested literal now, even though nothing produces one yet.

### 3.4 Goldens

Regenerate every golden file whose text changes. At least
`testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` and every golden that contains
`call (: inv`. Diff each one before accepting it: it may differ from the old text only in
whitespace, except for parentheses moved by §3.1.

## 4. Acceptance criteria

- [ ] §3.1's associativity tests pass, and `binop_info` agrees with `ecParser.mly` for `/\`, `\/` and `=>`.
- [ ] Unit tests for the block renderer: a flat chain, a nested chain, a `forall` body, a `let`
      body, a long atom that stays on one line, and a nested record literal.
- [ ] Every regenerated golden differs from the old one only in whitespace, plus §3.1's
      parentheses. Say in the implementation report which goldens had §3.1 changes.
- [ ] `domino easycrypt --theorem Simple4WHS` and `--theorem Full4WHS` on `example-projects/4WHS`:
      every `Eq_*_Invariants.ec` compiles with `easycrypt compile`.
- [ ] `domino easycrypt --check-alignment` on 4WHS `Simple4WHS` passes as before. This proves that
      the multi-line `call` is still found and accepted.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cargo test --workspace easycrypt
cd example-projects/4WHS
$D easycrypt --theorem Full4WHS --force
easycrypt compile -I _build/easycrypt/Full4WHS _build/easycrypt/Full4WHS/Eq_H1_1_H2_0_Invariants.ec
less _build/easycrypt/Full4WHS/Eq_H1_1_H2_0.ec           # the call, one field per line
$D easycrypt --theorem Simple4WHS --check-alignment
```

Do **not** run `domino easycrypt prove` on 4WHS (overview §7). The layout cannot change what is
proved: EasyCrypt parses the same terms.

## 6. Notes / risks

- **Where the layout applies.** Only to `op` bodies and to the invariant `call`. Do not route
  oracle bodies or `Types.ec` declarations through the block renderer. Their goldens must not change,
  apart from §3.1 parentheses if they contain `/\`/`\/` chains.
- **Session records.** A `done` oracle's `script` in `Eq_*.session.json` holds only the oracle's
  bullet, never the `call`, so the records stay valid. Re-translating with `--force` deletes them
  anyway (ADR 0006).

## 7. State handed to the next story

Record in `43-…-IMPLEMENTATION-REPORT.md`: the block renderer's name and signature, how to call
it for a record literal with a nested record field value (story 42 needs exactly this), the final
associativity table, and the list of regenerated goldens.
