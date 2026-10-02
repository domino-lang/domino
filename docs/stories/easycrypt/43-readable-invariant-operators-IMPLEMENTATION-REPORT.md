# Story 43 — implementation report

## What changed

- **`src/writers/easycrypt/render.rs`**
  - §3.1: `binop_info` marks `/\` and `\/` right-associative, as `=>` already was (`ecParser.mly`:
    `%right IMPL`, `%right ORA OR`, `%right ANDA AND`). A left-nested chain now keeps its
    parentheses, so EasyCrypt reads back exactly the term in the AST.
  - §3.2: new `pub fn render_expr_block(e: &EcExpr, col: usize) -> String`. `render_op_def` writes
    `op name (args) : ty =` and then the body through it, on the next line at two spaces. The rules:
    - A chain (a maximal run of one of `/\`, `\/`, `=>` as the term nests) puts each operator
      first on its own line, and the first operand is padded to line up with the rest.
    - An operand that needs parentheses is laid out as its own block inside them. The
      parentheses come from the same `prec`/`binop_info` test that `render_operand` uses, so
      layout never adds or removes any.
    - The body of a `forall`/`exists` or a `let` goes on the next line, two spaces further in
      (`render_body_on_next_line`).
    - Everything else, record literals included, is `render_expr`'s single line. There is no
      width limit.
  - §3.3: new `pub fn render_record_block(e: &EcExpr, col: usize) -> String`, the one
    record-literal renderer. It puts one field per line, and a field value that is itself a literal
    is laid out the same way from the column where it starts. New `render_invariant_call` renders
    `ProofLine::InvariantCall` like this: `call (: inv`, then each argument through
    `render_record_block` on its own line at column 10 (two past `inv`), then `); last first.`.
  - `quant_keyword` and `render_quant_binders` are shared by the single-line and the block
    quantifier renderers.
- **`src/writers/easycrypt/ast.rs`**
  - New `ProofLine::InvariantCall { inv: EcExpr }`, structured like `ByequivPrecondition`.
  - New `EcExpr::right_chain(op, operands) -> Option<EcExpr>`, the one fold for `/\`, `\/` and
    `=>`. It nests to the right. For the associative `/\` and `\/` it splices in any operand that
    is already a chain of the same operator, so a whole conjunction is one flat chain with its
    conjuncts in their original order. It never splices `=>`.
- **`src/writers/easycrypt/proof.rs`**: pushes `ProofLine::InvariantCall { inv: inv_app }`
  instead of `plain_line(format!("call (: {}); last first.", render_expr(..)))`.
- **`src/writers/easycrypt/invariant.rs`**: `fold_and` and `translate_nary_bool` (SMT `and`,
  `or`, `=>`) use `EcExpr::right_chain`.
- **`src/writers/easycrypt/types.rs`**: Domino `And`/`Or`, and the adjacent-pairs conjunction of
  an n-ary `==`, use `right_chain` through `fold_right`. `Xor` (`^^`, which EasyCrypt declares
  `%left`) still folds to the left.
- **Goldens regenerated**: `testdata/easycrypt/story01/kitchen-sink.ec` and
  `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`. Both changed in whitespace
  only, with no §3.1 parenthesis changes. No golden contains `call (: inv`.
- **Docs**: story 42's "Inherited from earlier stories" section now names the renderers, the
  `InvariantCall` line, the layout of a nested literal and `right_chain`.

## Verification

- New unit tests in `src/writers/easycrypt/tests.rs`:
  - §3.1: `a_right_nested_conjunction_renders_flat` and
    `a_left_nested_conjunction_keeps_its_parentheses`, the same pair for `\/`, and
    `a_left_nested_implication_keeps_its_parentheses`.
  - §3.2:
    - `an_op_body_chain_puts_every_operator_first_on_its_own_line` (the story's own `inv` example)
    - `a_chain_nested_in_a_chain_is_its_own_aligned_block` (also covers a left-nested chain)
    - `a_forall_body_goes_on_the_next_line_two_spaces_in`
    - `a_let_body_goes_on_the_next_line_two_spaces_in`
    - `a_long_atom_stays_on_one_line`
    - `a_record_literal_in_an_op_body_stays_on_one_line`
  - §3.3: `a_record_literal_puts_one_field_per_line_and_a_nested_one_under_its_field`.
- `invariant.rs`:
  - `n_ary_connectives_nest_to_the_right_and_render_flat` covers `and`, `or`, `=>` and n-ary `=`.
  - `a_conjunction_inside_a_conjunction_is_spliced_into_one_chain` covers nested `and`/`or`/`=` and
    shows that `=>` and an `or` inside an `and` keep their parentheses.
  - `types.rs`: `expr_and_right_fold`, `expr_or_right_fold` and
    `expr_equals_four_operands_is_adjacent_pairs` now expect the right-nested shape.
- `proof.rs`: `the_invariant_call_puts_each_record_on_its_own_line_and_one_field_per_line`
  (hello-world) checks the exact text. It also checks that `split_sentences` still returns the call
  as one sentence starting with `call` and ending with `last first.`, which `check.rs` and the
  tactics driver rely on.
- `export.rs`: `hello_world_exports_its_one_equivalence` expects the new `op` layout.
- **Golden diff check.** I built a baseline binary from `97055f78` and exported five projects with
  it and with this branch: hello-world, simple-KEM-example, kem-dem-cca-ssp, and 4WHS
  `Simple4WHS`/`Full4WHS`. I then compared every `.ec` file with whitespace normalised.
  - 75 files are byte-identical. This covers every `Pkg_*`, `Comp_*`, `Types.ec` and
    `Interfaces.ec`.
  - 27 files differ in whitespace only. This covers every `Eq_*.ec` skeleton and the other
    invariant files.
  - 5 invariant files also *lose* §3.1 parentheses: kem-dem
    `Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM_Invariants.ec`, and Full4WHS `Eq_H1_1_H2_0`,
    `Eq_H2_1_H3_0`, `Eq_H5_H6_0` and `Eq_H6_1_1_H7_0` `_Invariants.ec`.
  - No file gains a parenthesis.
- **EasyCrypt compile**: all 32 `Eq_*.ec` and `Eq_*_Invariants.ec` files of those five exports
  compile with `easycrypt compile -I <dir>`. That includes every equivalence of `Simple4WHS` and
  `Full4WHS`.
- **`domino easycrypt check-alignment --theorem Simple4WHS`**, run on the new export with
  `DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`: `27 oracles checked, 0 mismatches`. The
  multi-line `call` is found and accepted.
- Clippy `--workspace --all-targets`, with and without `--features cvc5-lib`: no new warnings. The only warnings predate this story (see Notes for follow-up).
- Full suite (`DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`): all green, after the review fixes.
  - Plain `cargo test --workspace`: lib 566 passed, 0 failed, 5 ignored; `sspverif_smtlib` 2,
    `debug_all_claims` 3, `easycrypt_overwrite` 6, `easycrypt_progress` 1 passed. The
    cvc5-only test files run 0 tests.
  - `cargo test --workspace --features cvc5-lib`: lib 654 passed, 0 failed, 6 ignored;
    `sspverif_smtlib` 2, `debug_all_claims` 4, `easycrypt_ctrl_c` 4, `easycrypt_lockstep_progress` 1,
    `easycrypt_overwrite` 6, `easycrypt_progress` 1, `easycrypt_prove` 5, `easycrypt_tactics_writes` 3
    passed.

## Deviations and notes

- **What the §3.1 parenthesis changes are.** All of them remove parentheses, and all of them
  flatten an associative `/\`.
  - Most cases are a right-nested group that used to print with spurious parentheses, for example
    `sid = None /\ (ni = nr /\ nr = kmac /\ kmac = None)` from an n-ary SMT `=`. EasyCrypt reads the
    old and the new text as the same term.
  - A few were a group in the middle of a chain, for example a whole-package equality
    (`translate_instance_equality`) spliced between other conjuncts. For those, the old term
    grouped the conjuncts differently. The two are logically equivalent, so nothing EasyCrypt has
    to prove changes.
- **Producers splice nested `/\`/`\/` chains (`EcExpr::right_chain`).** The first version of this
  story only folded to the right. A whole-package equality, or an n-ary `=`, used as the *first*
  conjunct of an `and` then became a left-nested chain. It printed as a new parenthesised block,
  for example in Full4WHS `Domino_invariant` of `H1_1 ~ H2_0`, which went against §3.1's goal that
  chains print without parentheses. The spec review raised this. Splicing in the producers fixes
  it, and the renderer still never adds or removes a parenthesis.
- **Needs the owner's attention: an n-ary SMT `=>` is now translated correctly.**
  `translate_nary_bool` used to fold `=>` to the left, which turned `(=> a b c)` into
  `(a => b) => c`. SMT-LIB's `=>` is `:right-assoc`, so that was a different formula, not just a
  different layout. Sharing `right_chain` makes it `a => b => c`. No example project uses an `=>`
  with three or more arguments, so no golden or export changed. The spec review classed this as
  outside "layout only". I kept it, because the old translation was wrong. It is easy to split out
  if the owner prefers.
- **The `call` is a structured `ProofLine` (`InvariantCall`)**, not a multi-line string in
  `ProofLine::Tactic`, whose doc says `text` is one raw line. `ByequivPrecondition` already
  follows this pattern. The story did not say which mechanism to use.
- **Every `op`, however short, has its body on the next line** (`op kitchen_unit : unit =\n  tt.`),
  as §3.2 says. Each `let` in a sequence steps two spaces further in. In 4WHS's `Domino_state_eq`
  the eleven nested `let`s reach column 35. That follows from the rule.
- **Story 43's verify command `--check-alignment`** is the `check-alignment` subcommand on this branch
  (`domino easycrypt check-alignment --theorem Simple4WHS`).
- The exports were written with `--out /tmp/…`, and nothing under `example-projects/` was written.
- **`cvc5-lib` builds need `source ~/.cache/domino/cvc5-lib-env.sh`** (from
  `scripts/setup-cvc5-lib.sh`). Without it, `cvc5-sys` 0.4.0 tries to build cvc5 from source and
  fails, because `cmake` is not installed.
- `domino easycrypt prove` was not run on 4WHS (overview §7).

## State handed to the next story

- **Operator bodies**: `render.rs::render_expr_block(e: &EcExpr, col: usize) -> String`.
  - `col` is the column of `e`'s first character. The first line carries no indentation of its
    own, and every later line is indented to an absolute column of at least `col`.
  - `render_op_def` passes every `EcItem::OpDef` body through it at `col = 2`, so a new `op` needs
    no layout code.
  - `render_expr` stays single-line for everything else: oracle bodies, statements, axioms, lemma
    statements, `byequiv` conjuncts and `Types.ec`.
- **Record literals**: `render.rs::render_record_block(e: &EcExpr, col: usize) -> String`, used
  only for the arguments of the invariant `call`.
- **A record literal with a nested record field value (story 42)**: build the AST and nothing else.
  - The nesting is `ProofLine::InvariantCall { inv }`, with `inv` being
    `EcExpr::App { head: "inv", args: [left, right] }`. Each side is an `EcExpr::RecordLit`, and the
    nested literal is the *value* of a field, for example
    `("l_pkg_KX", EcExpr::RecordLit { fields: vec![("KX_d_LTK", …), …] })`.
  - It renders as

    ```
              {| l_pkg_KX = {| KX_d_LTK = Comp_H1.Pkg_Inst_KX.d_LTK{1};
                               KX_d_State = Comp_H1.Pkg_Inst_KX.d_State{1} |};
                 l_pkg_KX_b = Comp_H1.Pkg_Inst_KX.b{1};
                 l_abort_flag = Comp_H1.Game_H1.abort_flag{1} |}
    ```

  - The nested literal starts right after `field = `, and its fields line up under its own first
    field. A one-field literal stays on one line (`{| a = 1 |}`).
  - `a_record_literal_puts_one_field_per_line_and_a_nested_one_under_its_field` pins this layout.
- **Associativity table (`binop_info`)**, loosest first:

  | Level | Operators | Associativity |
  |---|---|---|
  | 0 | `=>` | right |
  | 1 | `\/` | right |
  | 2 | `/\` | right |
  | 3 | `=` `<>` | none (parentheses on both sides) |
  | 4 | `<` `<=` `>` `>=` | left |
  | 5 | `+` `-` | left |
  | 6 | `*` `%/` `%%` | left |
  | 7 | `^^` | left |

  Build `/\`, `\/` and `=>` chains with `EcExpr::right_chain` (it splices nested `/\`/`\/`). `^^`
  folds to the left (`types.rs::fold_left`).
- **Goldens regenerated**: `testdata/easycrypt/story01/kitchen-sink.ec` and
  `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`, both whitespace only. No
  golden holds the `call`. Its layout is pinned by `proof.rs`'s
  `the_invariant_call_puts_each_record_on_its_own_line_and_one_field_per_line`.
- Consumers of the `call` sentence are unchanged. `split_sentences` returns the multi-line sentence
  as one string with newlines inside. `check.rs`'s `starts_with("call") && ends_with("last first.")`
  still matches it.

## Code review

`code-review` skill, against `97055f78`, with two reviewers in parallel. There is no
`docs/agents/issue-tracker.md`, and the spec was the story file.

- **Standards** (sources: overview §6/§7, `CONTEXT.md`, the conventions of the surrounding code). No
  hard violations.
  - Fixed: the `debug_assert!` in `render_chain_block` went against render.rs's "rendering is total"
    rule. It is gone.
  - Fixed: `fold_right` was written twice, in `invariant.rs` and `types.rs`. Both now share
    `EcExpr::right_chain`.
  - Fixed: the `Quant` and `Let` arms built the same next-line body. They now share
    `render_body_on_next_line`.
  - Declined: typing `InvariantCall` as `{ head, args }`. The AST keeps the real invariant formula,
    as `ByequivPrecondition` keeps its conjuncts, and the `App` match falls back to one line, as
    render.rs's totality rule requires.
- **Spec**:
  - Fixed: a chain spliced in as the first conjunct printed a new parenthesised block, which went
    against §3.1's goal. The producers now splice (see the deviation above).
  - Fixed: record literals in `op` bodies were laid out one field per line, but §3.2 says
    "everything else on one line". The record layout is now `render_record_block`, used only for the
    `call`. This also removes the reviewer's point that a chain in a field value would print as
    `f =    a`.
  - Kept and flagged for the owner: the `=>` fold, which changes meaning (see above).
  - Declined: the claim that editing story 42 was out of scope. The working agreement (overview §6)
    asks for later stories' "Inherited" sections to be updated.

## Notes for follow-up

- Clippy warnings that predate this story are left alone: `src/debug/sweep.rs:199`, and, with
  `cvc5-lib`, the `tempfile::TempDir::into_path` deprecations in `src/debug/driver.rs` and
  `src/debug/lockstep_run.rs`, which came with the dependency update `0434437c`.
- `example-projects/*/_build/` is not git-ignored, so `domino easycrypt` with the default `--out`
  leaves untracked files in the worktree.
