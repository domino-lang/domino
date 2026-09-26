# Story 40 — implementation report

## What changed

- **`src/writers/easycrypt/progress.rs`**: two new `ExportEvent`s, `NodeStarted { oracle, node, total }` and `SentenceSent { sentence }`. `proving_message(oracle, node, total, sentence)` renders `PKENC  N7/23  smt(dec_enc).`: the first non-empty line of the sentence only, and `router` instead of `N<k>/<total>` for the router prelude.
  - `BarExportObserver`: remembers the oracle, node and tree size; on `NodeStarted` and `SentenceSent` it sets the bar's message and resets its elapsed timer. The tactics bar's template is now `{prefix} {bar} {pos}/{len}  {wide_msg} {elapsed}`, so indicatif cuts the message to the terminal width and the time on the current sentence sits at the right edge. Other phases keep their template. `GoalFinished` still sets `<oracle> N7 closed|admitted`.
  - `PlainExportObserver`: one line per `NodeStarted` (`  PKENC N7/23`, `  PKENC router`), nothing for `SentenceSent`.
- **`src/easycrypt/tactics/live/mod.rs`**: `LiveHandle::node_started(node, total)` (oracle name from the current oracle) and `sentence_sent(sentence)`.
- **`src/easycrypt/tactics/driver.rs`**: `Prover::send` emits `SentenceSent` before sending; `oracle` emits `NodeStarted` for `router`, `prove_node` for `N<idx>`. `total` is the number of nodes of `OracleTree`'s joint tree (`outcome.tree.nodes.len()`).

## Verification

- Unit tests (`writers::easycrypt::progress::tests`): the message format, including a multi-line sentence (only the first line) and the router; the plain node line; the bar observer's message after `NodeStarted` + `SentenceSent`.
- `tactics::tests::live::the_walk_announces_its_node_before_every_sentence` (real EasyCrypt, hello-world): the first events are `node router/<total>` then `proc; inline.`, every `NodeStarted` carries the same total, and every accepted sentence was announced.
- `crates/domino/tests/easycrypt_lockstep_progress.rs` extended: `--progress plain` prints `router` and `N<k>/<total>` node lines and no sentence lines; `none` prints none; stdout is still identical across the three modes.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean except `src/debug/sweep.rs:199`, older than this story.
- Full suite (`DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`, cvc5 env sourced for the second run): without `cvc5-lib` 548 passed, 0 failed, 5 ignored; with it 636 passed, 0 failed, 6 ignored. The two timing-sensitive session tests from story 39 passed in both runs.

## Deviations and notes

- **`NodeStarted` is also sent when the walk returns to a parent** after a child subtree is done (with the parent's node), so the bar names the node whose sentences are being sent, not the last child. In plain mode this gives a repeated `N3/23` line after a subtree; a reader sees where the walk is again.
- **Not looked at on a terminal.** Stderr is a pipe in the tests, so the drawn bar (truncation by `wide_msg`, the elapsed timer) was checked only through the message string, not on a pty.
- The router prelude's `N0/total` is not shown: the prelude is `router`; the joint tree's root is the first `N<k>`.
- The bar keeps its oracle position (`pos/len`) in front of the new message, which the story did not ask for or forbid.
- `admit.` sentences are sent by `Prover::admit` directly, not through `send`, so they are not announced.
- `CONTEXT.md` and the overview carry unrelated uncommitted edits and are not touched.

## Code review

The `/implement` skill is not available to this agent and `/code-review` was not run; the diff was reviewed by hand against the spec. No finding beyond the stale-node case handled above.
