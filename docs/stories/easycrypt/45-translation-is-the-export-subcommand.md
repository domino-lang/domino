# Story 45 — Translation is `domino easycrypt export`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35 (translation and proving are separate commands).
**Blocks:** nothing. It is independent of story 44.

---

## 1. Why this story exists

The owner: *"Can we move the translation command from domino easycrypt to domino easycrypt export.
So then we have domino easycrypt export, domino easycrypt debug and domino easycrypt prove in
addition to check-alignment."*

Today translation is the bare parent command. Its flags (`--theorem`, `--force`, `--progress`) live
on the parent `Easycrypt` struct (`crates/domino/src/cli.rs`), next to the subcommand slot. As a
result `domino easycrypt --progress plain debug …` and `domino easycrypt --force prove …` parse, and
the flag is silently ignored, because only translation reads it.

## 2. Inherited from earlier stories

- **Story 35 / ADR 0006:** translation is its own command and a proof job never translates.
- **Story 32 / ADR 0004:** translation refuses to overwrite anything but run artifacts without
  `--force`.
- **Story 21:** translation's `--progress`.
- **`resume-an-oracle-from-its-saved-joint-tree` (ADR 0008):**
  - translation's `--force` also deletes the saved joint trees (`*.tree.json`) through
    `job::remove_records_and_trees`, and its help (`Easycrypt.force`) says so; that help moves to
    `EcExport` unchanged;
  - `EcProve` has `--resume trust|replay|restart` (`ResumeArg`), and `EcProve --force`'s help
    ends "Overrides `--resume`." next to the "fixed by `domino easycrypt --force`" pointer to
    update;
  - `crates/domino/tests/easycrypt_overwrite.rs` gained
    `a_saved_joint_tree_blocks_translation_and_force_deletes_it`, which calls the bare
    `easycrypt` like its neighbours.

## 3. Work to do

- New subcommand `EasycryptCommand::Export(EcExport)`, with `--theorem` (optional: without it every
  theorem is exported), `--force` and `--progress`. These move off `Easycrypt` with their help text
  unchanged. `easycrypt_translate` takes `&EcExport`.
- `Easycrypt` keeps only the global `--project` and `--out`, plus a **required** subcommand
  (`subcommand_required = true`, `arg_required_else_help = true`). Bare `domino easycrypt` prints the
  help and exits non-zero. **No alias**: the branch is unreleased, and an alias would keep the
  ambiguous flag placement.
- Subcommand order in `--help`: `export`, `prove`, `debug`, `check-alignment`.
- Wording: the subcommand is named `export`, and the concept stays **Translation** (`CONTEXT.md`).
  Help text says "translate"/"translation" for what `export` does, as it does today.
- Update every current pointer to the old spelling:
  - help strings: `Easycrypt`'s doc comment, `EcProve --force`'s "fixed by
    `domino easycrypt --force`" → `domino easycrypt export --force`, and any other in `cli.rs` /
    `main.rs`;
  - the integration tests that call bare `easycrypt` (`easycrypt_progress`, `easycrypt_overwrite`,
    `easycrypt_tactics_writes`, `easycrypt_ctrl_c`, `easycrypt_prove`, `easycrypt_lockstep_progress`;
    grep `crates/domino/tests` for `"easycrypt"` to find any added since);
  - the `domino` skill under `.claude/skills/`, and scripts, if they use the bare form.
- **Leave alone:** ADRs and earlier stories. They record what was true when they were written.

## 4. Acceptance criteria

- [ ] `domino easycrypt export [--theorem T] [--force] [--progress M]` behaves exactly as
      `domino easycrypt …` did: same files, same stdout, same refusal without `--force`.
- [ ] `domino easycrypt` with no subcommand prints the help and exits non-zero.
- [ ] `domino easycrypt --force export`, `domino easycrypt --progress plain debug` and
      `domino easycrypt --theorem T prove …` are parse errors.
- [ ] `--project` and `--out` still work before or after the subcommand.
- [ ] No help string, test or skill outside `docs/adr/` and `docs/stories/` names the bare
      translation spelling.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt; echo $?                                   # help, non-zero
$D easycrypt export --theorem <T> --force
$D easycrypt --force export --theorem <T>; echo $?      # parse error
$D easycrypt --progress plain debug --theorem <T>; echo $?   # parse error
grep -rn 'easycrypt --\(force\|progress\|theorem\)' crates .claude scripts
```
