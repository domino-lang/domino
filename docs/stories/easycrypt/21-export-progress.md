# Story 21 — Progress reporting for `domino easycrypt`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 05 (the command).
**Blocks:** nothing. Story 28 reuses the phase list for the `--tactics` run.

---

## 1. Why this story exists

The owner, on the plain export (no tactics): *"I want to know what is being translated now and how
far we are into the process."* `domino easycrypt` currently prints nothing until it finishes. On
4WHS (two theorems, many hops) that is a long silence.

## 2. Inherited from earlier stories

- `domino debug` already has `--progress auto|plain|bar|none` (`crates/domino/src/cli.rs`,
  `enum ProgressMode`). Its behaviour: `auto` = bar on a terminal, plain lines when piped. It uses
  an observer pattern (`src/debug/progress.rs`: `DebugEvent`, `DebugObserver`, `PlainObserver`,
  `BarObserver`, `NopObserver`). Stdout carries only the final report.
- Export entry: `export_theorem` and the writer modules under `src/writers/easycrypt/`
  (`types.rs`, `package.rs`, `game.rs`, `invariant.rs`, `proof.rs`, `export.rs`). The pipeline is
  `EasyCryptTransform`.

## 3. Work to do

1. Add `--progress` to `Commands::Easycrypt`, reusing `ProgressMode` and its default `auto`.
2. Define an `ExportEvent` stream and an observer trait, modelled on `DebugEvent`/`DebugObserver`.
   Don't generalise the debugger's trait unless it falls out naturally. The events are:
   - `TheoremStarted { name, index, total }`;
   - `PhaseStarted { phase, total_items }`, where `phase` is one of `transform`, `types`,
     `packages`, `games`, `invariants`, `proofs`, `write`;
   - `ItemStarted { phase, name, index }`, e.g. package variant `Pkg_KEM_v2`, composition
     `Comp_Game_MOD_CCA_PKE`, equivalence `Eq_H4_H5`;
   - `PhaseFinished`, `TheoremFinished`, and `Finished { files_written }`.
3. Plain mode prints one line per item, e.g. `[Full4WHS 2/2] games 3/7: Comp_H5`. Bar mode shows
   a bar per phase, labelled with the current item.
4. Every event goes to stderr. **Stdout and every written file are byte-identical** to before the
   story, whatever the progress mode.

## 4. Acceptance criteria

- [ ] `domino easycrypt --progress plain` on 4WHS prints every theorem, phase and item, in order.
- [ ] `--progress none` is silent on stderr. Output files are byte-identical across all four modes
      (test with hello-world after story 20, or kem-dem).
- [ ] An observer test pins the event order, as `observer_sees_a_well_formed_event_stream` does
      for the debugger.
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace && D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --progress plain   # export only — allowed
```

## 6. Notes / risks

- Export takes seconds, so don't add threads or throttling. Events are emitted synchronously.
- If `export_theorem` fails partway through, the last event shown must be the item that failed.
  This is the main practical value of the story.

## 7. State handed to the next story

Record in the report the event enum, the phase names and the observer trait's location. Story 28
reuses the phase names for the first part of a `--tactics` run.
