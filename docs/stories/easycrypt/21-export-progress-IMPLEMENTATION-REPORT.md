# Story 21 — implementation report

## What changed

- New module `src/writers/easycrypt/progress.rs` (state for story 28):
  - `ExportPhase { Transform, Types, Packages, Games, Invariants, Proofs, Write }`, names
    `transform`, `types`, `packages`, `games`, `invariants`, `proofs`, `write`.
  - `ExportEvent<'a>` (`#[non_exhaustive]`): `TheoremStarted { name, index, total }`,
    `PhaseStarted { phase, total_items }`, `ItemStarted { phase, name, index }` (1-based),
    `PhaseFinished { phase }`, `TheoremFinished { name }`, `Finished { files_written }`.
  - `trait ExportObserver { fn on_event(&mut self, &ExportEvent) }`, with `NopExportObserver`,
    `PlainExportObserver`, `BarExportObserver` (indicatif, one bar per phase, finished phases stay).
    Not generalised with the debugger's `DebugObserver`.
  - `PhaseScope` (crate-internal) emits `PhaseStarted`, numbers `ItemStarted`, emits `PhaseFinished`.
- `export_theorem_observed`, `compute_package_variants_observed`, `compute_game_files_observed`,
  `compute_equivalence_files_observed`, `write_all_observed`. The old entry points are wrappers with
  the null observer, so no existing caller changed.
- `domino easycrypt --progress auto|plain|bar|none` (default `auto`, same `ProgressMode` as `debug`).
  Everything goes to stderr.

## Event stream

```
( TheoremStarted
    transform(1: theorem) types(2: Types.ec, Interfaces.ec) packages(Pkg_<variant>…)
    games(Comp_<comp>…) invariants(Eq_<l>_<r>_Invariants…) proofs(Eq_<l>_<r>…)
  TheoremFinished )*
write(<Theorem>/<file>…)  Finished { files_written }
```

Plain example: `[Full4WHS 1/2] games 3/12: Comp_PRF`; write lines have no theorem prefix.

## Deviations

- **`write` is one phase after all theorems**, not per theorem: every theorem is still exported in
  memory before any file is written (a failed export must not leave a half-written tree). Its item
  names carry the theorem directory. Consequently stdout reports are now printed after all writes.
- **`invariants` and `proofs` are separate passes** in `compute_equivalence_files_observed`
  (previously one interleaved loop). The output is identical; test `rendering_is_deterministic`
  and the unchanged goldens confirm it.
- The phase-item names for invariants/proofs are derived from the hop's instance names before
  building, so the event precedes a failure in that item.

## Tests

- `export::tests::observer_sees_a_well_formed_event_stream` (hello-world: phase order, item
  numbering, totals, item names), `observing_does_not_change_the_export`,
  `write_phase_names_every_file_and_ends_with_finished`, `a_failing_export_ends_on_the_failing_item`
  (yao), `progress::tests::phase_scope_numbers_items_from_one`.
- `crates/domino/tests/easycrypt_progress.rs`: runs the binary on hello-world in all four modes;
  stdout and every written file are byte-identical, `none` is silent, `auto` equals `plain` when piped.
- Manual: `domino easycrypt --progress plain` on 4WHS prints both theorems, every phase and item.
- Full `cargo test --workspace`: 462 lib tests passed, 0 failed (5 ignored), plus the new integration
  test; `cargo clippy --workspace --all-targets` clean.
