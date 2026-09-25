# Story 32 — implementation report

## What changed

- `src/writers/easycrypt/overwrite.rs` (new) holds the check and nothing else.
  - `check_export_tree(out, theorems) -> Result<(), ExportTreeError>`. It looks at two things:
    - every `<out>/<theorem>/` of this invocation, recursively. Any file there that is not a run
      artifact is offending.
    - the files directly in `<out>`. Any file there is offending, run artifact or not.
      Subdirectories of `<out>` other than this run's theorems are not looked at.

    It also reports a file where a theorem's directory goes (as a file in `<out>`), and an `<out>`
    that is itself a file. `<out>` and the theorem directories may be links to directories.
    Links inside them are not followed and count as files. A missing directory or an empty one
    passes.
  - `is_run_artifact(rel)`, where `rel` is relative to the theorem's directory. The patterns are
    stated once:
    - `RUN_ARTIFACT_DIRS = ["progress", "!debug!"]`. These are whole subtrees, taken only as
      directories directly in the theorem's directory (`sub/progress/x` is not exempt, and neither
      is a *file* named `progress`).
    - file names ending in `.report.txt`, and `alignment.txt`, at any depth.
  - `ExportTreeOccupied { out, files, proofs }` is a hand-written `miette::Diagnostic` with code
    `easycrypt::export_tree_occupied`.
    - The message is `N existing file(s) under <out> are not run artifacts, so `domino easycrypt`
      wrote nothing:`, followed by every offending file, one per line, relative to `<out>` and
      sorted.
    - The help has one line per `Eq_*.ec` in a theorem directory that holds work:
      `<file>: N of M oracles already proved; --force discards them`. It gains
      `(and the partial proof of K more; `--oracle` limits a run to one oracle)` when some oracles
      are partially proved. The help always ends with `move them away, choose another `--out`, or
      pass `--force` to write anyway (it overwrites what the export writes and leaves other files in
      place)`.
  - `ExportTreeError::Read { path, source }` covers a directory that cannot be read (not
    `NotFound`). Its code is `easycrypt::export_tree_unreadable`.
  - `proof_progress(text) -> OracleCounts { proved, partial, total }` counts the oracle bullets of a
    proof file.
    - A bullet is a `(* <proc> *)` line (one word) followed by a line starting `+ proc`. It runs to
      the next such marker or to `qed.`.
    - A bullet is **proved** when no `admit.` is left in it outside comments. It is **partially
      proved** when it has an admit but is more than the bare `+ proc; inline. admit.`.
    - A fresh export therefore counts 0/0/M and prints no line.
- CLI: `domino easycrypt --force`, documented in `--help` with the exemption list.
- `easycrypt()` (`crates/domino/src/main.rs`) runs things in this order:
  1. load the project and resolve the theorem names (`TheoremNotFound` still comes first);
  2. compute `out_base`;
  3. **run the check** (skipped under `--force`);
  4. only then, with `--tactics`, the `TacticsNeedCvc5Lib` / `Session::start` probe;
  5. the export and the write.

  The probe used to be right after the project load. It moved below the check, so the check comes
  before the probe and before any export work.
- `Error::ExportTree` in the binary wraps `ExportTreeError` (transparent diagnostic).

## Verification

- `writers::easycrypt::overwrite::tests` (11):
  - the exemption patterns, both positive and negative;
  - a missing or empty output passes;
  - every offending file of every theorem is listed, and a run on `A` alone ignores `B`/`C`;
  - a loose file in `<out>` refuses, and a loose `Eq_*.ec` there gets no "discards" line;
  - a file in place of the theorem directory refuses, and so does an `<out>` that is a file;
  - `proof_progress` on a three-oracle file (skeleton / proved / partial) gives (1, 1, 3), and on
    hello-world's real exported `Eq_*.ec` gives (0, 0, 1), which pins the export's bullet shape;
  - `(* *)` and `(**)` lines do not trip the marker parser (a review found a slice panic there);
  - a `--out` that is a link to a directory is followed;
  - the refusal's message and help text.
- `crates/domino/tests/easycrypt_overwrite.rs` (5, runs the binary):
  - **AC 1 and AC 2**, on hello-world: the second run fails non-zero, lists every written file,
    prints nothing on stdout and changes nothing (one file edited in between stays edited).
    `--force` then succeeds, and its tree is byte-identical to a first run into an empty
    directory.
  - **AC 3 and AC 7**: a missing `--out`, an empty one, an empty theorem directory, and one
    holding only `progress/…`, `!debug!/…`, `*.report.txt` and `alignment.txt` all pass.
  - **AC 4**, simulated: hand-written `Prf.ec`/`Invariants.ec` directly in `--out` are refused
    and named. Nothing changes and no theorem directory is created.
  - **AC 5**, on 4WHS (the check fires before any export, so this is cheap):
    - `Full4WHS/` dirty and `Simple4WHS/` clean: refused, and `Simple4WHS/` is not created.
    - Both dirty: both listed in one run.
    - `--theorem Simple4WHS` with `Full4WHS/` still dirty: passes.
  - **AC 6**: `--tactics` with `DOMINO_EASYCRYPT` removed and a dirty directory gives the overwrite
    error. This holds both with and without `cvc5-lib`, since the non-`cvc5-lib` error would
    otherwise be `TacticsNeedCvc5Lib`.
- Manual, §5 of the story, on kem-dem:
  - `rm -rf _build/easycrypt && domino easycrypt` writes 16 files.
  - Running it again refuses, lists the 16 files and exits 1.
  - `--force` writes again.
  - `--out …/4WHS/ec4whs/full` refuses and lists its 8 hand-written files. The shasum of every file
    in that directory is the same before and after, and no directory was created. Its hand-written
    `Eq_H7_bleast0_H7_bleast1.ec` has the export's bullet shape (`12 of 12` proved). No
    "discards" line is printed for it, because it is a loose file and `--force` would not touch it.
- Manual, `--tactics` on hello-world (`cvc5-lib`, `DOMINO_EASYCRYPT=easycrypt/ec.native`):
  - A second run refuses with `Proof/Eq_medium_composition_small_composition.ec: 1 of 1 oracles
    already proved; --force discards them`.
  - With `DOMINO_EASYCRYPT` unset, it gives the same overwrite error.
  - With the `.ec` files moved away, the run is still refused, by the one remaining
    `Eq_….eco` (see below).
  - Once that is moved as well, a second `--tactics` run needs no `--force`.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: no warnings.
- Full suite, `cargo test --workspace` with `DOMINO_EASYCRYPT=easycrypt/ec.native`: all pass
  (sspverif 500 passed, 5 ignored; domino `easycrypt_overwrite` 5, `easycrypt_progress` 1).
  With `--features cvc5-lib`: 564 passed, 1 failed, 6 ignored. The one failure is the known
  `debug::driver::tests::goal_smt_is_empty_for_an_admitted_claim` (see stories 23–31).

## Deviations and notes

- **Files directly in `<out>` block the run.** The story says the check covers "only the
  directories this invocation will write". Under that rule AC 4 cannot hold:
  `--out ec4whs/full` writes `ec4whs/full/Full4WHS/`, which does not exist, so the check would
  pass and the hand-written files would never be named. Domino never writes a file directly into
  `<out>`, so a file there means `<out>` is someone's development and not an export root.
  Granularity between theorems is unchanged: other theorems' *directories* are still not looked at.
- **AC 3's "two consecutive `--tactics` runs need no `--force`"** is read as "run artifacts alone
  never block". A literal second `--tactics` run into the same directory *is* refused, because the
  first one wrote `Eq_*.ec`, the proof the ADR exists to protect. AC 1 requires that refusal.
- **`*.eco` is not a run artifact.** `easycrypt compile`, which the tactics run's compile gate
  and any user compile call, leaves an `.eco` cache next to each compiled `.ec`. Once the `.ec`
  files are moved away the `.eco` still blocks. It is generated and never hand-edited, so adding
  it to the patterns is a one-line change. It was left out because the ADR lists the patterns
  explicitly. **Open question for the owner.** The same goes for `.DS_Store`, which Finder drops
  into any directory it has opened.
- `--force` only overwrites. It does not delete stale files that the new export no longer
  produces. That is the "today's behaviour" the story restores.
- miette wraps long lines at the terminal width (80 when piped). A long `--out` path, or a long
  file name in the list, can wrap mid-path. The global handler was left unchanged.
- The check runs after the project is loaded (it needs the theorem names), so a project that
  does not parse reports its parse error first. It still runs before the probe and before any
  export work.
- **A stray top-level file** such as `.DS_Store` or a `README` in `_build/easycrypt` now blocks
  every theorem's run. That is the price of the loose-file rule above. Ignoring dotfiles there
  would be a small follow-up if the owner wants it.
- **AC 3's wording** ("two consecutive `--tactics` runs need no `--force`") contradicts the
  story's own §6 ("the natural next command is blocked"). The story text should be reworded.
- The library functions `write_files`/`write_all_observed` are still unguarded. The check sits at
  the command, the only place that knows about `--force`.

## State handed to the next story

- Exemption patterns (`src/writers/easycrypt/overwrite.rs`):
  - `RUN_ARTIFACT_DIRS = ["progress", "!debug!"]`: subtrees, directly in `<out>/<theorem>/`.
  - file names `*.report.txt` and `alignment.txt`, at any depth.

  Nothing else is exempt. Any file directly in `<out>` blocks.
- The check sits in `easycrypt()` right after the theorem names and `out_base` are resolved. That
  is **before** the `--tactics` probe (`TacticsNeedCvc5Lib` / `Session::start`) and before any
  export work. `--force` skips it.
- Story 33: a new file about the run must match the patterns above. A sealed oracle counts as
  "partially proved" in the refusal, and `proof_progress` assumes the export's bullet shape
  (`(* <proc> *)` then `+ proc…`). The story-33 "Inherited" section has this.
