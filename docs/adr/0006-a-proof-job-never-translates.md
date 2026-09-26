# A proof job never translates, and trusts translation's files by name

**Status:** accepted. Implemented by `docs/stories/easycrypt/35-…` to `38-…`. Amends ADR 0004
(its *Resuming is not addressed* consequence).

`domino easycrypt --tactics` translated the whole theorem and rewrote the export tree before every
tactics run. Two runs on different equivalences of one theorem therefore rewrote each other's
files, and since story 32 the second one could not even start without `--force` — which discards
the first one's proofs. Proving a theorem with several equivalences was strictly sequential, even
though each equivalence's proof touches only its own `Eq_*.ec`.

We split the two. `domino easycrypt` **translates** and nothing else. `domino easycrypt prove` runs
one **proof job** per equivalence, and a proof job **never rewrites a file that belongs to
translation or to another equivalence**. It checks translation's files only by name: if a file with
the expected name exists, it is taken to be what translation would have written, and its contents
are not read, compared or fingerprinted. A missing file is created, atomically and only if it is
still absent, so two jobs racing to create it cannot tear it. The unit of parallelism is the
equivalence: a lock stops two jobs on the same one.

Whether an equivalence still needs proving is decided by its **session record**
(`Eq_<L>_<R>.session.json`), not by the proof file: translation always writes a skeleton
`Eq_*.ec`, so the file's existence says nothing. The record is written after the proof file at
every checkpoint and holds each oracle's status and accepted script. A complete record means the
equivalence is skipped; a partial one means the job **resumes**, proving only the oracles not yet
done. A done oracle is closed in the live EasyCrypt session with `admit.` and its recorded script
is written back into the file verbatim — so resuming neither re-proves nor parses anything back
out of a `.ec`.

## Considered options

- **Keep one command, skip translation when the tree exists.** Rejected: the rule "don't
  overwrite" and the rule "regenerate what is stale" collide in one command, and ADR 0004 already
  made re-translation an explicit `--force`.
- **Check contents (hash, banner, byte comparison) before trusting a file.** Rejected: it needs the
  translation to have run in order to know what to compare against, which is the cost the split
  exists to avoid, and it would reject hand-edited files that someone put there on purpose. A stale
  file is fixed by re-translating with `--force`.
- **Resume by parsing the tactic scripts out of `Eq_*.ec`** (the option ADR 0004 deferred).
  Rejected: the record holds the same scripts as data, written by the same process that proved
  them.
- **Re-send a done oracle's script to EasyCrypt on resume.** Rejected: it is re-proving under
  another name, minutes per oracle on kem-dem, and ADR 0005 already accepts that a script
  EasyCrypt accepted once is not re-checked.
- **Allow two jobs on one equivalence (different `--oracle`s) and merge on write.** Rejected for
  now: a merge on every checkpoint is a harder problem than the one being solved.

## Consequences

- **Nothing checks that the files a proof job runs against are current.** Edit a package, forget
  to re-translate, and the next proof job proves against the old translation. This is the price of
  the decision and the reason this ADR exists: do not add a content check to `prove` without
  reading the second option above.
- The session record is not a run artifact. ADR 0004's check protects it, and translation with
  `--force` deletes every one it finds, together with the proofs it describes.
- A resumed proof file is only as trustworthy as the record it was rebuilt from. A hand-edited
  record produces a file that claims proofs EasyCrypt never saw; the record is not meant to be
  edited.
- `--tactics` is removed, not deprecated.
