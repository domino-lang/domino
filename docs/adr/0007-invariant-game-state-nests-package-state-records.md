# The invariant file's game state nests one record per package instance

**Status:** accepted. Implemented by `docs/stories/easycrypt/42-…`.

The translated invariant (`Eq_<L>_<R>_Invariants.ec`) needs a value for each side's game state.
Until story 42 that was one flat record per side, with a field for every package state field
**and** every package parameter. A whole-package equality from a `.smt2`, `(= left.KX right.KX)`,
was expanded field by field over whatever keys the two instances shared. So it also compared
parameters, which Domino's equality does not do: in Domino a package's state is its state fields
only, and parameters are bound once (`CONTEXT.md`, *Package state*).

We now declare, **in the invariant file only**, one record type per package holding that
package's state fields (`KX_pkgstate`). Each side's game record has one field of that type per
instance with state, then one field per parameter that becomes a variable, then `abort_flag`. A
whole-package equality becomes a single record equality, ``l.`l_pkg_KX = r.`r_pkg_KX``. It is
well-typed exactly when both instances use the same package, which matches the sorts in Domino's
encoding. Parameters sit beside the package records, where `params_inv` states them.

## Considered options

- **Keep the flat record and expand equality over state fields only.** This is the smaller
  change. It was rejected because the expansion stays a translation-time reconstruction of
  something Domino states in one `=`. Comparing two different packages would silently compare the
  fields that happen to share a name instead of failing, and story 06 already had to special-case
  whole-instance atoms to make the expansion work.
- **Nest the parameters inside the package record.** Rejected: that is the defect itself. A
  package's state would include its parameters, and every package equality would equate them.
- **Reuse the package modules' own types from `Pkg_*.ec`.** Rejected: packages are translated as
  modules with global variables, not as record values, and adding record types there would change
  every package translation to serve the invariant file alone.

## Consequences

- The package-state types are a helper of the invariant file, like the game records (story 06):
  nothing outside `Eq_*_Invariants.ec` and the invariant `call` mentions them.
- The `call` site builds a nested record literal, and the record's shape is part of every
  generated proof. Changing it again means regenerating every `Eq_*.ec` and re-proving.
- After `rewrite /inv`, smt sees through two levels of record projection instead of one.
- Field names are prefixed with the package name because EasyCrypt record fields are global
  operators. When both sides use the same package, they share the type and therefore its fields.
- A package instantiated with different field types in one equivalence (different widths) cannot
  share a type. It is a hard error until a project needs it.
