# Context

The shared vocabulary of this repository. Glossary only — no implementation details, no plans.
When a term here conflicts with how a document or a piece of code uses a word, this file wins.

## Domino core

**Package** — a reusable unit of stateful code: parameters, state fields, imported oracle
signatures and oracle definitions. A package is a *template*; it is never used directly.

**Package parameter** — a value a package is instantiated with. Three kinds: booleans
(see *idealization bit*), integers, and functions.

**Package instance** — a package with all of its parameters bound, living inside one composition
under an instance name. By the time a proof runs, an instance's code has been rewritten so that
every parameter and type is substituted: an instance is *monomorphic*.

**Composition** (also **game**) — a set of package instances plus the call graph wiring them
together, and the list of oracles it exports to the adversary.

**Game instance** — a composition with its game constants bound, named in a theorem. Several game
instances can share one composition and differ only in the constants they bind.

**Theorem constant** — a value declared at theorem level and passed down into game instances and
from there into package instances. Boolean, integer or function.

**Oracle** — a procedure a package defines. An **exported oracle** is one the composition offers
to the adversary.

**Abort** — an oracle ending without a value: an explicit `abort`, an `assert` whose condition is
false, or unwrapping a `None`. An abort is not an error; it is a run of the game in which the
adversary loses its ability to query further. Abort **cascades**: a caller whose callee aborted
aborts too, and once a game has aborted no later query does anything.

**Idealization bit** — a boolean parameter that selects between a real and an idealized behaviour
of a package. Related instances usually differ only in these bits.

**Equivalence** — a proof step claiming two game instances are perfectly indistinguishable. Its
obligations are discharged per exported oracle.

**Claim** — one obligation of an equivalence for one oracle: `invariant`, `same-output` or
`equal-aborts`, each with its dependencies.

**State relation** — a predicate over the left and right game states, hand-written in SMT-LIB, that
an equivalence maintains. One set of state relations per equivalence.

## EasyCrypt export

**Package variant** — one EasyCrypt module generated for a package, specialised to a distinct
assignment of its integer and function parameters. Two package instances that agree on those
parameters share one variant; boolean parameters do not distinguish variants, since they are
initialization arguments.

**Instance clone** — an EasyCrypt theory clone of a package variant, one per package instance, so
that each instance has its own memory. Instances of the same variant differ only by their clone.

**Router** — the EasyCrypt module generated for a composition. It owns the *abort flag*, exposes the
composition's exported oracles, and forwards each to the package instance that defines it. Packages
themselves carry no abort flag.

**Abort flag** — the router's single piece of state, recording that the game has aborted. It is the
EasyCrypt counterpart of Domino's abort cascade: while it is set, every oracle returns `None`.

**Experiment** — the EasyCrypt module that initializes a router with a game instance's constants and
runs the adversary against it. One per composition; the constants are its `run` arguments.

**Game interface** — the EasyCrypt module type listing the oracles a router exposes to the
adversary. Compositions exporting the same signatures share one.

**Game-state record** — a flat record type collecting one game instance's package state fields plus
its abort flag. It exists solely so that invariant operators take a single argument per side; no
router or package ever uses it.

**`Domino_` operator** — an EasyCrypt operator translated from a hand-written SMT-LIB state relation
or helper function, named after its SMT original.
