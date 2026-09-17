# Packages declare their own import interfaces; compositions adapt to them

**Status:** accepted — implemented by `docs/stories/easycrypt/14-package-import-interfaces-and-prefixes.md`.

An exported EasyCrypt package module takes its imported oracles as a functor parameter, and the
obvious way to type that parameter is with the *callee's* exported module type. We did that first,
and it made a package's module a function of the composition it appears in: the parameter's type,
name and even arity came from the wiring, so `Fwd` was emitted twice for `hello-world` — two files
differing in one line — and would be emitted again for every new way of composing it. Instead, a
package now declares its **import interface** in its own file, named by its own import names, and a
composition is responsible for producing something of that shape: it passes a callee's instance
module directly when one instance already serves the whole interface unrenamed, and otherwise emits
a small stateless **import adapter** that fans the expected oracles out to the instances that
provide them. A package is therefore duplicated only when its *code* differs — different `Bits(...)`
widths or different function parameters — never because of how it is plugged in.

## Considered options

- **Type the parameter by the callee's exported interface** (what we had). Rejected: it puts a
  composition-level fact inside a package file, so packages multiply with the wiring. It is also
  *sound* — EasyCrypt's module-type matching is structural and width-subtyping, so the duplicate
  types never forced anything — which is precisely why it survived four stories without looking
  wrong. Expect someone to propose it again; this is the reason not to.
- **One functor parameter per callee instance** (also what we had, orthogonally). Rejected for the
  same reason: the arity and the parameter names (`P_<callee instance>`) are facts about a
  composition.
- **Always emit an adapter, never pass a callee directly.** Rejected as noise: when a single
  instance already satisfies the interface, width subtyping makes the adapter a pure forwarding
  layer with no reader benefit. The cost is that the generated shape is now conditional, which
  anything that inlines the output has to handle.
- **Emit one maximal module type and let width subtyping match everything.** Rejected: the
  parameter's type is what tells a reader — and the debugger lowering — which oracles a package may
  actually call.

## Consequences

- Where an adapter is generated, a proof that inlines a package oracle passes through one extra
  call. Tactic scripts and the EasyCrypt-side debugger lowering must handle both depths.
- `Interfaces.ec` holds game interfaces only. The per-package module types it used to carry — and
  the deduplication of them added by story 11 — are gone.
- A package body now calls its *own* import names, so a composition that renames an oracle
  (`X: Y of inst`) is resolved in the adapter rather than inside the package. This is the one part
  of the change that alters generated oracle bodies rather than names and wiring.
- Function parameters still split a package into several modules, because a `Fn` parameter is
  translated into a call to a named operator baked into the body. Making them `init` arguments of
  arrow type would remove the last non-`Bits` reason for a package to have variants; not attempted.
