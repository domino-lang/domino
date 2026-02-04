# Domino

`Domino` is a tool that helps you manage the tedious parts of working with the State-Separation Proofs framework for doing crypto proofs.

> **This project is in early alpha. Expect insufficient documentation and bugs, bugs, bugs!**

## Features

- Handle packages, games and proofs in a custom language close to pseudocode
- Type-check oracle code and wiring between packages
- Check that reduction game hops are valid
- Use SMT solvers to show equivalence of games with different code
  - This requires hand-writing invariants in SMT-LIB, but not proving them.
- Generate LATeX cryptocode and diagrams

## Installation

Requirements:

- A somewhat recent Rust toolchain. If you don't have that, look into [rustup].
- CVC5 installed and in the `PATH` (not needed for building domino, but for running it)

Install the tool using `cargo install --git https://github.com/domino-lang/domino domino`.
Ensure that the installed binary is in your `PATH`. (By default, Cargo installs to (`~/.cargo/bin`).)

## Usage

Enter a project directory and run `domino prove`.
To get an idea how a project is structured, see the `example-projects/hello-world` directory (sorry, proper documentation is on the roadmap).

To generate LaTeX for a project, use `domino latex`. The output will be in `_build/latex`, relative to the project root.

## Model

At the lowest level, there are _packages_, which can expose oracles (exports) and call oracles on other packages (imports). A package has both _state_ and _constant parameters_. One layer higher there are _games_, which instantiate packages into package instance and assign which oracle is called for every import. A game also has constant parameters that can be assigned to package constant parameters during instantiation. At the highest layer there are proofs, which instantiate games and describe hops between these. There are reduction game hops, which are graph-based arguments based on an assumption, and equivalence game hops, where we use an SMT solver to show that two games behave identically.

## Soundness Gaps

Right now, the tool does the hard parts of equivalence proofs, but so far two properties have to be checked manually:

- **Invariant Induction Base Case**: The left and right base state are equivalent according to the equivalence relation of the invariant.
- **Injectivity of Randomness Mapping**: The randomness mapping describes which random values in the left and right game should be equivalent. In order to ensure that the random values are not e.g. all constrained to be the same value, this check needs to be done.

## Roadmap

- [ ] Fix Remaining Soundness Gaps
- [ ] Improve Documentation
- [ ] Improve Error Reporting
- [ ] Editor/LSP support
- [ ] Close Soundness Gaps
- [ ] Automatically Determine Advantage Terms
- [ ] Type parameters - in instantiations, allow not just assigning constants, but also types.
- [ ] Automatically find invariants for equivalence proofs.

[rustup]: https://rustup.rs/
