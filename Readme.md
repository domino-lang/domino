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

### `cvc5-lib` feature (native cvc5 backend)

The interactive `domino debug` command talks to cvc5 through the [`cvc5`](https://crates.io/crates/cvc5)
crate (in-process bindings) instead of a child process. This lives behind the **optional
`cvc5-lib` cargo feature** and is **not** part of a default build — `cargo build --workspace` needs
nothing extra and does not pull in `cvc5`.

Building `--features cvc5-lib` needs two things bindgen and the linker have to find:

1. a prebuilt **static cvc5** (`libcvc5.a`, `libcvc5parser.a` and the C API headers), pointed at by
   `CVC5_LIB_DIR` / `CVC5_INCLUDE_DIR`. We use the crate's `static` feature but *skip* its
   build-from-source path (which would need CMake and a cvc5 checkout) by setting `CVC5_LIB_DIR`.
2. a working **libclang** for bindgen (`LIBCLANG_PATH`, plus `BINDGEN_EXTRA_CLANG_ARGS` if the
   libclang you use ships no builtin headers).

The helper script fetches both into `~/.cache/domino` and writes an env file:

```bash
scripts/setup-cvc5-lib.sh
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
cargo test  --workspace --features cvc5-lib
```

Nix users: `nix develop .#cvc5-lib` provides the toolchain + libclang (and sets `LIBCLANG_PATH`);
still run `scripts/setup-cvc5-lib.sh` once for the prebuilt static cvc5.

## Usage

Enter a project directory and run `domino prove`.
To get an idea how a project is structured, see the `example-projects/hello-world` directory (sorry, proper documentation is on the roadmap).

To generate LaTeX for a project, use `domino latex`. The output will be in `_build/latex`, relative to the project root.

## Model

At the lowest level, there are _packages_, which can expose oracles (exports) and call oracles on other packages (imports). A package has both _state_ and _constant parameters_. One layer higher there are _games_, which instantiate packages into package instance and assign which oracle is called for every import. A game also has constant parameters that can be assigned to package constant parameters during instantiation. At the highest layer there are proofs, which instantiate games and describe hops between these. There are reduction game hops, which are graph-based arguments based on an assumption, and equivalence game hops, where we use an SMT solver to show that two games behave identically.

## Roadmap

- [ ] Improve Documentation
- [ ] Improve Error Reporting
- [ ] Editor/LSP support
- [ ] Automatically Determine Advantage Terms
- [ ] Type parameters - in instantiations, allow not just assigning constants, but also types.
- [ ] Automatically find invariants for equivalence proofs.

[rustup]: https://rustup.rs/
