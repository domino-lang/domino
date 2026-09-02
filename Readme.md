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

### `cvc5-lib` feature (native cvc5 backend, required for `domino debug`)

The interactive `domino debug` command talks to cvc5 through the [`cvc5`](https://crates.io/crates/cvc5)
crate (in-process bindings) instead of a child process. This lives behind the **optional
`cvc5-lib` cargo feature** and is **not** part of a default build — `cargo build --workspace` needs
nothing extra and does not pull in `cvc5`. This also means `domino debug` does not work unless you
build (and run!) with `--features cvc5-lib` — see the exact commands below. Running the plain
`cargo build`/`cargo run -p domino` binary against `debug` prints a reminder of this and exits;
it does not silently fall back to anything.

Supported platforms: **Linux** (x86_64, arm64) and **macOS** (x86_64, arm64/Apple Silicon).

Building `--features cvc5-lib` needs two things bindgen and the linker have to find:

1. a prebuilt **static cvc5** (`libcvc5.a`, `libcvc5parser.a` and the C API headers), pointed at by
   `CVC5_LIB_DIR` / `CVC5_INCLUDE_DIR`. We use the crate's `static` feature but *skip* its
   build-from-source path (which would need CMake and a cvc5 checkout) by setting `CVC5_LIB_DIR`.
2. a working **libclang** for bindgen (`LIBCLANG_PATH`, plus `BINDGEN_EXTRA_CLANG_ARGS` if the
   libclang you use ships no builtin headers). On macOS this is the `libclang.dylib` that ships
   with Xcode / the Command Line Tools (`xcode-select --install` if you don't have either yet).

The helper script fetches/locates both (into `~/.cache/domino` on Linux; it reuses the system
libclang on macOS) and writes an env file. **Re-run it whenever you switch machines/OS** — the env
file it writes is platform-specific and isn't portable between e.g. Linux and macOS checkouts:

```bash
scripts/setup-cvc5-lib.sh
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
cargo test  --workspace --features cvc5-lib
```

Nix users: `nix develop .#cvc5-lib` provides the toolchain + libclang (and sets `LIBCLANG_PATH`);
still run `scripts/setup-cvc5-lib.sh` once for the prebuilt static cvc5.

**If `CVC5_LIB_DIR` isn't set, the build does *not* fail with a clear error.** The `cvc5` crate
silently falls back to cloning cvc5 from GitHub and building it from source with CMake, which most
setups don't have installed. So if `cargo build --features cvc5-lib` fails with something like:

```
cvc5 source not found — cloning tag cvc5-... from GitHub...
.../configure.sh: line 525: cmake: command not found
thread 'main' panicked ...: cvc5 configure.sh failed
```

it means the env vars aren't set **in the shell you just ran that build in** — you either haven't
run `scripts/setup-cvc5-lib.sh` yet, or you forgot to `source ~/.cache/domino/cvc5-lib-env.sh` in
this particular terminal (sourcing doesn't persist across shells/terminal tabs — run it again).

#### Actually running `domino debug`

`source`ing the env file only lasts for the current shell, so do it again in every new terminal
before building or running with `cvc5-lib`. The feature also has to be passed to `cargo run`, not
just `cargo build` — `cargo run -p domino debug` (no `--features`, no `--`) builds the
`cvc5-lib`-less binary and passes `debug` as a `cargo` argument, not a `domino` one, so it won't
do what you want. Use:

```bash
source ~/.cache/domino/cvc5-lib-env.sh   # once per shell
cargo run -p domino --features cvc5-lib -- debug \
  --proof <THEOREM> --proofstep <N> --oracle <ORACLE> --claim <CLAIM>
```

`--proof`/`--proofstep`/`--oracle`/`--claim` describe which equivalence proofstep and claim to
debug; run `domino proofsteps` (also needs `-p domino -- proofsteps`, no `cvc5-lib` required) from
inside a project directory to list the valid `--proof`/`--proofstep` values.

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
