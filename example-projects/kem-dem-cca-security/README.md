# KEM-DEM

This project formalizes a result by Cramer and Shoup in
Domino which states that the composition of a CCA-secure Key Encapsulation
Mechanism (KEM) with a CCA-secure Data Encapsulation Mechanism (DEM) yields a
CCA-secure public key encryption (PKE) scheme. This formalization uses the
State Separating Proofs (SSP) framework and closely resembles the proof of the
same result in Section 4 of the work by Bruzska, Delignat-Lavaud Fournet,
Kohbrok, and Kohlweiss [[1]]. Full breakdown and explanation of this
formalization along with a general tutorial of Domino exists in the
Master's thesis of Amirhosein Rajabi at Aalto University [[2]].

There are two key differences with the proof introduced in [[1]]:

1. Stateless packages are used for the KEM and DEM schemes as well as the
   candidate PKE scheme.
2. Only DEM and key packages have the idealization bit while the original paper
   uses the idealization parameter for KEM and DEM packages.

[1]: https://eprint.iacr.org/2018/306
[2]: https://aaltodoc.aalto.fi/items/d68b77e6-3396-4728-9c05-88a9ca90398f

## Project structure

A Domino project contains en empty file `ssp.toml` at the root of the project
along with three subdirectories `proofs`, `packages`, and `games`, which
respectively contain the proofs to be verified, SSP package definition, and
security games as package compositions. The proof file `proofs/proof.ssp`
contains instances of the security games and game hops to be verified by Domino.
See the comments in the file for more explanation of the game hops.

## How to run the verification?

You need a working Rust installation as well as having cvc5 installed and in the `PATH`.
Install Domino using `cargo install --git https://github.com/domino-lang/domino domino`.
Ensure that it is in your `PATH`. Then, run `domino prove` inside the Domino project (i.e. this directory).
You will see 5 game hops are verified. (3 reductions and 2 code equivalences)

Use `--transcript` or `-t` option to generate the proof obligations in SMT-LIB language.
This option saves the SMT2 code that is fed into the SMT solver (cvc5) as files.
Domino stores an SMT2 file for each code equivalence game hop in `_build/code_eq`
(relative to the project root).

You can also generate a LaTeX export of the composition diagrams and pseudocode of
the packages by running `domino latex`. LaTeX files are generated in `_build/latex`
(again relative to the project root).
