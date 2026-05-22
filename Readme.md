Supplementary Material for the CRYPTO 2026 Submission
===

This Readme contains condensed information for CRYPTO 2026 reviewers. For the regular Readme, refer to [Readme.project.md](./Readme.project.md)

## Setup

To run Domino on your machine, you need

 - CVC5 version 1.3 -- https://cvc5.github.io/
 - Recent rust and cargo -- https://rustup.rs/

You can opt to *install* Domino by running 
```
cargo install --path crates/domino
```

or run it directly using cargo 
```
cargo run -p domino
```

within the provided folder

## Web version

Alternatively to an installation, there is a Web version at https://dainty-froyo-12acd5.netlify.app/. The website also provides prepared archives for all the example projects. While this works well for simple projects, the web version reaches its limits when verifying, for example, the full 4-Way Handshake and is noticeably slower.

The web interface in this submission is still extremely basic. It does allow running Domino on a project of your choice, but no further options to inspect projects or make changes. To use it, first upload a zip'ed Domino project, and then choose either the "proofsteps" or "prove" buttons.

## Case Studies from the Submission

### 4-Way Handshake

The Domino project for 4WHS is located in `example-projects/4WHS` and contains both the simplified and full proof. In particular, games associated with the simplified version are named `games/Hybrid{0..3}` while the games associated with the full version are named `games/H{0..7}`. The invariant specifications are located in `theorem/simple` and `theorem/full` respectively. 

In the folder `_build/latex` you can find automated pdf exports of the projects. The LaTeX source can be recreated using `domino latex` (resp. `cargo run -p domino latex`).

Running `domino prove` (resp. `cargo run -p domino prove`) in that folder will verify both simplified and the full 4-Way Handshake security. You can choose to limit Domino to either proof by passing `--proof Full4WHS` (resp. `--proof Simple4WHS`). For further options, we refer to the output of `--help`.

Making use of parallel solving (`--parallel 12`), Simple4WHS takes less than a minute on a modern notebook, while Full4WHS takes around 40 minutes.

### Yao's Garbling Scheme

There are three main theorem files:
1. HybridCircuitSecurity is the generalized hybrid argument with the three main hybrid proof steps. It proves $CoreReal$ ~ $CoreIdeal$ where $CoreReal = SEC^0_d$ and $CoreIdeal = SEC^1_d$. (`invariant-CoreReal-HybridReal.smt2` for the hybrid start, `invariant-HybridIdeal-HybridReal1.smt2` for hybrid step, and `invariant-CoreIdeal-HybridIdeal.smt2` for hybrid end)
2. Yao3Layer reduces the security of 3-layer circuit security to layer assumptions by three reduction game hops outlined in section 5.
3. LayerSecurity is the layer assumption (invariants: invariant-Layer.smt2)
4. Yao reduces Yao's circuit security to hybrid circuit security with straight line reduction. Yao circuit security games expose a single oracle GARBLE for garbling the entire circuit.
    
Estimated proof times: 
1. HybridCircuitSecuirty = 10 (start) + 30 (step) + 5 (end) minutes
2. LayerSecurity = 30 seconds
