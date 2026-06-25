# KEM-DEM

This directory contains 5 formalizations of the KEM-DEM paradigm for constructing hybrid public key encryption schemes. One proof is written in (https://eprint.iacr.org/2018/306)[state-separating proofs (SSP) style], and 4 proofs are written using the (https://eprint.iacr.org/2025/1569)[blended approach]. The 4 proofs in blended style were written to match analogous EasyCrypt proofs, and each of the 4 proof folders has a subdirectory called `easycrypt` which contains the analogous EasyCrypt proof. The following table summarizes the assumptions, security notions, proof structure, as well as the source of the corresponding EasyCrypt proof.

In the table, multi-instance refers to multiple keys in the game, and multi-challenge refers to multiple encryption queries.

| Project | PKE Security | Strategy | KEM Assumption | DEM Assumption | EasyCrypt Proof | EasyCrypt Source |
| - | - | - | - | - | - | - |
| `kem-dem-cca-ssp` | Single Challenge CCA | Full SSP | Single challenge CCA | Single-instance One-time CCA |  - | - |
| `kem-dem-cca-blended-parallel` | Single Challenge CCA | Blended with parallel hops | Single challenge CCA | Single-instance One-time CCA | `easycrypt/Dominofied_KEMDEM.ec` | - |
| `kem-dem-cca-blended-redundant` | Single Challenge CCA | Blended with redundant hops | Single challenge CPA | Single-instance One-time CCA | `easycrypt/Tutorial_KEMDEM.ec` | (https://gitlab.com/fdupress/easycrypt-tutorial/-/blob/main/kemdem/KEMDEM_CCA.ec)[EasyCrypt Tutorial on François Dupressoir's GitLab] |
| `kem-dem-cpa-blended-parallel-single-challenge` | Single challenge CPA (i.e. single encryption challenge) | Blended with parallel hops | Single challenge CPA (i.e. single encapsulation challenge) | Single-instance One-time CPA | `easycrypt/KEMDEM_lor.ec` | (https://github.com/proof-ladders/asymmetric-ladder/tree/main/kemdem/EasyCrypt/left-or-right)[Proof Ladders Project GitHub] |
| `kem-dem-cpa-blended-parallel-multi-challenge` | Multi challenge CPA (i.e. multiple encryption challenges) | Blended with parallel hops  | Multi challenge CPA (i.e. multiple encapsulation challenges) | Multi-instance One-time CPA (i.e. multiple one-time CPA encryption challenges under fresh keys) | `easycrypt/KEMDEM_CPA.ec` | (https://github.com/proof-ladders/asymmetric-ladder/tree/main/kemdem/EasyCrypt/multi-challenge)[Proof Ladders Project GitHub] |
