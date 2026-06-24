# KEM-DEM

This directory consists of four formalization of the KEM-DEM paradigm for constructing 
hybrid public key encryption schemes. The following table summarizes the 
assumptions, security notions, proof structure, as well as a corresponding proof
in EasyCrypt for easier comparison. The corresponding EasyCrypt proof for each 
formalization live in a subdirectory called `easycrypt`.

| Project | Security Notion | Strategy | KEM Assumption | DEM Assumption | PKE Security | EasyCrypt Proof | EasyCrypt Source |
| - | - | - | - | - | - | - | - |
| `kem-dem-cca-security-ssp` | CCA | Full SSP | Single challenge | One-time secrecy , multi-challenge | Single Challenge | - | - |
| `kem-dem-cca-security` | CCA | Blended with parallel hops | Single challenge | One-time secrecy , single-challenge | Single Challenge | `easycrypt/Dominofied_KEMDEM.ec` | - |
| `kem-dem-cca-security-easycrypt` | CCA | Blended with redundant hops | Single challenge | One-time secrecy , single-challenge | Single Challenge | `easycrypt/Tutorial_KEMDEM.ec` | (https://gitlab.com/fdupress/easycrypt-tutorial/-/blob/main/kemdem/KEMDEM_CCA.ec)[EasyCrypt Tutorial on François Dupressoir's GitLab] |
| `kem-dem-cpa-security-single-challenge` | CPA | Blended with parallel hops | Single challenge | One-time secrecy , single-challenge | Single Challenge | `easycrypt/KEMDEM_lor.ec` | (https://github.com/proof-ladders/asymmetric-ladder/tree/main/kemdem/EasyCrypt/left-or-right)[Proof Ladders Project GitHub] |
| `kem-dem-cpa-security-multi-challenge` | CPA | Blended with parallel hops | Multi challenge | One-time secrecy , multi-challenge | Multi Challenge | `easycrypt/KEMDEM_CPA.ec` | (https://github.com/proof-ladders/asymmetric-ladder/tree/main/kemdem/EasyCrypt/multi-challenge)[Proof Ladders Project GitHub] |
