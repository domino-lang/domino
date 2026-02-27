// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    gamehops::{
        equivalence::{error::Result, ResolvedClaim},
        GameHop,
    },
    package::Export,
};

pub(crate) mod indicatif;
#[cfg(test)]
pub(crate) mod mock;

pub trait UI {
    type ProveUI: ProveUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn prove_ui(&self) -> Self::ProveUI;
}

pub trait ProveUI {
    type ProveTheoremUI: ProveTheoremUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&self);
    fn finish(&self);

    fn start_theorem(&self, theorem_name: &str) -> Self::ProveTheoremUI;
}

pub trait ProveTheoremUI {
    type ProveGamehopUI: ProveGamehopUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn finish(&self);

    fn start_gamehop(&self, gamehop: &GameHop) -> Self::ProveGamehopUI;
}

pub trait ProveGamehopUI: Sync {
    type ProveOracleUI: ProveOracleUI;
    type ProveInvariantStartUI: ProveInvariantStartUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn is_reduction(&self);

    fn start(&mut self);
    fn finish(&self);

    fn start_oracle(&self, oracle: &Export) -> Self::ProveOracleUI;
    fn start_invariant_start(&self, start: String) -> Self::ProveInvariantStartUI;
}

pub trait ProveOracleUI: Send + Sync {
    type ProveClaimUI: ProveClaimUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>>;

    fn start_claim(&self, claim: &ResolvedClaim) -> Self::ProveClaimUI;
    fn start_injectivity(&self, claim: &str) -> Self::ProveClaimUI;
}

pub trait ProveInvariantStartUI: Send + Sync {
    type ProveClaimUI: ProveClaimUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>>;

    fn start_claim(&self, claim_name: &str) -> Self::ProveClaimUI;
}

pub trait ProveClaimUI: Send + Sync {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn run(self, fun: impl FnOnce() -> Result<()>) -> Result<()>;
}
