// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{gamehops::GameHop, package::Export, theorem::Claim};

pub(crate) mod indicatif;
#[cfg(test)]
pub(crate) mod mock;

pub trait UI {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn prove_ui(&self) -> impl ProveUI;
}

pub trait ProveUI {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&self);
    fn finish(&self);

    fn start_theorem(&self, theorem_name: &str) -> impl ProveTheoremUI;
}

pub trait ProveTheoremUI {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn finish(&self);

    fn start_gamehop(&self, gamehop: &GameHop) -> impl ProveGamehopUI;
}

pub trait ProveGamehopUI: Sync {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn is_reduction(&self);

    fn start(&mut self);
    fn finish(&self);

    fn start_oracle(&self, oracle: &Export) -> impl ProveOracleUI;
}

pub trait ProveOracleUI: Send + Sync {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn finish(&self);

    fn start_claim(&self, claim: &Claim) -> impl ProveClaimUI;
}

pub trait ProveClaimUI: Send {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn success(&self);
    fn failure(&self);
}
