// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    gamehops::{
        equivalence::{error::Result, ResolvedClaim},
        GameHop,
    },
    package::Export,
};

pub mod indicatif;

#[cfg(test)]
pub(crate) mod mock;

pub trait UI {
    type ProofstepUI: ProofstepUI;
    type ProveUI: ProveUI;
    type LatexUI: LatexUI;

    fn println(&self, line: &str) -> std::io::Result<()>;

    fn proofstep_ui(&self) -> Self::ProofstepUI;
    fn prove_ui(&self) -> Self::ProveUI;
    fn latex_ui(&self) -> Self::LatexUI;
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

pub trait ProofstepUI {
    fn println(&self, line: &str) -> std::io::Result<()>;
}

pub trait LatexUI {
    fn game_iterator<Item>(
        &self,
        iter: impl ExactSizeIterator<Item = Item>,
        caption: String,
    ) -> impl Iterator<Item = Item>;
}

pub trait LatexUIGameIterator<'ui, Item> {
    fn ui_iter(self, ui: &'ui impl LatexUI, caption: &str) -> impl Iterator<Item = Item>;
}

impl<'ui, S, T: ExactSizeIterator<Item = S>> LatexUIGameIterator<'ui, S> for T {
    fn ui_iter(self, ui: &'ui impl LatexUI, caption: &str) -> impl Iterator<Item = S> {
        ui.game_iterator(self, caption.to_string())
    }
}
