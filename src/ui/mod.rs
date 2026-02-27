// SPDX-License-Identifier: MIT OR Apache-2.0

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

    fn start_proofstep(&self, proofstep_name: String) -> impl ProveProofstepUI;
}

pub trait ProveProofstepUI: Sync {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn finish(&self);

    fn is_reduction(&self);

    fn start_oracle(&self, oracle_name: String) -> impl ProveOracleUI;
}

pub trait ProveOracleUI: Send {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn finish(&self);

    fn start_lemma(&self, lemma_name: &str) -> impl ProveLemmaUI;
}

pub trait ProveLemmaUI {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn start(&mut self);
    fn finish(&self);
}
