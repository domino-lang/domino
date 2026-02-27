// SPDX-License-Identifier: MIT OR Apache-2.0

pub mod indicatif;
#[cfg(test)]
pub(crate) mod mock;

pub trait UI {
    fn println(&self, line: &str) -> std::io::Result<()>;

    fn prove_ui(&self) -> impl ProveUI;
    fn latex_ui(&self) -> impl LatexUI;
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

pub trait LatexUI {
    fn game_iterator<'ui, Item>(
        &'ui self,
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
