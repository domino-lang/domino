// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::ui::{ProveLemmaUI, ProveOracleUI, ProveProofstepUI, ProveTheoremUI, ProveUI, UI};

#[derive(Clone)]
pub struct TestUI {}

impl TestUI {
    pub fn new() -> Self {
        Self {}
    }
}

impl UI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn prove_ui(&self) -> impl ProveUI {
        self.clone()
    }
}

impl ProveUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&self) {}
    fn finish(&self) {}

    fn start_theorem(&self, _theorem_name: &str) -> impl ProveTheoremUI {
        self.clone()
    }
}

impl ProveTheoremUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}

    fn start_proofstep(&self, _proofstep_name: String) -> impl ProveProofstepUI {
        self.clone()
    }
}

impl ProveProofstepUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}

    fn is_reduction(&self) {}

    fn start_oracle(&self, _oracle_name: String) -> impl ProveOracleUI {
        self.clone()
    }
}

impl ProveOracleUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}

    fn start_lemma(&self, _lemma_name: &str) -> impl ProveLemmaUI {
        self.clone()
    }
}

impl ProveLemmaUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}
}
