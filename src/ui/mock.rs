// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    gamehops::{
        equivalence::{error::Result, ResolvedClaim},
        GameHop,
    },
    package::Export,
    ui::{
        ProveClaimUI, ProveGamehopUI, ProveInvariantStartUI, ProveOracleUI, ProveTheoremUI,
        ProveUI, UI,
    },
};

#[derive(Clone)]
pub struct TestUI {}

impl TestUI {
    pub fn new() -> Self {
        Self {}
    }
}

impl UI for TestUI {
    type ProveUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn prove_ui(&self) -> Self::ProveUI {
        self.clone()
    }
}

impl ProveUI for TestUI {
    type ProveTheoremUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&self) {}
    fn finish(&self) {}

    fn start_theorem(&self, _theorem_name: &str) -> Self::ProveTheoremUI {
        self.clone()
    }
}

impl ProveTheoremUI for TestUI {
    type ProveGamehopUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}

    fn start_gamehop(&self, _gamehop_name: &GameHop) -> Self::ProveGamehopUI {
        self.clone()
    }
}

impl ProveGamehopUI for TestUI {
    type ProveOracleUI = TestUI;
    type ProveInvariantStartUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}

    fn is_reduction(&self) {}

    fn start_oracle(&self, _oracle_name: &Export) -> Self::ProveOracleUI {
        self.clone()
    }
    fn start_invariant_start(&self, _oracle_name: String) -> Self::ProveInvariantStartUI {
        self.clone()
    }
}

impl ProveOracleUI for TestUI {
    type ProveClaimUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        fun(&self)
    }

    fn start_claim(&self, _claim: &ResolvedClaim) -> Self::ProveClaimUI {
        self.clone()
    }
    fn start_injectivity(&self, _claim: &str) -> Self::ProveClaimUI {
        self.clone()
    }
}
impl ProveInvariantStartUI for TestUI {
    type ProveClaimUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        fun(&self)
    }

    fn start_claim(&self, _claim: &str) -> Self::ProveClaimUI {
        self.clone()
    }
}

impl ProveClaimUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce() -> Result<()>) -> Result<()> {
        fun()
    }
}
