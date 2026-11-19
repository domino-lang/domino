// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    gamehops::{
        equivalence::{error::Result, ResolvedClaim},
        GameHop,
    },
    package::Export,
    theorem::{GameInstance, Theorem},
    ui::*,
};

#[derive(Clone)]
pub struct TestUI {}

impl TestUI {
    pub fn new() -> Self {
        Self {}
    }
}

impl UI for TestUI {
    type GamehopUI = TestUI;
    type ProveUI = TestUI;
    type LatexUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn gamehop_ui(&self) -> Self::GamehopUI {
        self.clone()
    }

    fn prove_ui(&self) -> Self::ProveUI {
        self.clone()
    }

    fn latex_ui(&self) -> Self::LatexUI {
        self.clone()
    }
}

impl ProveUI for TestUI {
    type ProveTheoremUI = TestUI;
    type ProveGamesUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&self) {}
    fn finish(&self) {}

    fn start_theorem(&self, _theorem_name: &str) -> Self::ProveTheoremUI {
        self.clone()
    }
    fn start_games(&self) -> Self::ProveGamesUI {
        self.clone()
    }
}

impl ProveGamesUI for TestUI {
    type ProveGameUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}
    fn skip(&self) {}

    fn start_game(&self, _game: &GameInstance) -> Self::ProveGameUI {
        self.clone()
    }
}
impl ProveTheoremUI for TestUI {
    type ProveGamehopUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self, _theorem: &Theorem) {}
    fn skip(&self) {}

    fn start_gamehop(&self, _gamehop_name: &GameHop) -> Self::ProveGamehopUI {
        self.clone()
    }
}

impl ProveGameUI for TestUI {
    type ProveGameClaimUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce(&Self) -> Result<()>) -> Result<()> {
        fun(&self)
    }

    fn start_claim(&self, _claim: &ResolvedClaim) -> Self::ProveGameClaimUI {
        self.clone()
    }
}

impl ProveGamehopUI for TestUI {
    type ProveGamehopOracleUI = TestUI;
    type ProveGamehopInvariantStartUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn start(&mut self) {}
    fn finish(&self) {}

    fn is_reduction(&self) {}

    fn start_oracle(&self, _oracle_name: &Export) -> Self::ProveGamehopOracleUI {
        self.clone()
    }
    fn start_invariant_start(&self, _oracle_name: String) -> Self::ProveGamehopInvariantStartUI {
        self.clone()
    }
}

impl ProveGamehopOracleUI for TestUI {
    type ProveGamehopClaimUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        fun(&self)
    }

    fn start_claim(&self, _claim: &ResolvedClaim) -> Self::ProveGamehopClaimUI {
        self.clone()
    }
    fn start_injectivity(&self, _claim: &str) -> Self::ProveGamehopClaimUI {
        self.clone()
    }
}
impl ProveGamehopInvariantStartUI for TestUI {
    type ProveGamehopClaimUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        fun(&self)
    }

    fn start_claim(&self, _claim: &str) -> Self::ProveGamehopClaimUI {
        self.clone()
    }
}

impl ProveGamehopClaimUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce() -> Result<()>) -> Result<()> {
        fun()
    }
}

impl ProveGameClaimUI for TestUI {
    type ProveGameOracleUI = TestUI;
    type ProveGameInvariantStartUI = TestUI;

    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        fun(&self)
    }

    fn start_oracle(&self, _oracle: &Export) -> Self::ProveGameOracleUI {
        self.clone()
    }
    fn start_invariant_start(&self) -> Self::ProveGameInvariantStartUI {
        self.clone()
    }
}

impl ProveGameInvariantStartUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce() -> Result<()>) -> Result<()> {
        fun()
    }
}

impl ProveGameOracleUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }

    fn run(self, fun: impl FnOnce() -> Result<()>) -> Result<()> {
        fun()
    }
}

impl GamehopUI for TestUI {
    fn println(&self, _line: &str) -> std::io::Result<()> {
        Ok(())
    }
}

impl LatexUI for TestUI {
    fn game_iterator<Item>(
        &self,
        iter: impl ExactSizeIterator<Item = Item>,
        _caption: String,
    ) -> impl Iterator<Item = Item> {
        iter
    }
}
