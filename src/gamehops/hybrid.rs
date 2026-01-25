// SPDX-License-Identifier: MIT OR Apache-2.0

use super::equivalence::Equivalence;
use super::reduction::Reduction;
use crate::parser::ast::GameInstanceName;

#[derive(Debug, Clone)]
pub struct Hybrid<'a> {
    hybrid_game: GameInstanceName<'a>,
    equivalence: Equivalence,
    #[allow(unused)]
    reduction: Reduction<'a>,
    left_name: String,
    right_name: String,
}

impl<'a> Hybrid<'a> {
    pub fn new(
        hybrid_game: GameInstanceName<'a>,
        equivalence: Equivalence,
        reduction: Reduction<'a>,
        left_name: String,
        right_name: String,
    ) -> Self {
        Self {
            hybrid_game,
            equivalence,
            reduction,
            left_name,
            right_name,
        }
    }
    pub(crate) fn hybrid_name(&self) -> &GameInstanceName<'a> {
        &self.hybrid_game
    }
    pub(crate) fn equivalence(&self) -> &Equivalence {
        &self.equivalence
    }
    pub(crate) fn left_name(&self) -> &str {
        &self.left_name
    }
    pub(crate) fn right_name(&self) -> &str {
        &self.right_name
    }
}
