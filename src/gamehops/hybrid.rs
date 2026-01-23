// SPDX-License-Identifier: MIT OR Apache-2.0

use super::equivalence::Equivalence;
use super::reduction::Reduction;
use crate::parser::ast::GameInstanceName;

#[derive(Debug, Clone)]
pub struct Hybrid<'a> {
    hybrid_game: GameInstanceName<'a>,
    equivalence: Equivalence,
    reduction: Reduction<'a>,
}

impl<'a> Hybrid<'a> {
    pub fn new(
        hybrid_game: GameInstanceName<'a>,
        equivalence: Equivalence,
        reduction: Reduction<'a>,
    ) -> Self {
        Self {
            hybrid_game,
            equivalence,
            reduction,
        }
    }
    pub(crate) fn hybrid_name(&self) -> &GameInstanceName<'a> {
        &self.hybrid_game
    }
    pub(crate) fn equivalence(&self) -> &Equivalence {
        &self.equivalence
    }
    // pub(crate) fn right_name(&self) -> &GameInstanceName<'a> {
    //     &self.right_game
    // }
}
