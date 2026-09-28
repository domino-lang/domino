// SPDX-License-Identifier: MIT OR Apache-2.0

use super::equivalence::Equivalence;
use super::reduction::Reduction;
use crate::parser::ast::GameInstanceName;

#[derive(Debug, Clone)]
pub struct Hybrid<'a> {
    hybrid_game: GameInstanceName<'a>,
    equivalence: Equivalence,
    reduction: Reduction<'a>,
    left_name: String,
    right_name: String,
    /// The loop variable's name in the hybrid instance declaration.
    loop_var: String,
}

impl<'a> Hybrid<'a> {
    pub fn new(
        hybrid_game: GameInstanceName<'a>,
        equivalence: Equivalence,
        reduction: Reduction<'a>,
        left_name: String,
        right_name: String,
        loop_var: String,
    ) -> Self {
        Self {
            hybrid_game,
            equivalence,
            reduction,
            left_name,
            right_name,
            loop_var,
        }
    }
    pub(crate) fn hybrid_name(&self) -> &GameInstanceName<'a> {
        &self.hybrid_game
    }
    pub(crate) fn equivalence(&self) -> &Equivalence {
        &self.equivalence
    }
    pub(crate) fn reduction(&self) -> &Reduction<'a> {
        &self.reduction
    }
    pub(crate) fn loop_var(&self) -> &str {
        &self.loop_var
    }
    pub(crate) fn left_name(&self) -> &str {
        &self.left_name
    }
    pub(crate) fn right_name(&self) -> &str {
        &self.right_name
    }
}
