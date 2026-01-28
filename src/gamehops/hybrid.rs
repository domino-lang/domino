// SPDX-License-Identifier: MIT OR Apache-2.0

use super::equivalence::Equivalence;
use crate::parser::ast::GameInstanceName;

#[derive(Debug, Clone)]
pub struct Hybrid<'a> {
    hybrid_game: GameInstanceName<'a>,
    equivalence: Equivalence,
}

impl<'a> Hybrid<'a> {
    pub fn new(hybrid_game: GameInstanceName<'a>, equivalence: Equivalence) -> Self {
        Self {
            hybrid_game,
            equivalence,
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
