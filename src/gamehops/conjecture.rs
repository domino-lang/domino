// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::parser::ast::GameInstanceName;

#[derive(Debug, Clone)]
pub struct Conjecture<'a> {
    left_game: GameInstanceName<'a>,
    right_game: GameInstanceName<'a>,
}

impl<'a> Conjecture<'a> {
    pub fn new(left_game: GameInstanceName<'a>, right_game: GameInstanceName<'a>) -> Self {
        Self {
            left_game,
            right_game,
        }
    }
    pub(crate) fn left_name(&self) -> &GameInstanceName<'a> {
        &self.left_game
    }
    pub(crate) fn right_name(&self) -> &GameInstanceName<'a> {
        &self.right_game
    }
}
