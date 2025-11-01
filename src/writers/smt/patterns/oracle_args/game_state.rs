// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::game_ident::GameConstIdentifier,
    writers::smt::patterns::{
        DatastructurePattern as _, GameStatePattern as GameStateDatatypePattern,
    },
};

use super::*;

pub struct GameStatePattern<'a> {
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
}

impl OracleArgPattern for GameStatePattern<'_> {
    type Variant = OldNewVariant;

    fn global_const_name(&self, game_inst_name: &str, variant: &OldNewVariant) -> String {
        format!("<<game-state-{game_inst_name}-{variant}>>")
    }

    fn local_arg_name(&self) -> String {
        "<game-state>".to_string()
    }

    fn sort(&self) -> Sort {
        GameStateDatatypePattern {
            game_name: self.game_name,
            params: self.game_params,
        }
        .sort(vec![])
    }
}
