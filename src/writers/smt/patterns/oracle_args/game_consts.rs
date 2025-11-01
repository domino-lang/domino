// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::writers::smt::patterns::{
    game_consts::GameConstsPattern as GameConstsDatatypePattern, DatastructurePattern as _,
};

use super::*;

pub struct GameConstsPattern<'a> {
    pub game_name: &'a str,
}

impl OracleArgPattern for GameConstsPattern<'_> {
    type Variant = ();

    fn global_const_name(&self, game_inst_name: &str, _variant: &()) -> String {
        format!("<<game-consts-{game_inst_name}>>")
    }

    fn local_arg_name(&self) -> String {
        "<game-consts>".to_string()
    }

    fn sort(&self) -> Sort {
        GameConstsDatatypePattern {
            game_name: self.game_name,
        }
        .sort(vec![])
    }
}
