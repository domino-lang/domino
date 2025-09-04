use crate::writers::smt::patterns::{
    theorem_consts::TheoremConstsPattern as TheoremConstsDatatypePattern, DatastructurePattern as _,
};

use super::*;

pub struct TheoremConstsPattern<'a> {
    pub theorem_name: &'a str,
}

impl OracleArgPattern for TheoremConstsPattern<'_> {
    type Variant = ();

    fn global_const_name(&self, _game_inst_name: &str, _variant: &()) -> String {
        "<<theorem-consts>>".to_string()
    }

    fn local_arg_name(&self) -> String {
        "<theorem-consts>".to_string()
    }

    fn sort(&self) -> Sort {
        TheoremConstsDatatypePattern {
            theorem_name: self.theorem_name,
        }
        .sort(vec![])
    }
}
