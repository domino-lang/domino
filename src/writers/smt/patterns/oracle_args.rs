// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::Display;

use crate::writers::smt::declare;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::sorts::Sort;

mod game_consts;
mod game_state;
mod theorem_consts;

pub use game_consts::*;
pub use game_state::*;
pub use theorem_consts::*;

#[derive(Debug, Clone)]
pub enum OldNewVariant {
    Old,
    New { oracle_name: String },
}

impl Display for OldNewVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OldNewVariant::Old => write!(f, "old"),
            OldNewVariant::New { oracle_name } => write!(f, "new-{oracle_name}"),
        }
    }
}

pub trait OracleArgPattern {
    type Variant;

    fn global_const_name(&self, game_inst_name: &str, variant: &Self::Variant) -> String;
    fn local_arg_name(&self) -> String;
    fn sort(&self) -> Sort;

    fn declare(&self, game_inst_name: &str, variant: &Self::Variant) -> SmtExpr {
        declare::declare_const(self.global_const_name(game_inst_name, variant), self.sort())
    }

    fn define(
        &self,
        game_inst_name: &str,
        variant: &Self::Variant,
        term: impl Into<SmtExpr>,
    ) -> impl Into<SmtExpr> {
        declare::define_const(
            self.global_const_name(game_inst_name, variant),
            self.sort(),
            term,
        )
    }
}

pub trait OldNewOracleArgPattern: OracleArgPattern<Variant = OldNewVariant> {
    fn old_global_const_name(&self, game_inst_name: &str) -> String {
        self.global_const_name(game_inst_name, &OldNewVariant::Old)
    }

    fn new_global_const_name(&self, game_inst_name: &str, oracle_name: String) -> String {
        self.global_const_name(game_inst_name, &OldNewVariant::New { oracle_name })
    }

    fn declare_old(&self, game_inst_name: &str) -> SmtExpr {
        self.declare(game_inst_name, &OldNewVariant::Old)
    }

    fn declare_new(&self, game_inst_name: &str, oracle_name: String) -> SmtExpr {
        self.declare(game_inst_name, &OldNewVariant::New { oracle_name })
    }
}

/// OracleArgPattern where variant is unit
pub trait UnitOracleArgPattern: OracleArgPattern<Variant = ()> {
    fn unit_global_const_name(&self, game_inst_name: &str) -> String {
        <Self as OracleArgPattern>::global_const_name(self, game_inst_name, &())
    }

    fn unit_declare(&self, game_inst_name: &str) -> SmtExpr {
        <Self as OracleArgPattern>::declare(self, game_inst_name, &())
    }

    fn unit_define(&self, game_inst_name: &str, term: impl Into<SmtExpr>) -> impl Into<SmtExpr> {
        <Self as OracleArgPattern>::define(self, game_inst_name, &(), term)
    }
}

impl<T: OracleArgPattern<Variant = OldNewVariant>> OldNewOracleArgPattern for T {}
impl<T: OracleArgPattern<Variant = ()>> UnitOracleArgPattern for T {}
