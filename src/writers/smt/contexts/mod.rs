// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::writers::smt::{exprs::SmtExpr, names};

pub struct GlobalContext;

impl GlobalContext {
    pub fn smt_latest_gamestate() -> SmtExpr {
        ("select", names::var_globalstate_name()).into()
    }
}

mod equivalence;
mod game_inst;
mod oracle;
mod pkg_inst;

pub use equivalence::EquivalenceContext;
pub use game_inst::GameInstanceContext;
pub use oracle::OracleContext;
pub use pkg_inst::PackageInstanceContext;
