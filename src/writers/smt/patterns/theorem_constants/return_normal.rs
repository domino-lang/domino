use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    writers::smt::{
        patterns::{theorem_constants::ConstantPattern, DatastructurePattern, ReturnPattern},
        sorts::Sort,
    },
};

pub struct ReturnConst<'a> {
    pub game_inst_name: &'a str,
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],

    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],

    pub oracle_name: &'a str,
}

impl ConstantPattern for ReturnConst<'_> {
    fn name(&self) -> String {
        let Self {
            game_inst_name,
            oracle_name,
            ..
        } = self;

        format!("<return-{game_inst_name}-{oracle_name}>")
    }

    fn sort(&self) -> Sort {
        ReturnPattern {
            game_name: self.game_name,
            game_params: self.game_params,
            pkg_name: self.pkg_name,
            pkg_params: self.pkg_params,
            oracle_name: self.oracle_name,
        }
        .sort(vec![])
    }
}
