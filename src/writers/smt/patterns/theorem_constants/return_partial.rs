use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    writers::smt::{
        patterns::{theorem_constants::ConstantPattern, DatastructurePattern, PartialReturnPattern},
        sorts::Sort,
    },
};

pub struct PartialReturnConst<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub game_name: &'a str,
    pub pkg_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
}

impl<'a> ConstantPattern for PartialReturnConst<'a> {
    fn name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        format!("<partial-return-{game_inst_name}-{pkg_inst_name}-{oracle_name}>")
    }

    fn sort(&self) -> Sort {
        let Self {
            oracle_name,
            game_name,
            pkg_name,
            game_params,
            pkg_params,
            ..
        } = self;

        PartialReturnPattern {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        }
        .sort(vec![])
    }
}
