use crate::{
    expressions::Expression,
    identifier::pkg_ident::PackageConstIdentifier,
    writers::smt::{
        patterns::{
            datastructures::IntermediateStatePattern, theorem_constants::ConstantPattern,
            DatastructurePattern,
        },
        sorts::Sort,
    },
};

pub struct IntermediateStateConst<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
    pub variant: &'a str,
}

impl<'a> ConstantPattern for IntermediateStateConst<'a> {
    fn name(&self) -> String {
        let Self {
            game_inst_name,
            oracle_name,
            variant,
            ..
        } = self;

        format!("<intermediate-state-{game_inst_name}-{oracle_name}-{variant}>")
    }

    fn sort(&self) -> Sort {
        let Self {
            pkg_name,
            pkg_params,
            oracle_name,
            ..
        } = self;

        IntermediateStatePattern {
            pkg_name,
            params: pkg_params,
            oracle_name,
        }
        .sort(vec![])
    }
}
