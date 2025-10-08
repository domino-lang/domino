use crate::{
    types::Type,
    writers::smt::{patterns::theorem_constants::ConstantPattern, sorts::Sort},
};

pub struct ReturnValueConst<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub ty: &'a Type,
}

impl ConstantPattern for ReturnValueConst<'_> {
    fn name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        format!("return-value-{game_inst_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn sort(&self) -> Sort {
        let inner_sort = self.ty.clone().into();
        Sort::Other("ReturnValue".to_string(), vec![inner_sort])
    }
}
