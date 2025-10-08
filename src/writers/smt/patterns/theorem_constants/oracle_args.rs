use crate::{
    types::Type,
    writers::smt::{patterns::theorem_constants::ConstantPattern, sorts::Sort},
};

#[derive(Clone, Debug)]
pub struct OracleArgs<'a> {
    pub oracle_name: &'a str,
    pub arg_name: &'a str,
    pub arg_type: &'a Type,
}

impl ConstantPattern for OracleArgs<'_> {
    fn name(&self) -> String {
        let Self {
            oracle_name,
            arg_name,
            ..
        } = self;

        format!("<arg-{oracle_name}-{arg_name}>")
    }

    fn sort(&self) -> Sort {
        self.arg_type.clone().into()
    }
}
