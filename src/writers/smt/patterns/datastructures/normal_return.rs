use super::{DatastructurePattern, DatastructureSpec};
use crate::expressions::Expression;
use crate::identifier::game_ident::GameConstIdentifier;
use crate::identifier::pkg_ident::PackageConstIdentifier;
use crate::types::Type;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::patterns::instance_names::{encode_params, only_non_function_expression};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReturnPattern<'a> {
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub struct ReturnConstructor;

#[derive(PartialEq, Eq)]
pub enum ReturnSelector<'a> {
    GameState,
    ReturnValueOrAbort { return_type: &'a Type },
}

impl<'a> DatastructurePattern<'a> for ReturnPattern<'a> {
    type Constructor = ReturnConstructor;
    type Selector = ReturnSelector<'a>;
    type DeclareInfo = Type;

    const CAMEL_CASE: &'static str = "OracleReturn";
    const KEBAB_CASE: &'static str = "oracle-return";

    fn sort_name(&self) -> String {
        let camel_case = ReturnPattern::CAMEL_CASE;
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            game_params,
            pkg_params,
        } = self;

        let game_encoded_params = encode_params(only_non_function_expression(*game_params));
        let pkg_encoded_params = encode_params(only_non_function_expression(*pkg_params));
        format!("<{camel_case}-{game_name}-{game_encoded_params}-{pkg_name}-{pkg_encoded_params}-{oracle_name}>")
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            ..
        } = self;

        let game_encoded_params = encode_params(only_non_function_expression(self.game_params));
        let pkg_encoded_params = encode_params(only_non_function_expression(self.pkg_params));

        format!("<mk-{kebab_case}-{game_name}-{game_encoded_params}-{pkg_name}-{pkg_encoded_params}-{oracle_name}>")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            ..
        } = self;

        let game_encoded_params = encode_params(only_non_function_expression(self.game_params));
        let pkg_encoded_params = encode_params(only_non_function_expression(self.pkg_params));

        let field_name = match sel {
            ReturnSelector::GameState => "game-state",
            ReturnSelector::ReturnValueOrAbort { .. } => "return-value-or-abort",
        };

        format!("<{kebab_case}-{game_name}-{game_encoded_params}-{pkg_name}-{pkg_encoded_params}-{oracle_name}-{field_name}>")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let field_name = match sel {
            ReturnSelector::GameState => "game-state",
            ReturnSelector::ReturnValueOrAbort { .. } => "return-value-or-abort",
        };

        format!("match-{field_name}")
    }

    fn datastructure_spec(&self, return_type: &'a Type) -> DatastructureSpec<'a, Self> {
        DatastructureSpec(vec![(
            ReturnConstructor,
            vec![
                ReturnSelector::GameState,
                ReturnSelector::ReturnValueOrAbort { return_type },
            ],
        )])
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        let Self {
            game_name,
            game_params,
            ..
        } = self;

        let game_state_pattern = super::game_state::GameStatePattern {
            game_name,
            params: game_params,
        };

        match sel {
            ReturnSelector::GameState => game_state_pattern.sort(vec![]).into(),
            ReturnSelector::ReturnValueOrAbort { return_type } => {
                ("ReturnValue", *return_type).into()
            }
        }
    }
}

impl ReturnPattern<'_> {
    pub fn global_const_name(&self) -> String {
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            ..
        } = self;

        let game_encoded_params = encode_params(only_non_function_expression(self.game_params));
        let pkg_encoded_params = encode_params(only_non_function_expression(self.pkg_params));

        format!("<!return-{game_name}-{game_encoded_params}-{pkg_name}-{pkg_encoded_params}-{oracle_name}>")
    }
}
