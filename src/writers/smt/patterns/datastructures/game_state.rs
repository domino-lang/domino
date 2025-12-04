// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::game_ident::GameConstIdentifier,
    theorem::GameInstance,
    transforms::samplify::{Position as SamplePosition, SampleInfo},
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        names::{Delimiter, FunctionNameBuilder, NameBuilderStage, NameSection, SortNameBuilder},
        patterns::{
            instance_names::{encode_params, only_ints},
            DatastructurePattern, DatastructureSpec, PackageStatePattern,
        },
        sorts::Sort,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GameStatePattern<'a> {
    pub game_name: &'a str,
    pub params: &'a [(GameConstIdentifier, Expression)],
}

#[derive(Debug, PartialEq, Eq)]
pub enum GameStateSelector<'a> {
    PackageInstance { pkg_inst_name: &'a str, sort: Sort },
    // Box'ed to reduce size of enum variant
    Randomness { sample_pos: Box<SamplePosition> },
}

impl<'a> NameSection for GameStateSelector<'a> {
    fn push_into<Delim, Stage>(
        &self,
        builder: crate::writers::smt::names::NameBuilder<Delim, Stage>,
    ) -> crate::writers::smt::names::NameBuilder<Delim, crate::writers::smt::names::NotEmpty>
    where
        Delim: Delimiter,
        Stage: NameBuilderStage,
    {
        match self {
            GameStateSelector::PackageInstance { pkg_inst_name, .. } => {
                builder.push("pkgstate").push(pkg_inst_name)
            }
            GameStateSelector::Randomness { sample_pos } => {
                builder.push("rand").extend(sample_pos.as_ref())
            }
        }
    }
}

#[derive(Debug)]
pub struct GameStateDeclareInfo<'a> {
    pub(crate) game_inst: &'a GameInstance,
    pub sample_info: &'a SampleInfo,
}

impl<'a> DatastructurePattern<'a> for GameStatePattern<'a> {
    type Constructor = ();
    type Selector = GameStateSelector<'a>;
    type DeclareInfo = GameStateDeclareInfo<'a>;

    const CAMEL_CASE: &'static str = "GameState";
    const KEBAB_CASE: &'static str = "game";

    fn sort_name(&self) -> String {
        let encoded_params = encode_params(only_ints(self.params));

        SortNameBuilder::new()
            .push(Self::CAMEL_CASE)
            .push(self.game_name)
            .maybe_extend(&encoded_params)
            .build()
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let encoded_params = encode_params(only_ints(self.params));

        FunctionNameBuilder::new()
            .push("mk")
            .push(Self::KEBAB_CASE)
            .push(self.game_name)
            .maybe_extend(&encoded_params)
            .build()
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let encoded_params = encode_params(only_ints(self.params));

        FunctionNameBuilder::new()
            .push(Self::KEBAB_CASE)
            .push(self.game_name)
            .maybe_extend(&encoded_params)
            .extend(sel)
            .build()
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        FunctionNameBuilder::new().push("match").extend(sel).build()
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        match sel {
            GameStateSelector::PackageInstance { sort, .. } => sort.clone().into(),
            GameStateSelector::Randomness { .. } => Type::Integer.into(),
        }
    }

    fn datastructure_spec(&self, info: &Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let Self { game_name, .. } = self;

        debug_assert_eq!(game_name, &info.game_inst.game_name());

        let pkgstate_selectors = info.game_inst.game().pkgs.iter().map(|inst| {
            let params = &inst.params;
            let pkg_name = &inst.pkg.name;

            let sort = PackageStatePattern { pkg_name, params }.sort(vec![]);

            GameStateSelector::PackageInstance {
                pkg_inst_name: &inst.name,
                sort,
            }
        });

        let rand_selectors =
            info.sample_info
                .positions
                .iter()
                .map(|sample_pos| GameStateSelector::Randomness {
                    sample_pos: Box::new(sample_pos.clone()),
                });

        let fields = pkgstate_selectors.chain(rand_selectors).collect();

        DatastructureSpec(vec![((), fields)])
    }
}
