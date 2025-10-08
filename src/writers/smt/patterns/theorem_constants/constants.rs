use sspverif_smtlib::{
    syntax::{command::Command, term::Term},
    theories,
};

use crate::types::Type;

use super::ConstantPattern;

pub struct TheoremConstant<'a> {
    pub theorem_name: &'a str,
    pub ident_name: &'a str,
    pub ty: &'a Type,
}

pub struct GameInstanceConstant<'a> {
    pub theorem_name: &'a str,
    pub game_inst_name: &'a str,
    pub ident_name: &'a str,
    pub ty: &'a Type,
}

pub struct PackageInstanceConstant<'a> {
    pub theorem_name: &'a str,
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub ident_name: &'a str,
    pub ty: &'a Type,
}

pub struct GameInstanceConstantAssigment<'a> {
    pub theorem_const: TheoremConstant<'a>,
    pub game_inst_const: GameInstanceConstant<'a>,
}

pub struct PackageInstanceConstantAssigment<'a> {
    pub game_inst_const: GameInstanceConstant<'a>,
    pub pkg_inst_const: PackageInstanceConstant<'a>,
}

impl super::ConstantPattern for TheoremConstant<'_> {
    fn name(&self) -> String {
        let Self {
            theorem_name,
            ident_name,
            ..
        } = self;
        format!("<$const-theorem-{theorem_name}-{ident_name}$>")
    }

    fn sort(&self) -> crate::writers::smt::sorts::Sort {
        self.ty.clone().into()
    }
}

impl super::ConstantPattern for GameInstanceConstant<'_> {
    fn name(&self) -> String {
        let Self {
            theorem_name,
            game_inst_name,
            ident_name,
            ..
        } = self;
        format!("<$const-gameinst-{theorem_name}-{game_inst_name}-{ident_name}$>")
    }

    fn sort(&self) -> crate::writers::smt::sorts::Sort {
        self.ty.clone().into()
    }
}

impl super::ConstantPattern for PackageInstanceConstant<'_> {
    fn name(&self) -> String {
        let Self {
            theorem_name,
            game_inst_name,
            pkg_inst_name,
            ident_name,
            ..
        } = self;
        format!("<$const-pkginst-{theorem_name}-{game_inst_name}-{pkg_inst_name}-{ident_name}$>")
    }

    fn sort(&self) -> crate::writers::smt::sorts::Sort {
        self.ty.clone().into()
    }
}

impl From<GameInstanceConstantAssigment<'_>> for Command {
    fn from(value: GameInstanceConstantAssigment<'_>) -> Self {
        let theorem_ident = Term::Base(value.theorem_const.name().into(), vec![]);
        let game_inst_ident = Term::Base(value.game_inst_const.name().into(), vec![]);

        Command::Assert(theories::core::eq(vec![theorem_ident, game_inst_ident]))
    }
}

impl From<PackageInstanceConstantAssigment<'_>> for Command {
    fn from(value: PackageInstanceConstantAssigment<'_>) -> Self {
        let game_inst_ident = Term::Base(value.game_inst_const.name().into(), vec![]);
        let pkg_inst_ident = Term::Base(value.pkg_inst_const.name().into(), vec![]);

        Command::Assert(theories::core::eq(vec![game_inst_ident, pkg_inst_ident]))
    }
}
