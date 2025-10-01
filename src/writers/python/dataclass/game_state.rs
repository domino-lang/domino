use core::fmt::Display;

use crate::{
    theorem::GameInstance,
    writers::python::{
        dataclass::Dataclass,
        identifier::{GameStateFieldName, GameStateTypeName, PackageStateTypeName},
        ty::PyType,
    },
};

pub(crate) struct GameStatePattern<'a> {
    game_inst: &'a GameInstance,
}

impl<'a> GameStatePattern<'a> {
    pub fn new(game_inst: &'a GameInstance) -> Self {
        Self { game_inst }
    }
}

impl<'a> Dataclass<'a> for GameStatePattern<'a> {
    type Name = GameStateTypeName<'a>;
    fn name(&self) -> GameStateTypeName<'a> {
        GameStateTypeName(self.game_inst.game().name())
    }

    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType<'a>)> {
        self.game_inst.game.pkgs.iter().map(|pkg_inst| {
            (
                GameStateFieldName::PackageState(pkg_inst.name()),
                PyType::PackageState(PackageStateTypeName(pkg_inst.pkg_name())),
            )
        })
    }
}
