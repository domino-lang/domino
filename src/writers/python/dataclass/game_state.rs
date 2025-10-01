use core::fmt::Display;

use crate::{
    theorem::GameInstance,
    writers::python::{dataclass::Dataclass, ty::PyType},
};

pub struct GameStatePattern<'a> {
    game_inst: &'a GameInstance,
}

impl<'a> GameStatePattern<'a> {
    pub fn new(game_inst: &'a GameInstance) -> Self {
        Self { game_inst }
    }
}

struct GameStateTypeName<'a>(&'a str);

enum GameStateFieldName<'a> {
    PackageState(&'a str),
    Randomness(&'a str),
}

impl<'a> Display for GameStateTypeName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(name) = self;
        write!(f, "GameState_{name}")
    }
}

impl<'a> Display for GameStateFieldName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GameStateFieldName::PackageState(name) => write!(f, "pkg_{name}"),
            GameStateFieldName::Randomness(_) => todo!(),
        }
    }
}

impl<'a> Dataclass for GameStatePattern<'a> {
    fn name(&self) -> impl Display {
        self.game_inst.game().name()
    }

    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType)> {
        self.game_inst.game.pkgs.iter().map(|pkg_inst| {
            (
                GameStateFieldName::PackageState(pkg_inst.name()),
                PyType::PackageState(pkg_inst.pkg_name()),
            )
        })
    }
}
