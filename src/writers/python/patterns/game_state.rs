/*
*
*
* We need to
* - figure out the types to use on python's side
*   - bits_n
*     - BitVector? external dep.
*     - bitvec? same problem.
*     - maybe we just need deps
*   - int -> int
*   - bool -> bool
*
* - we need the const assignments in here - maybe simply full gameinstance?
* - what sample info do we need?
*   - here, not so much, but we need to find a way to do randomness mapping
*
* */

use std::fmt::Display;

use crate::{package::Package, theorem::GameInstance};

static UNIT: () = ();

pub struct GameStatePattern<'a> {
    game_inst: &'a GameInstance,
}

impl<'a> GameStatePattern<'a> {
    pub fn new(game_inst: &'a GameInstance) -> Self {
        Self { game_inst }
    }
}

pub struct PackageStatePattern<'a> {
    pkg: &'a Package,
}

impl<'a> PackageStatePattern<'a> {
    pub fn new(pkg: &'a Package) -> Self {
        Self { pkg }
    }
}

struct GameStateTypeName<'a>(&'a str);
enum GameStateFieldName<'a> {
    PackageState(&'a str),
    Randomness(&'a str),
}
struct PackageStateTypeName<'a>(&'a str);
struct PackageStateFieldName<'a>(&'a str);

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

impl<'a> Display for PackageStateTypeName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(name) = self;
        write!(f, "PackageState_{name}")
    }
}

impl<'a> Display for PackageStateFieldName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(name) = self;
        write!(f, "{name}")
    }
}

impl<'a> Dataclass for PackageStatePattern<'a> {
    fn name(&self) -> impl Display {
        PackageStateTypeName(self.pkg.name())
    }

    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType<'_>)> {
        self.pkg.state.iter().map(|(name, ty, _)| {
            (
                PackageStateFieldName(name.as_str()),
                ty.clone().try_into().unwrap(),
            )
        })
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

pub struct DataclassWriter<DC: Dataclass>(pub DC);

impl<DC: Dataclass> Display for DataclassWriter<DC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "@dataclass")?;
        writeln!(f, "class {}:", self.0.name())?;
        for (name, ty) in self.0.fields() {
            writeln!(f, "  {name}: {ty}")?;
        }
        Ok(())
    }
}

struct BitVecLength<'a>(&'a ());

enum PyType<'a> {
    BitVec(BitVecLength<'a>),
    Int,
    Bool,
    List(Box<Self>),
    PackageState(&'a str),
}

impl<'a> Display for PyType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PyType::BitVec(bit_vec_length) => todo!(),
            PyType::Int => write!(f, "int"),
            PyType::Bool => write!(f, "bool"),
            PyType::List(py_type) => write!(f, "List[{py_type}]"),
            PyType::PackageState(name) => write!(f, "{}", PackageStateTypeName(name)),
        }
    }
}

impl<'a> TryFrom<crate::types::Type> for PyType<'a> {
    type Error = ();

    fn try_from(value: crate::types::Type) -> Result<Self, Self::Error> {
        match value {
            crate::types::Type::Integer => Ok(PyType::Int),
            crate::types::Type::Boolean => Ok(PyType::Bool),
            crate::types::Type::Bits(_count_spec) => Ok(PyType::BitVec(BitVecLength(&UNIT))),
            crate::types::Type::List(ty) => PyType::try_from(*ty).map(Box::new).map(PyType::List),
            _ => todo!(),
        }
    }
}

trait Dataclass {
    fn name(&self) -> impl Display;
    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType)>;
}
