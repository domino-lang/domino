// SPDX-License-Identifier: MIT OR Apache-2.0

use game_ident::GameIdentifier;
use pkg_ident::PackageConstIdentifier;
use theorem_ident::TheoremIdentifier;

use crate::{
    expressions::{Expression, ExpressionKind},
    parser::package::ForComp,
    types::Type,
};

use self::{
    game_ident::GameConstIdentifier,
    pkg_ident::{PackageIdentifier, PackageOracleCodeLoopVarIdentifier},
};

#[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
pub enum Identifier {
    PackageIdentifier(pkg_ident::PackageIdentifier),
    GameIdentifier(game_ident::GameIdentifier),
    TheoremIdentifier(theorem_ident::TheoremIdentifier),

    /// Denotes identifiers that were injected by transforms.
    /// Should only live inside oracle code
    Generated(String, Type),
}

impl Identifier {
    pub fn into_theorem_identifier(self) -> Option<TheoremIdentifier> {
        match self {
            Identifier::PackageIdentifier(package_identifier) => package_identifier
                .into_const()?
                .game_assignment?
                .into_identifier()?
                .into_theorem_identifier(),

            Identifier::GameIdentifier(game_identifier) => game_identifier
                .into_const()?
                .assigned_value?
                .into_identifier()?
                .into_theorem_identifier(),
            Identifier::TheoremIdentifier(theorem_identifier) => Some(theorem_identifier),
            Identifier::Generated(_, _) => None,
        }
    }

    pub fn as_theorem_identifier_mut(&mut self) -> Option<&mut TheoremIdentifier> {
        match self {
            Identifier::PackageIdentifier(package_identifier) => package_identifier
                .as_const_mut()?
                .game_assignment
                .as_mut()?
                .as_mut()
                .as_identifier_mut()?
                .as_theorem_identifier_mut(),

            Identifier::GameIdentifier(game_identifier) => game_identifier
                .as_const_mut()?
                .assigned_value
                .as_mut()?
                .as_mut()
                .as_identifier_mut()?
                .as_theorem_identifier_mut(),
            Identifier::TheoremIdentifier(theorem_identifier) => Some(theorem_identifier),
            Identifier::Generated(_, _) => None,
        }
    }

    pub fn as_theorem_identifier(&self) -> Option<&TheoremIdentifier> {
        match self {
            Identifier::PackageIdentifier(package_identifier) => package_identifier
                .as_const()?
                .game_assignment
                .as_ref()?
                .as_ref()
                .as_identifier()?
                .as_theorem_identifier(),

            Identifier::GameIdentifier(game_identifier) => game_identifier
                .as_const()?
                .assigned_value
                .as_ref()?
                .as_ref()
                .as_identifier()?
                .as_theorem_identifier(),
            Identifier::TheoremIdentifier(theorem_identifier) => Some(theorem_identifier),
            Identifier::Generated(_, _) => None,
        }
    }

    pub(crate) fn identifiers_match(&self, other: &Self) -> bool {
        match (self, other) {
            (Identifier::Generated(_, _), _) | (_, Identifier::Generated(_, _)) => {
                todo!("i don't think this should ever happen")
            }

            (
                Identifier::PackageIdentifier(PackageIdentifier::Const(l)),
                Identifier::PackageIdentifier(PackageIdentifier::Const(r)),
            ) => {
                if let (Some(l), Some(r)) = (l.game_assignment.as_ref(), r.game_assignment.as_ref())
                {
                    match (l.as_ref().kind(), r.as_ref().kind()) {
                        (ExpressionKind::Identifier(l), ExpressionKind::Identifier(r)) => {
                            l.identifiers_match(r)
                        }
                        _ => l == r,
                    }
                } else {
                    l.name == r.name && l.pkg_name == r.pkg_name
                }
            }

            (
                Identifier::GameIdentifier(GameIdentifier::Const(l)),
                Identifier::GameIdentifier(GameIdentifier::Const(r)),
            ) => {
                if let (Some(l), Some(r)) = (l.assigned_value.as_ref(), r.assigned_value.as_ref()) {
                    match (l.as_ref().kind(), r.as_ref().kind()) {
                        (ExpressionKind::Identifier(l), ExpressionKind::Identifier(r)) => {
                            l.identifiers_match(r)
                        }
                        _ => l == r,
                    }
                } else {
                    l.name == r.name && l.game_name == r.game_name
                }
            }

            (
                Identifier::TheoremIdentifier(TheoremIdentifier::Const(l)),
                Identifier::TheoremIdentifier(TheoremIdentifier::Const(r)),
            ) => l.name == r.name,

            (
                Identifier::PackageIdentifier(PackageIdentifier::Const(PackageConstIdentifier {
                    game_assignment,
                    ..
                })),
                game_ident @ Identifier::GameIdentifier(_),
            )
            | (
                game_ident @ Identifier::GameIdentifier(_),
                Identifier::PackageIdentifier(PackageIdentifier::Const(PackageConstIdentifier {
                    game_assignment,
                    ..
                })),
            ) => {
                let assignment = &**game_assignment.as_ref().unwrap();
                match assignment.kind() {
                    ExpressionKind::Identifier(inner_ident) => {
                        game_ident.identifiers_match(inner_ident)
                    }
                    _ => false,
                }
            }

            other => todo!("{other:?}"),
        }
        // 1. find common root context
        // 2. compare value at shared context
    }

    pub(crate) fn is_const(&self) -> bool {
        matches!(
            self,
            Identifier::PackageIdentifier(PackageIdentifier::Const(_))
                | Identifier::GameIdentifier(GameIdentifier::Const(_))
                | Identifier::TheoremIdentifier(TheoremIdentifier::Const(_))
        )
    }
}

impl From<GameConstIdentifier> for Identifier {
    fn from(value: GameConstIdentifier) -> Self {
        Identifier::GameIdentifier(game_ident::GameIdentifier::Const(value))
    }
}

impl From<PackageOracleCodeLoopVarIdentifier> for Identifier {
    fn from(value: PackageOracleCodeLoopVarIdentifier) -> Self {
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(value))
    }
}

impl From<PackageIdentifier> for Identifier {
    fn from(value: PackageIdentifier) -> Self {
        Identifier::PackageIdentifier(value)
    }
}

impl From<GameIdentifier> for Identifier {
    fn from(value: GameIdentifier) -> Self {
        Identifier::GameIdentifier(value)
    }
}

pub mod pkg_ident {
    use crate::types::Type;

    use super::*;

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub enum PackageIdentifier {
        Const(PackageConstIdentifier),
        State(PackageStateIdentifier),
        Local(PackageLocalIdentifier),
        OracleImport(PackageOracleImportIdentifier),
        OracleArg(PackageOracleArgIdentifier),
        ImportsLoopVar(PackageImportsLoopVarIdentifier),
        CodeLoopVar(PackageOracleCodeLoopVarIdentifier),
    }

    impl PackageIdentifier {
        pub(crate) fn ident_ref(&self) -> &str {
            match self {
                PackageIdentifier::Const(const_ident) => &const_ident.name,
                PackageIdentifier::State(state_ident) => &state_ident.name,
                PackageIdentifier::Local(local_ident) => &local_ident.name,
                PackageIdentifier::OracleArg(arg_ident) => &arg_ident.name,
                PackageIdentifier::OracleImport(oracle_import) => &oracle_import.name,
                PackageIdentifier::ImportsLoopVar(loopvar) => &loopvar.name,
                PackageIdentifier::CodeLoopVar(loopvar) => &loopvar.name,
            }
        }

        pub(crate) fn ident(&self) -> String {
            self.ident_ref().to_string()
        }

        pub(crate) fn get_type(&self) -> Type {
            match self {
                PackageIdentifier::Const(const_ident) => const_ident.ty.clone(),
                PackageIdentifier::State(state_ident) => state_ident.ty.clone(),
                PackageIdentifier::Local(local_ident) => local_ident.ty.clone(),
                PackageIdentifier::OracleArg(arg_ident) => arg_ident.ty.clone(),
                PackageIdentifier::OracleImport(oracle_import) => oracle_import.return_type.clone(),
                PackageIdentifier::ImportsLoopVar(_loopvar) => Type::Integer,
                PackageIdentifier::CodeLoopVar(_loopvar) => Type::Integer,
            }
        }

        pub(crate) fn set_pkg_inst_info(&mut self, pkg_inst_name: String, game_name: String) {
            match self {
                PackageIdentifier::Const(id) => id.set_pkg_inst_info(pkg_inst_name, game_name),
                PackageIdentifier::State(id) => id.set_pkg_inst_info(pkg_inst_name, game_name),
                PackageIdentifier::Local(id) => id.set_pkg_inst_info(pkg_inst_name, game_name),
                PackageIdentifier::OracleImport(id) => {
                    id.set_pkg_inst_info(pkg_inst_name, game_name)
                }
                PackageIdentifier::OracleArg(id) => id.set_pkg_inst_info(pkg_inst_name, game_name),
                PackageIdentifier::ImportsLoopVar(id) => {
                    id.set_pkg_inst_info(pkg_inst_name, game_name)
                }
                PackageIdentifier::CodeLoopVar(id) => {
                    id.set_pkg_inst_info(pkg_inst_name, game_name)
                }
            }
        }

        pub(crate) fn set_game_inst_info(&mut self, game_inst_name: String, theorem_name: String) {
            match self {
                PackageIdentifier::Const(id) => id.set_game_inst_info(game_inst_name, theorem_name),
                PackageIdentifier::State(id) => id.set_game_inst_info(game_inst_name, theorem_name),
                PackageIdentifier::Local(id) => id.set_game_inst_info(game_inst_name, theorem_name),
                PackageIdentifier::OracleImport(id) => {
                    id.set_game_inst_info(game_inst_name, theorem_name)
                }
                PackageIdentifier::OracleArg(id) => {
                    id.set_game_inst_info(game_inst_name, theorem_name)
                }
                PackageIdentifier::ImportsLoopVar(id) => {
                    id.set_game_inst_info(game_inst_name, theorem_name)
                }
                PackageIdentifier::CodeLoopVar(id) => {
                    id.set_game_inst_info(game_inst_name, theorem_name)
                }
            }
        }

        pub fn as_const(&self) -> Option<&PackageConstIdentifier> {
            if let Self::Const(v) = self {
                Some(v)
            } else {
                None
            }
        }
        pub fn as_const_mut(&mut self) -> Option<&mut PackageConstIdentifier> {
            if let Self::Const(v) = self {
                Some(v)
            } else {
                None
            }
        }
        pub fn into_const(self) -> Option<PackageConstIdentifier> {
            if let Self::Const(v) = self {
                Some(v)
            } else {
                None
            }
        }
        pub fn into_state(self) -> Option<PackageStateIdentifier> {
            if let Self::State(v) = self {
                Some(v)
            } else {
                None
            }
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageConstIdentifier {
        pub pkg_name: String,
        pub name: String,
        pub ty: crate::types::Type,
        pub game_assignment: Option<Box<Expression>>,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    impl From<PackageConstIdentifier> for Identifier {
        fn from(value: PackageConstIdentifier) -> Self {
            Identifier::PackageIdentifier(PackageIdentifier::Const(value))
        }
    }

    impl PackageConstIdentifier {
        pub(crate) fn new(name: String, pkg_name: String, ty: Type) -> Self {
            Self {
                pkg_name,
                name,
                ty,
                game_assignment: None,
                pkg_inst_name: None,
                game_name: None,
                game_inst_name: None,
                theorem_name: None,
            }
        }

        pub(crate) fn ident(&self) -> String {
            self.name.clone()
        }

        pub(crate) fn ident_ref(&self) -> &str {
            &self.name
        }

        pub(crate) fn set_assignment(&mut self, assignment: Expression) {
            self.game_assignment = Some(Box::new(assignment))
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageStateIdentifier {
        pub pkg_name: String,
        pub name: String,
        pub ty: crate::types::Type,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    impl From<PackageStateIdentifier> for Identifier {
        fn from(value: PackageStateIdentifier) -> Self {
            Identifier::PackageIdentifier(PackageIdentifier::State(value))
        }
    }

    macro_rules! impl_set_inst_info {
        ($idtype:ty) => {
            impl $idtype {
                pub(crate) fn set_pkg_inst_info(
                    &mut self,
                    pkg_inst_name: String,
                    game_name: String,
                ) {
                    self.pkg_inst_name = Some(pkg_inst_name);
                    self.game_name = Some(game_name);
                }

                pub(crate) fn set_game_inst_info(
                    &mut self,
                    game_inst_name: String,
                    theorem_name: String,
                ) {
                    self.game_inst_name = Some(game_inst_name);
                    self.theorem_name = Some(theorem_name);
                }
            }
        };
    }

    impl PackageStateIdentifier {
        pub(crate) fn new(name: String, pkg_name: String, ty: Type) -> Self {
            Self {
                pkg_name,
                name,
                ty,
                pkg_inst_name: None,
                game_name: None,
                game_inst_name: None,
                theorem_name: None,
            }
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageLocalIdentifier {
        pub pkg_name: String,
        pub oracle_name: String,
        pub name: String,
        pub ty: crate::types::Type,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageOracleArgIdentifier {
        pub pkg_name: String,
        pub oracle_name: String,
        pub name: String,
        pub ty: crate::types::Type,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageOracleImportIdentifier {
        pub pkg_name: String,
        pub name: String,
        pub args: Vec<crate::types::Type>,
        pub return_type: crate::types::Type,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageImportsLoopVarIdentifier {
        pub pkg_name: String,
        pub name: String,
        // ty is always Integer
        pub start: Box<Expression>,
        pub end: Box<Expression>,
        pub start_comp: ForComp,
        pub end_comp: ForComp,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct PackageOracleCodeLoopVarIdentifier {
        pub pkg_name: String,
        pub name: String,
        // ty is always Integer
        pub start: Box<Expression>,
        pub end: Box<Expression>,
        pub start_comp: ForComp,
        pub end_comp: ForComp,
        pub pkg_inst_name: Option<String>,
        pub game_name: Option<String>,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
    }

    impl_set_inst_info!(PackageConstIdentifier);
    impl_set_inst_info!(PackageStateIdentifier);
    impl_set_inst_info!(PackageLocalIdentifier);
    impl_set_inst_info!(PackageOracleArgIdentifier);
    impl_set_inst_info!(PackageOracleImportIdentifier);
    impl_set_inst_info!(PackageImportsLoopVarIdentifier);
    impl_set_inst_info!(PackageOracleCodeLoopVarIdentifier);
}

/*
*
* - im code soll der identifier stehen, der beschreibt wo der wert deklariert wird
*
*
* - pkg instanziieren:
*   - pkg const ident   -> aufloesen
*   - pkg loopvar ident -> anreichern
*
* - game instanziieren:
*   - game const ident   -> aufloesen
*   - game loopvar ident -> anreichern
*
*
*
* */

pub mod game_ident {
    use crate::types::Type;

    use self::pkg_ident::PackageConstIdentifier;

    use super::*;

    impl GameIdentifier {
        pub(crate) fn ident_ref(&self) -> &str {
            match self {
                GameIdentifier::Const(const_ident) => &const_ident.name,
                GameIdentifier::LoopVar(loopvar) => &loopvar.name,
            }
        }

        pub(crate) fn ident(&self) -> String {
            self.ident_ref().to_string()
        }

        pub(crate) fn get_type(&self) -> Type {
            match self {
                GameIdentifier::Const(const_ident) => const_ident.ty.clone(),
                GameIdentifier::LoopVar(_local_ident) => Type::Integer,
            }
        }

        pub fn into_const(self) -> Option<GameConstIdentifier> {
            if let Self::Const(v) = self {
                Some(v)
            } else {
                None
            }
        }

        pub fn as_const_mut(&mut self) -> Option<&mut GameConstIdentifier> {
            if let Self::Const(v) = self {
                Some(v)
            } else {
                None
            }
        }

        pub fn as_const(&self) -> Option<&GameConstIdentifier> {
            if let Self::Const(v) = self {
                Some(v)
            } else {
                None
            }
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub enum GameIdentifier {
        Const(GameConstIdentifier),
        LoopVar(GameLoopVarIdentifier),
    }

    impl GameIdentifier {
        pub fn game_name(&self) -> &str {
            match self {
                GameIdentifier::Const(c) => &c.game_name,
                GameIdentifier::LoopVar(l) => &l.game_name,
            }
        }

        pub fn with_instance_info(self, inst_info: GameIdentInstanciationInfo) -> Self {
            match self {
                GameIdentifier::Const(c) => Self::Const(GameConstIdentifier {
                    inst_info: Some(inst_info),
                    ..c
                }),
                GameIdentifier::LoopVar(l) => Self::LoopVar(GameLoopVarIdentifier {
                    inst_info: Some(inst_info),
                    ..l
                }),
            }
        }
    }

    impl GameIdentifier {
        pub(crate) fn set_game_inst_info(&mut self, game_inst_name: String, theorem_name: String) {
            match self {
                GameIdentifier::Const(id) => id.set_game_inst_info(game_inst_name, theorem_name),
                GameIdentifier::LoopVar(id) => id.set_game_inst_info(game_inst_name, theorem_name),
            }
        }
    }

    impl GameConstIdentifier {
        pub(crate) fn set_game_inst_info(&mut self, game_inst_name: String, theorem_name: String) {
            self.game_inst_name = Some(game_inst_name);
            self.theorem_name = Some(theorem_name);
        }

        pub(crate) fn set_assignment(&mut self, assignment: Expression) {
            self.assigned_value = Some(Box::new(assignment))
        }
    }

    impl GameLoopVarIdentifier {
        pub(crate) fn set_game_inst_info(&mut self, game_inst_name: String, theorem_name: String) {
            self.game_inst_name = Some(game_inst_name);
            self.theorem_name = Some(theorem_name);
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct GameIdentInstanciationInfo {
        pub lower: PackageConstIdentifier,
        pub pkg_inst_name: String,
    }

    #[derive(Debug, Clone, PartialOrd, Eq, Ord)]
    pub struct GameConstIdentifier {
        pub game_name: String,
        pub name: String,
        pub ty: crate::types::Type,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
        pub inst_info: Option<GameIdentInstanciationInfo>,
        pub assigned_value: Option<Box<Expression>>,
    }

    impl PartialEq for GameConstIdentifier {
        fn eq(&self, other: &Self) -> bool {
            self.game_name == other.game_name && self.name == other.name && self.ty == other.ty
        }
    }

    impl core::hash::Hash for GameConstIdentifier {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.game_name.hash(state);
            self.name.hash(state);
            self.ty.hash(state);
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct GameLoopVarIdentifier {
        pub game_name: String,
        pub name: String,
        // ty is always Integer
        pub start: Box<Expression>,
        pub end: Box<Expression>,
        pub start_comp: ForComp,
        pub end_comp: ForComp,
        pub game_inst_name: Option<String>,
        pub theorem_name: Option<String>,
        pub inst_info: Option<GameIdentInstanciationInfo>,
    }

    impl From<GameLoopVarIdentifier> for Identifier {
        fn from(value: GameLoopVarIdentifier) -> Self {
            Identifier::GameIdentifier(GameIdentifier::LoopVar(value))
        }
    }
}

pub mod theorem_ident {
    use crate::types::Type;

    use super::*;

    impl TheoremIdentifier {
        pub(crate) fn ident_ref(&self) -> &str {
            match self {
                TheoremIdentifier::Const(const_ident) => &const_ident.name,
                TheoremIdentifier::LoopVar(loopvar) => &loopvar.name,
            }
        }

        pub(crate) fn ident(&self) -> String {
            self.ident_ref().to_string()
        }

        pub(crate) fn get_type(&self) -> Type {
            match self {
                TheoremIdentifier::Const(const_ident) => const_ident.ty.clone(),
                TheoremIdentifier::LoopVar(_local_ident) => Type::Integer,
            }
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub enum TheoremIdentifier {
        Const(TheoremConstIdentifier),
        LoopVar(TheoremLoopVarIdentifier),
    }

    impl TheoremIdentifier {
        pub fn with_instance_info(self, inst_info: TheoremIdentInstanciationInfo) -> Self {
            match self {
                TheoremIdentifier::Const(c) => Self::Const(TheoremConstIdentifier {
                    inst_info: Some(inst_info),
                    ..c
                }),
                TheoremIdentifier::LoopVar(l) => Self::LoopVar(TheoremLoopVarIdentifier {
                    inst_info: Some(inst_info),
                    ..l
                }),
            }
        }

        pub fn theorem_name(&self) -> &str {
            match self {
                TheoremIdentifier::Const(c) => &c.theorem_name,
                TheoremIdentifier::LoopVar(l) => &l.theorem_name,
            }
        }
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct TheoremIdentInstanciationInfo {
        pub lower: GameConstIdentifier,
        pub game_inst_name: String,
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct TheoremConstIdentifier {
        pub theorem_name: String,
        pub name: String,
        pub ty: crate::types::Type,
        pub inst_info: Option<TheoremIdentInstanciationInfo>,
    }

    #[derive(Debug, Clone, Hash, PartialOrd, Eq, Ord, PartialEq)]
    pub struct TheoremLoopVarIdentifier {
        pub theorem_name: String,
        pub name: String,
        // ty is always Integer
        pub start: Box<Expression>,
        pub end: Box<Expression>,
        pub start_comp: ForComp,
        pub end_comp: ForComp,
        pub inst_info: Option<TheoremIdentInstanciationInfo>,
    }

    impl From<TheoremConstIdentifier> for TheoremIdentifier {
        fn from(value: TheoremConstIdentifier) -> Self {
            TheoremIdentifier::Const(value)
        }
    }

    impl From<TheoremLoopVarIdentifier> for TheoremIdentifier {
        fn from(value: TheoremLoopVarIdentifier) -> Self {
            TheoremIdentifier::LoopVar(value)
        }
    }

    impl<T: Into<TheoremIdentifier>> From<T> for Identifier {
        fn from(value: T) -> Self {
            Identifier::TheoremIdentifier(value.into())
        }
    }
}

impl Identifier {
    pub fn get_type(&self) -> Type {
        match self {
            Identifier::PackageIdentifier(pkg_ident) => pkg_ident.get_type(),
            Identifier::GameIdentifier(game_ident) => game_ident.get_type(),
            Identifier::TheoremIdentifier(theorem_ident) => theorem_ident.get_type(),
            Identifier::Generated(_, ty) => ty.clone(),
        }
    }

    pub fn ident_ref(&self) -> &str {
        match self {
            Identifier::Generated(name, _) => name,
            Identifier::PackageIdentifier(pkg_ident) => pkg_ident.ident_ref(),
            Identifier::GameIdentifier(game_ident) => game_ident.ident_ref(),
            Identifier::TheoremIdentifier(theorem_ident) => theorem_ident.ident_ref(),
        }
    }

    pub fn ident(&self) -> String {
        match self {
            Identifier::Generated(ident, _) => ident.clone(),
            Identifier::PackageIdentifier(pkg_ident) => pkg_ident.ident(),
            Identifier::GameIdentifier(game_ident) => game_ident.ident(),
            Identifier::TheoremIdentifier(theorem_ident) => theorem_ident.ident(),
        }
    }
}

#[cfg(test)]
mod tests {
    /* while we should test equality of identifiers, this one is not interesting because it tests variants that we want to get rid of
    use super::{GameInstanceConst, Identifier, PackageConst};

    #[test]
    fn identifier_equality() {
        let left = Identifier::Parameter(PackageConst {
            name_in_pkg: "d".to_string(),
            pkgname: "Mod".to_string(),
            game_inst_name: "MODSec0_inst".to_string(),
            name_in_comp: "d".to_string(),
            name_in_theorem: "d".to_string(),
        });

        let right = Identifier::GameInstanceConst(GameInstanceConst {
            game_inst_name: "MODSec0_inst".to_string(),
            name_in_comp: "d".to_string(),
            name_in_theorem: "d".to_string(),
        });

        assert_eq!(left, right)
        }
    */
}
