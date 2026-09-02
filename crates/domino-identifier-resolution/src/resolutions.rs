use domino_ast::{
    arena::Ref,
    ast_nodes::{game, identifier, oracles, package, statements, theorem},
};

use crate::{diag, BuiltinType, BuiltinValue};

/// A resolution for an oracle name in a signature position
#[derive(Debug, Clone, Copy)]
pub enum OracleImportResolution {
    Import(Ref<oracles::OracleSignature<identifier::OracleImportIdentifierKind>>),
    Error(Ref<diag::Diagnostic>),
}

/// A resolution for an oracle name in a definition position
#[derive(Debug, Clone, Copy)]
pub enum OracleDefinitionResolution {
    Definition(Ref<oracles::OracleDefinition>),
    Error(Ref<diag::Diagnostic>),
}

/// A resolution for the import part of an oracle name in a composition position, i.e. it resolves
/// the oracle name in the composition to the sigature in the import block of the caller
#[derive(Debug, Clone, Copy)]
pub enum OracleCompositionImportResolution {
    Adversary,
    Import {
        sig: Ref<oracles::OracleSignature<identifier::OracleImportIdentifierKind>>,
        pkg_inst: Ref<game::InstanceBlock>,
    },
    EquivalenceOracle {
        sig: Ref<oracles::OracleSignature<identifier::OracleImportIdentifierKind>>,
        pkg_inst: Ref<game::InstanceBlock>,
        game_inst: Ref<theorem::InstanceBlock>,
    },
    Error(Ref<diag::Diagnostic>),
}

/// A resolution for the definition part of an oracle name in a composition position, i.e. it
/// resolces the oracle name in the composition to the oracle definition of the callee
#[derive(Debug, Clone, Copy)]
pub enum OracleCompositionDefinitionResolution {
    Definition {
        def: Ref<oracles::OracleDefinition>,
        pkg_inst: Ref<game::InstanceBlock>,
    },
    EquivalenceOracle {
        def: Ref<oracles::OracleDefinition>,
        pkg_inst: Ref<game::InstanceBlock>,
        game_inst: Ref<theorem::InstanceBlock>,
    },
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum OracleValueResolution {
    State(Ref<package::PackageConstDecl>),
    Consts(Ref<package::PackageConstDecl>),
    Arg(Ref<oracles::OracleValueArgDecl>),
    Local(Ref<statements::AssignStatement>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum PackageTypeResolution {
    TypeParam(Ref<identifier::PackageTypeIdentifier>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum PackageTypeArgResolution {
    TypeParam(Ref<identifier::PackageTypeIdentifier>),
    Consts(Ref<package::PackageConstDecl>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum GameResolution {
    Game(Ref<game::Game>),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum GameTypeResolution {
    TypeParam(Ref<identifier::GameTypeIdentifier>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum GameTypeArgResolution {
    TypeParam(Ref<identifier::GameTypeArgumentIdentifier>),
    Consts(Ref<game::GameConstDecl>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum GameConstValueResolution {
    ConstParam(Ref<game::GameConstDecl>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum PackageConstValueResolution {
    ConstParam(Ref<package::PackageConstDecl>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum PackageInstanceResolution {
    Adversary,
    PackageInstance(Ref<game::InstanceBlock>),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum PackageResolution {
    Package(Ref<package::Package>),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum TheoremResolution {
    Theorem(Ref<theorem::Theorem>),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum TheoremTypeResolution {
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum TheoremTypeArgResolution {
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum TheoremConstValueResolution {
    ConstParam(Ref<theorem::TheoremConstDecl>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum GameInstanceResolution {
    GameInstance(Ref<theorem::InstanceBlock>),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum AssumptionResolution {
    Assumption(Ref<theorem::AssumptionsItem>),
    Error(Ref<diag::Diagnostic>),
}

#[derive(Debug, Clone, Copy)]
pub enum LemmaResolution {
    Lemma(Ref<theorem::LemmaItem>),
    Error(Ref<diag::Diagnostic>),
}

macro_rules! impl_from_diag {
    ($resolution:ty) => {
        impl From<Ref<diag::Diagnostic>> for $resolution {
            fn from(diag: Ref<diag::Diagnostic>) -> Self {
                Self::Error(diag)
            }
        }
    };
}

impl_from_diag!(OracleImportResolution);
impl_from_diag!(OracleDefinitionResolution);
impl_from_diag!(OracleCompositionImportResolution);
impl_from_diag!(OracleCompositionDefinitionResolution);
impl_from_diag!(OracleValueResolution);
impl_from_diag!(PackageTypeResolution);
impl_from_diag!(PackageTypeArgResolution);
impl_from_diag!(GameResolution);
impl_from_diag!(GameTypeResolution);
impl_from_diag!(GameTypeArgResolution);
impl_from_diag!(GameConstValueResolution);
impl_from_diag!(PackageConstValueResolution);
impl_from_diag!(PackageInstanceResolution);
impl_from_diag!(PackageResolution);
impl_from_diag!(TheoremResolution);
impl_from_diag!(TheoremTypeResolution);
impl_from_diag!(TheoremTypeArgResolution);
impl_from_diag!(TheoremConstValueResolution);
impl_from_diag!(GameInstanceResolution);
impl_from_diag!(AssumptionResolution);
impl_from_diag!(LemmaResolution);
