use domino_ast::{
    ast_nodes::{game, identifier, oracles, package, statements, theorem, types},
    Arenas,
};
use domino_collections::arena::Ref;

use crate::{
    diag,
    traits::{
        HasTypeArgResolution, HasTypeResolution, HasValueResolution, TypeArgResolution,
        TypeArgResolutionKind, TypeResolution, TypeResolutionKind, ValueResolution,
        ValueResolutionKind,
    },
    BuiltinType, BuiltinValue,
};

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
    State(Ref<package::PackageStateDecl>),
    Consts(Ref<package::PackageConstDecl>),
    Arg(Ref<oracles::OracleValueArgDecl>),
    Local(Ref<statements::AssignStatement>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

impl ValueResolution<oracles::OracleExpressionKind> for OracleValueResolution {
    fn kind(
        &self,
        arenas: &Arenas,
    ) -> crate::traits::ValueResolutionKind<oracles::OracleExpressionKind> {
        match self {
            OracleValueResolution::State(decl) => {
                ValueResolutionKind::Declaration(arenas.get(decl).ty)
            }
            OracleValueResolution::Consts(decl) => {
                ValueResolutionKind::Declaration(arenas.get(decl).ty)
            }
            OracleValueResolution::Arg(decl) => {
                ValueResolutionKind::Declaration(arenas.get(decl).ty)
            }
            // TODO: handle complex patterns
            OracleValueResolution::Local(assign) => {
                ValueResolutionKind::Assignment(arenas.get(assign).expr)
            }
            OracleValueResolution::Builtin(builtin_value) => {
                ValueResolutionKind::Builtin(*builtin_value)
            }
            OracleValueResolution::Error(e) => ValueResolutionKind::Error(*e),
        }
    }
}

impl<'a> HasValueResolution<oracles::OracleExpressionKind> for crate::IdentifierResolution<'a> {
    type Resolution = OracleValueResolution;
    fn get(
        &self,
        id: Ref<identifier::Identifier<identifier::OracleValueIdentifierKind>>,
    ) -> &OracleValueResolution {
        self.oracle_value_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PackageTypeResolution {
    TypeParam(Ref<identifier::PackageTypeIdentifier>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

impl TypeResolution<types::PackageTypeKind> for PackageTypeResolution {
    fn kind(&self, _arenas: &Arenas) -> TypeResolutionKind<types::PackageTypeKind> {
        match *self {
            PackageTypeResolution::TypeParam(id) => TypeResolutionKind::Declaration(id),
            PackageTypeResolution::Builtin(builtin_type) => {
                TypeResolutionKind::Builtin(builtin_type)
            }
            PackageTypeResolution::Error(e) => TypeResolutionKind::Error(e),
        }
    }
}

impl<'a> HasTypeResolution<types::PackageTypeKind> for crate::IdentifierResolution<'a> {
    type Resolution = PackageTypeResolution;

    fn type_resolution(
        &self,
        id: Ref<
            identifier::Identifier<<types::PackageTypeKind as types::TypeKind>::TypeIdentifierKind>,
        >,
    ) -> &Self::Resolution {
        self.pkg_type_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PackageTypeArgResolution {
    TypeParam(Ref<identifier::PackageTypeIdentifier>),
    Consts(Ref<package::PackageConstDecl>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

impl TypeArgResolution<types::PackageTypeKind> for PackageTypeArgResolution {
    fn kind(&self, arenas: &Arenas) -> TypeArgResolutionKind<types::PackageTypeKind> {
        match *self {
            PackageTypeArgResolution::TypeParam(id) => {
                TypeArgResolutionKind::Type(TypeResolutionKind::Declaration(id))
            }
            PackageTypeArgResolution::Consts(decl) => {
                TypeArgResolutionKind::Value(ValueResolutionKind::Declaration(arenas.get(decl).ty))
            }
            PackageTypeArgResolution::Builtin(builtin_type) => {
                TypeArgResolutionKind::Type(TypeResolutionKind::Builtin(builtin_type))
            }
            PackageTypeArgResolution::Error(e) => TypeArgResolutionKind::Error(e),
        }
    }
}

impl<'a> HasTypeArgResolution<types::PackageTypeKind> for crate::IdentifierResolution<'a> {
    type Resolution = PackageTypeArgResolution;

    fn type_arg_resolution(
        &self,
        id: Ref<
            identifier::Identifier<
                <types::PackageTypeKind as types::TypeKind>::TypeArgIdentifierKind,
            >,
        >,
    ) -> &Self::Resolution {
        self.pkg_type_arg_names.get(id)
    }
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

impl TypeResolution<types::GameTypeKind> for GameTypeResolution {
    fn kind(&self, _arenas: &Arenas) -> TypeResolutionKind<types::GameTypeKind> {
        match *self {
            GameTypeResolution::TypeParam(id) => TypeResolutionKind::Declaration(id),
            GameTypeResolution::Builtin(builtin_type) => TypeResolutionKind::Builtin(builtin_type),
            GameTypeResolution::Error(e) => TypeResolutionKind::Error(e),
        }
    }
}

impl<'a> HasTypeResolution<types::GameTypeKind> for crate::IdentifierResolution<'a> {
    type Resolution = GameTypeResolution;

    fn type_resolution(
        &self,
        id: Ref<
            identifier::Identifier<<types::GameTypeKind as types::TypeKind>::TypeIdentifierKind>,
        >,
    ) -> &Self::Resolution {
        self.game_type_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum GameTypeArgResolution {
    TypeParam(Ref<identifier::GameTypeIdentifier>),
    Consts(Ref<game::GameConstDecl>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

impl TypeArgResolution<types::GameTypeKind> for GameTypeArgResolution {
    fn kind(&self, arenas: &Arenas) -> TypeArgResolutionKind<types::GameTypeKind> {
        match *self {
            GameTypeArgResolution::TypeParam(id) => {
                TypeArgResolutionKind::Type(TypeResolutionKind::Declaration(id))
            }
            GameTypeArgResolution::Consts(decl) => {
                TypeArgResolutionKind::Value(ValueResolutionKind::Declaration(arenas.get(decl).ty))
            }
            GameTypeArgResolution::Builtin(builtin_type) => {
                TypeArgResolutionKind::Type(TypeResolutionKind::Builtin(builtin_type))
            }
            GameTypeArgResolution::Error(e) => TypeArgResolutionKind::Error(e),
        }
    }
}

impl<'a> HasTypeArgResolution<types::GameTypeKind> for crate::IdentifierResolution<'a> {
    type Resolution = GameTypeArgResolution;

    fn type_arg_resolution(
        &self,
        id: Ref<
            identifier::Identifier<<types::GameTypeKind as types::TypeKind>::TypeArgIdentifierKind>,
        >,
    ) -> &Self::Resolution {
        self.game_type_arg_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum GameConstValueResolution {
    ConstParam(Ref<game::GameConstDecl>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

impl ValueResolution<game::PureGameExpressionKind> for GameConstValueResolution {
    fn kind(&self, arenas: &Arenas) -> ValueResolutionKind<game::PureGameExpressionKind> {
        match self {
            GameConstValueResolution::ConstParam(decl) => {
                ValueResolutionKind::Declaration(arenas.get(decl).ty)
            }
            GameConstValueResolution::Builtin(builtin_value) => {
                ValueResolutionKind::Builtin(*builtin_value)
            }
            GameConstValueResolution::Error(e) => ValueResolutionKind::Error(*e),
        }
    }
}

impl<'a> HasValueResolution<game::PureGameExpressionKind> for crate::IdentifierResolution<'a> {
    type Resolution = GameConstValueResolution;
    fn get(
        &self,
        id: Ref<identifier::Identifier<identifier::GameConstValueIdentifierKind>>,
    ) -> &GameConstValueResolution {
        self.game_const_value_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PackageConstValueResolution {
    ConstParam(Ref<package::PackageConstDecl>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

impl ValueResolution<package::PurePackageExpressionKind> for PackageConstValueResolution {
    fn kind(&self, arenas: &Arenas) -> ValueResolutionKind<package::PurePackageExpressionKind> {
        match self {
            PackageConstValueResolution::ConstParam(decl) => {
                ValueResolutionKind::Declaration(arenas.get(decl).ty)
            }
            PackageConstValueResolution::Builtin(builtin_value) => {
                ValueResolutionKind::Builtin(*builtin_value)
            }
            PackageConstValueResolution::Error(e) => ValueResolutionKind::Error(*e),
        }
    }
}

impl<'a> HasValueResolution<package::PurePackageExpressionKind>
    for crate::IdentifierResolution<'a>
{
    type Resolution = PackageConstValueResolution;
    fn get(
        &self,
        id: Ref<identifier::Identifier<identifier::PackageConstValueIdentifierKind>>,
    ) -> &PackageConstValueResolution {
        self.pkg_const_value_names.get(id)
    }
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

impl TypeResolution<types::TheoremTypeKind> for TheoremTypeResolution {
    fn kind(&self, _arenas: &Arenas) -> TypeResolutionKind<types::TheoremTypeKind> {
        match *self {
            TheoremTypeResolution::Builtin(builtin_type) => {
                TypeResolutionKind::Builtin(builtin_type)
            }
            TheoremTypeResolution::Error(e) => TypeResolutionKind::Error(e),
        }
    }
}

impl<'a> HasTypeResolution<types::TheoremTypeKind> for crate::IdentifierResolution<'a> {
    type Resolution = TheoremTypeResolution;

    fn type_resolution(
        &self,
        id: Ref<
            identifier::Identifier<<types::TheoremTypeKind as types::TypeKind>::TypeIdentifierKind>,
        >,
    ) -> &Self::Resolution {
        self.theorem_type_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TheoremTypeArgResolution {
    Consts(Ref<theorem::TheoremConstDecl>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

impl TypeArgResolution<types::TheoremTypeKind> for TheoremTypeArgResolution {
    fn kind(&self, arenas: &Arenas) -> TypeArgResolutionKind<types::TheoremTypeKind> {
        match *self {
            TheoremTypeArgResolution::Builtin(builtin_type) => {
                TypeArgResolutionKind::Type(TypeResolutionKind::Builtin(builtin_type))
            }
            TheoremTypeArgResolution::Error(e) => TypeArgResolutionKind::Error(e),
            TheoremTypeArgResolution::Consts(decl) => {
                TypeArgResolutionKind::Value(ValueResolutionKind::Declaration(arenas.get(decl).ty))
            }
        }
    }
}

impl<'a> HasTypeArgResolution<types::TheoremTypeKind> for crate::IdentifierResolution<'a> {
    type Resolution = TheoremTypeArgResolution;

    fn type_arg_resolution(
        &self,
        id: Ref<
            identifier::Identifier<
                <types::TheoremTypeKind as types::TypeKind>::TypeArgIdentifierKind,
            >,
        >,
    ) -> &Self::Resolution {
        self.theorem_type_arg_names.get(id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TheoremConstValueResolution {
    ConstParam(Ref<theorem::TheoremConstDecl>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

impl ValueResolution<theorem::PureTheoremExpressionKind> for TheoremConstValueResolution {
    fn kind(&self, arenas: &Arenas) -> ValueResolutionKind<theorem::PureTheoremExpressionKind> {
        match self {
            TheoremConstValueResolution::ConstParam(decl) => {
                ValueResolutionKind::Declaration(arenas.get(decl).ty)
            }
            TheoremConstValueResolution::Builtin(builtin_value) => {
                ValueResolutionKind::Builtin(*builtin_value)
            }
            TheoremConstValueResolution::Error(e) => ValueResolutionKind::Error(*e),
        }
    }
}

impl<'a> HasValueResolution<theorem::PureTheoremExpressionKind>
    for crate::IdentifierResolution<'a>
{
    type Resolution = TheoremConstValueResolution;
    fn get(
        &self,
        id: Ref<identifier::Identifier<identifier::TheoremConstValueIdentifierKind>>,
    ) -> &TheoremConstValueResolution {
        self.theorem_const_value_names.get(id)
    }
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
