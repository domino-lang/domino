use crate::DeclarationType;
use domino_ast::{
    ast_nodes::{
        game,
        identifier::{self, Identifier as AstIdentifier, *},
    },
    GlobalRefId, InArena, NodeType, NodeTypeRef as _,
};
use domino_collections::arena::{Arena, Ref};

pub type Diagnostics = Arena<Diagnostic>;

#[derive(Debug, Clone, Copy)]
pub enum Diagnostic {
    MissingResolution(MissingResolutionDiag),
    UndefinedIdentifier(UndefinedIdentifierDiag),
    ExpectedConstValueIdentifier(ExpectedConstValueIdentifierDiag),
    ExpectedValueIdentifier(ExpectedValueIdentifierDiag),
    ExpectedTypeIdentifier(ExpectedTypeIdentifierDiag),
    ExpectedTypeArgIdentifier(ExpectedTypeArgIdentifierDiag),
    ExpectedOracleIdentifier(ExpectedOracleIdentifierDiag),
    ExpectedPackageIdentifier(ExpectedPackageIdentifierDiag),
    ExpectedPackageInstanceIdentifier(ExpectedPackageInstanceIdentifierDiag),
    ExpectedGameIdentifier(ExpectedGameIdentifierDiag),
    ExpectedGameInstanceIdentifier(ExpectedGameInstanceIdentifierDiag),
    ExpectedAssumptionIdentifier(ExpectedAssumptionIdentifierDiag),
    AssignToConst(AssignToConstDiag),
    PackageDoesNotImportOracle(PackageDoesNotImportOracleDiag),
    PackageDoesNotDefineOracle(PackageDoesNotDefineOracleDiag),
    AdversaryAsCallee(AdversaryAsCalleeDiag),
    CantRedefineBuiltin(CantRedefineBuiltinDiag),
    AlreadyDefined(AlreadyDefinedDiag),
}

impl Diagnostic {
    pub fn at(&self) -> GlobalRefId {
        match self {
            Diagnostic::MissingResolution(node) => node.ident,
            Diagnostic::UndefinedIdentifier(node) => node.ident,
            Diagnostic::ExpectedValueIdentifier(node) => node.ident,
            Diagnostic::ExpectedConstValueIdentifier(node) => node.ident,
            Diagnostic::ExpectedTypeIdentifier(node) => node.ident,
            Diagnostic::ExpectedTypeArgIdentifier(node) => node.ident,
            Diagnostic::ExpectedOracleIdentifier(node) => node.ident,
            Diagnostic::ExpectedPackageIdentifier(node) => node.ident,
            Diagnostic::ExpectedPackageInstanceIdentifier(node) => node.ident,
            Diagnostic::ExpectedGameIdentifier(node) => node.ident,
            Diagnostic::ExpectedGameInstanceIdentifier(node) => node.ident,
            Diagnostic::ExpectedAssumptionIdentifier(node) => node.ident,
            Diagnostic::AssignToConst(node) => node.ident,
            Diagnostic::PackageDoesNotImportOracle(node) => node.compose_oracle.global_ref_id(),
            Diagnostic::PackageDoesNotDefineOracle(node) => node.compose_oracle.global_ref_id(),
            Diagnostic::AdversaryAsCallee(node) => node.ident.global_ref_id(),
            Diagnostic::CantRedefineBuiltin(node) => node.ident,
            Diagnostic::AlreadyDefined(node) => node.ident,
        }
    }
}

pub enum ValueIdentifier {
    Oracle(Ref<OracleValueIdentifier>),
    Package(Ref<PackageConstValueIdentifier>),
    Game(Ref<GameConstValueIdentifier>),
    Theorem(Ref<TheoremConstValueIdentifier>),
}

pub enum TypeIdentifier {
    Package(Ref<PackageTypeIdentifier>),
    Game(Ref<GameTypeIdentifier>),
    Theorem(Ref<TheoremTypeIdentifier>),
}

pub enum TypeArgIdentifier {
    Package(Ref<PackageTypeArgumentIdentifier>),
    Game(Ref<GameTypeArgumentIdentifier>),
    Theorem(Ref<TheoremTypeArgumentIdentifier>),
}

pub enum Identifier {
    Value(Ref<ValueIdentifier>),
    Type(Ref<TypeIdentifier>),
    TypeArg(Ref<TypeArgIdentifier>),
    Oracle(Ref<OracleIdentifier>),
    Package(Ref<PackageIdentifier>),
    Game(Ref<GameIdentifier>),
    Theorem(Ref<TheoremIdentifier>),
}

pub enum OracleIdentifier {
    Import(Ref<OracleImportIdentifier>),
    Definition(Ref<OracleDefinitionIdentifier>),
    Composition(Ref<OracleCompositionIdentifier>),
}

#[derive(Debug, Clone, Copy)]
pub struct MissingResolutionDiag {
    pub ident: GlobalRefId,
    pub table: &'static str,
}

impl From<MissingResolutionDiag> for Diagnostic {
    fn from(value: MissingResolutionDiag) -> Self {
        Self::MissingResolution(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UndefinedIdentifierDiag {
    pub ident: GlobalRefId,
}

impl UndefinedIdentifierDiag {
    pub fn new<IK: IdentifierKind>(ident: Ref<AstIdentifier<IK>>) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
        }
    }
}

impl From<UndefinedIdentifierDiag> for Diagnostic {
    fn from(value: UndefinedIdentifierDiag) -> Self {
        Self::UndefinedIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedConstValueIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedConstValueIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedConstValueIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedConstValueIdentifierDiag) -> Self {
        Self::ExpectedConstValueIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedValueIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedValueIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedValueIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedValueIdentifierDiag) -> Self {
        Self::ExpectedValueIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AssignToConstDiag {
    pub ident: GlobalRefId,
}

impl AssignToConstDiag {
    pub fn new<IK: IdentifierKind>(ident: Ref<AstIdentifier<IK>>) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
        }
    }
}

impl From<AssignToConstDiag> for Diagnostic {
    fn from(value: AssignToConstDiag) -> Self {
        Self::AssignToConst(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedTypeIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedTypeIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedTypeIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedTypeIdentifierDiag) -> Self {
        Self::ExpectedTypeIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedTypeArgIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedTypeArgIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedTypeArgIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedTypeArgIdentifierDiag) -> Self {
        Self::ExpectedTypeArgIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedOracleIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedOracleIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedOracleIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedOracleIdentifierDiag) -> Self {
        Self::ExpectedOracleIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedPackageIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedPackageIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedPackageIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedPackageIdentifierDiag) -> Self {
        Self::ExpectedPackageIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedPackageInstanceIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedPackageInstanceIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedPackageInstanceIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedPackageInstanceIdentifierDiag) -> Self {
        Self::ExpectedPackageInstanceIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedGameIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedGameIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedGameIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedGameIdentifierDiag) -> Self {
        Self::ExpectedGameIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedGameInstanceIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedGameInstanceIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedGameInstanceIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedGameInstanceIdentifierDiag) -> Self {
        Self::ExpectedGameInstanceIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExpectedAssumptionIdentifierDiag {
    pub ident: GlobalRefId,
    pub decl: DeclarationType,
}

impl ExpectedAssumptionIdentifierDiag {
    pub fn new<IK: IdentifierKind>(
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        Self {
            ident: ident.global_ref_id(),
            decl: decl.decl_type(),
        }
    }
}

impl From<ExpectedAssumptionIdentifierDiag> for Diagnostic {
    fn from(value: ExpectedAssumptionIdentifierDiag) -> Self {
        Self::ExpectedAssumptionIdentifier(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PackageDoesNotImportOracleDiag {
    pub compose_oracle: Ref<identifier::OracleCompositionIdentifier>,
    pub compose_pkg_inst_left: Ref<identifier::PackageInstanceIdentifier>,
    pub pkg_inst: Option<Ref<game::InstanceBlock>>,
}

impl PackageDoesNotImportOracleDiag {
    pub fn new(
        oracle_ident: Ref<identifier::OracleCompositionIdentifier>,
        pkg_inst_ident: Ref<identifier::PackageInstanceIdentifier>,
        inst: Option<Ref<game::InstanceBlock>>,
    ) -> Self {
        Self {
            compose_oracle: oracle_ident,
            compose_pkg_inst_left: pkg_inst_ident,
            pkg_inst: inst,
        }
    }
}

impl From<PackageDoesNotImportOracleDiag> for Diagnostic {
    fn from(value: PackageDoesNotImportOracleDiag) -> Self {
        Self::PackageDoesNotImportOracle(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PackageDoesNotDefineOracleDiag {
    pub compose_oracle: Ref<identifier::OracleCompositionIdentifier>,
    pub compose_pkg_inst_left: Ref<identifier::PackageInstanceIdentifier>,
    pub pkg_inst: Option<Ref<game::InstanceBlock>>,
}

impl PackageDoesNotDefineOracleDiag {
    pub fn new(
        oracle_ident: Ref<identifier::OracleCompositionIdentifier>,
        pkg_inst_ident: Ref<identifier::PackageInstanceIdentifier>,
        inst: Option<Ref<game::InstanceBlock>>,
    ) -> Self {
        Self {
            compose_oracle: oracle_ident,
            compose_pkg_inst_left: pkg_inst_ident,
            pkg_inst: inst,
        }
    }
}

impl From<PackageDoesNotDefineOracleDiag> for Diagnostic {
    fn from(value: PackageDoesNotDefineOracleDiag) -> Self {
        Self::PackageDoesNotDefineOracle(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AdversaryAsCalleeDiag {
    pub ident: Ref<identifier::OracleCompositionIdentifier>,
}

impl AdversaryAsCalleeDiag {
    pub fn new(at: Ref<identifier::OracleCompositionIdentifier>) -> Self {
        Self { ident: at }
    }
}

impl From<AdversaryAsCalleeDiag> for Diagnostic {
    fn from(value: AdversaryAsCalleeDiag) -> Self {
        Self::AdversaryAsCallee(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CantRedefineBuiltinDiag {
    pub ident: GlobalRefId,
}

impl CantRedefineBuiltinDiag {
    pub fn new<IK>(at: Ref<identifier::Identifier<IK>>) -> Self
    where
        IK: IdentifierKind,
        identifier::Identifier<IK>: NodeType + InArena,
    {
        Self {
            ident: at.global_ref_id(),
        }
    }
}

impl From<CantRedefineBuiltinDiag> for Diagnostic {
    fn from(value: CantRedefineBuiltinDiag) -> Self {
        Self::CantRedefineBuiltin(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AlreadyDefinedDiag {
    pub ident: GlobalRefId,
    pub earlier: GlobalRefId,
}

impl AlreadyDefinedDiag {
    pub fn new<IK, T>(at: Ref<identifier::Identifier<IK>>, earlier: Ref<T>) -> Self
    where
        IK: IdentifierKind,
        identifier::Identifier<IK>: NodeType + InArena,
        T: NodeType + InArena,
    {
        Self {
            ident: at.global_ref_id(),
            earlier: earlier.global_ref_id(),
        }
    }
}

impl From<AlreadyDefinedDiag> for Diagnostic {
    fn from(value: AlreadyDefinedDiag) -> Self {
        Self::AlreadyDefined(value)
    }
}
