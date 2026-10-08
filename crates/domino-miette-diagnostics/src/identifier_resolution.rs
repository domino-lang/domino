#![allow(unused_assignments)]

use miette::SourceSpan;

use domino_ast::{ast_nodes::identifier::*, GlobalRefId, NodeTypeRef as _};
use domino_collections::arena::Ref;
use domino_identifier_resolution::{diag as idres, DeclarationType};
use domino_resolutions::{DiagFrom, NamedSource, Resolver};

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
pub enum Diagnostic {
    #[error(transparent)]
    #[diagnostic(transparent)]
    MissingResolution(#[from] MissingResolution),

    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedIdentifier(#[from] UndefinedIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedConstValueIdentifier(#[from] ExpectedConstValueIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedValueIdentifier(#[from] ExpectedValueIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedTypeIdentifier(#[from] ExpectedTypeIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedTypeArgIdentifier(#[from] ExpectedTypeArgIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedOracleIdentifier(#[from] ExpectedOracleIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedPackageIdentifier(#[from] ExpectedPackageIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedPackageInstanceIdentifier(#[from] ExpectedPackageInstanceIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedGameIdentifier(#[from] ExpectedGameIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedGameInstanceIdentifier(#[from] ExpectedGameInstanceIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpectedAssumptionIdentifier(#[from] ExpectedAssumptionIdentifier),

    #[error(transparent)]
    #[diagnostic(transparent)]
    AssignToConst(#[from] AssignToConst),

    #[error(transparent)]
    #[diagnostic(transparent)]
    PackageDoesNotImportOracle(#[from] PackageDoesNotImportOracle),

    #[error(transparent)]
    #[diagnostic(transparent)]
    PackageDoesNotDefineOracle(#[from] PackageDoesNotDefineOracle),

    #[error(transparent)]
    #[diagnostic(transparent)]
    AdversaryAsCallee(#[from] AdversaryAsCallee),

    #[error(transparent)]
    #[diagnostic(transparent)]
    CantRedefineBuiltin(#[from] CantRedefineBuiltin),

    #[error(transparent)]
    #[diagnostic(transparent)]
    AlreadyDefined(#[from] AlreadyDefined),
}

impl Diagnostic {
    pub fn at(&self) -> GlobalRefId {
        match self {
            Diagnostic::MissingResolution(node) => node.global_ref,
            Diagnostic::UndefinedIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedValueIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedConstValueIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedTypeIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedTypeArgIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedOracleIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedPackageIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedPackageInstanceIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedGameIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedGameInstanceIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedAssumptionIdentifier(node) => node.global_ref,
            Diagnostic::AssignToConst(node) => node.global_ref,
            Diagnostic::PackageDoesNotImportOracle(node) => node.global_ref,
            Diagnostic::PackageDoesNotDefineOracle(node) => node.global_ref,
            Diagnostic::AdversaryAsCallee(node) => node.global_ref,
            Diagnostic::CantRedefineBuiltin(node) => node.global_ref,
            Diagnostic::AlreadyDefined(node) => node.global_ref,
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

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("internal error: missing resolution for {table}")]
#[diagnostic(code(domino::resolve::idents::internal::missing_resolution))]
pub struct MissingResolution {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub table: &'static str,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::MissingResolutionDiag> for MissingResolution {
    fn diag_from<'a>(value: idres::MissingResolutionDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            table: value.table,
            global_ref: value.ident,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("undefined identifier")]
#[diagnostic(code(domino::resolve::idents::undefined))]
pub struct UndefinedIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::UndefinedIdentifierDiag> for UndefinedIdentifier {
    fn diag_from<'a>(value: idres::UndefinedIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected a const value identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_const_value))]
pub struct ExpectedConstValueIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedConstValueIdentifierDiag> for ExpectedConstValueIdentifier {
    fn diag_from<'a>(
        value: idres::ExpectedConstValueIdentifierDiag,
        resolver: Resolver<'a>,
    ) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected a value identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_value))]
pub struct ExpectedValueIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedValueIdentifierDiag> for ExpectedValueIdentifier {
    fn diag_from<'a>(value: idres::ExpectedValueIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("assigning to a constant")]
#[diagnostic(code(domino::resolve::idents::assign_to_const))]
pub struct AssignToConst {
    #[label("this identifier is a constant")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::AssignToConstDiag> for AssignToConst {
    fn diag_from<'a>(value: idres::AssignToConstDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an type identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_type))]
pub struct ExpectedTypeIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedTypeIdentifierDiag> for ExpectedTypeIdentifier {
    fn diag_from<'a>(value: idres::ExpectedTypeIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an type arg identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_type_arg))]
pub struct ExpectedTypeArgIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedTypeArgIdentifierDiag> for ExpectedTypeArgIdentifier {
    fn diag_from<'a>(value: idres::ExpectedTypeArgIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an oracle identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_oracle))]
pub struct ExpectedOracleIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedOracleIdentifierDiag> for ExpectedOracleIdentifier {
    fn diag_from<'a>(value: idres::ExpectedOracleIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an package identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_package))]
pub struct ExpectedPackageIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedPackageIdentifierDiag> for ExpectedPackageIdentifier {
    fn diag_from<'a>(value: idres::ExpectedPackageIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an package instance identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_package_instance))]
pub struct ExpectedPackageInstanceIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedPackageInstanceIdentifierDiag> for ExpectedPackageInstanceIdentifier {
    fn diag_from<'a>(
        value: idres::ExpectedPackageInstanceIdentifierDiag,
        resolver: Resolver<'a>,
    ) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected a game identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_game))]
pub struct ExpectedGameIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedGameIdentifierDiag> for ExpectedGameIdentifier {
    fn diag_from<'a>(value: idres::ExpectedGameIdentifierDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected a game instance identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_game_instance))]
pub struct ExpectedGameInstanceIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedGameInstanceIdentifierDiag> for ExpectedGameInstanceIdentifier {
    fn diag_from<'a>(
        value: idres::ExpectedGameInstanceIdentifierDiag,
        resolver: Resolver<'a>,
    ) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an assumption identifier, got a {decl_type}")]
#[diagnostic(code(domino::resolve::idents::expected_assumption))]
pub struct ExpectedAssumptionIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    pub decl_type: DeclarationType,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::ExpectedAssumptionIdentifierDiag> for ExpectedAssumptionIdentifier {
    fn diag_from<'a>(
        value: idres::ExpectedAssumptionIdentifierDiag,
        resolver: Resolver<'a>,
    ) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            decl_type: value.decl,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("oracle composition assigns an oracle that is not imported by the package")]
#[diagnostic(code(domino::resolve::idents::package_does_not_import_oracle))]
pub struct PackageDoesNotImportOracle {
    #[label("this oracle is not imported...")]
    pub compose_oracle: SourceSpan,

    #[label("...by this package instance.{dots}", dots = if pkg_inst.is_none() {""} else {".."})]
    pub compose_pkg_inst_left: SourceSpan,

    #[label("...which is instantiated here.")]
    pub pkg_inst: Option<SourceSpan>,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::PackageDoesNotImportOracleDiag> for PackageDoesNotImportOracle {
    fn diag_from<'a>(value: idres::PackageDoesNotImportOracleDiag, resolver: Resolver<'a>) -> Self {
        Self {
            compose_oracle: resolver.span(value.compose_oracle),
            compose_pkg_inst_left: resolver.span(value.compose_pkg_inst_left),
            pkg_inst: value.pkg_inst.map(|inst| resolver.span(inst)),
            global_ref: value.compose_oracle.global_ref_id(),
            source_code: resolver.named_source(value.compose_oracle),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("oracle composition assigns an oracle that is not defined by the package")]
#[diagnostic(code(domino::resolve::idents::package_does_not_define_oracle))]
pub struct PackageDoesNotDefineOracle {
    #[label("this oracle is not defined...")]
    pub compose_oracle: SourceSpan,

    #[label("...by this package instance.{dots}", dots = if pkg_inst.is_none() {""} else {".."})]
    pub compose_pkg_inst_left: SourceSpan,

    #[label("...which is instantiated here.")]
    pub pkg_inst: Option<SourceSpan>,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::PackageDoesNotDefineOracleDiag> for PackageDoesNotDefineOracle {
    fn diag_from<'a>(value: idres::PackageDoesNotDefineOracleDiag, resolver: Resolver<'a>) -> Self {
        Self {
            compose_oracle: resolver.span(value.compose_oracle),
            compose_pkg_inst_left: resolver.span(value.compose_pkg_inst_left),
            pkg_inst: value.pkg_inst.map(|inst| resolver.span(inst)),
            global_ref: value.compose_oracle.global_ref_id(),
            source_code: resolver.named_source(value.compose_oracle),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("adversary is not allowed in callee/right-hand-side position in a composition")]
#[diagnostic(code(domino::resolve::idents::adversary_as_callee_))]
pub struct AdversaryAsCallee {
    #[label("adversary composed in a callee position here")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::AdversaryAsCalleeDiag> for AdversaryAsCallee {
    fn diag_from<'a>(value: idres::AdversaryAsCalleeDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.span(value.ident),
            global_ref: value.ident.global_ref_id(),
            source_code: resolver.named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("this identifier is a builtin an can't be redefined")]
#[diagnostic(code(domino::resolve::idents::cant_redefine_builtin))]
pub struct CantRedefineBuiltin {
    #[label("this identifier is a builtin")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::CantRedefineBuiltinDiag> for CantRedefineBuiltin {
    fn diag_from<'a>(value: idres::CantRedefineBuiltinDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            global_ref: value.ident,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("this identifier has been defined before")]
#[diagnostic(code(domino::resolve::idents::already_defined))]
pub struct AlreadyDefined {
    #[label("this identifier has been defined earlier")]
    pub at: SourceSpan,

    #[label("earlier definition is here")]
    pub earlier: SourceSpan,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl DiagFrom<idres::AlreadyDefinedDiag> for AlreadyDefined {
    fn diag_from<'a>(value: idres::AlreadyDefinedDiag, resolver: Resolver<'a>) -> Self {
        Self {
            at: resolver.global_span(value.ident),
            earlier: resolver.global_span(value.earlier),
            global_ref: value.ident,
            source_code: resolver.global_named_source(value.ident),
        }
    }
}

macro_rules! impl_intodiag_diagnostic {
    ($idres:ty, $here:ty) => {
        impl DiagFrom<$idres> for Diagnostic {
            fn diag_from<'a>(value: $idres, resolver: Resolver<'a>) -> Self {
                <$here>::diag_from(value, resolver).into()
            }
        }
    };
}

impl_intodiag_diagnostic!(idres::MissingResolutionDiag, MissingResolution);
impl_intodiag_diagnostic!(idres::UndefinedIdentifierDiag, UndefinedIdentifier);

impl_intodiag_diagnostic!(
    idres::ExpectedConstValueIdentifierDiag,
    ExpectedConstValueIdentifier
);

impl_intodiag_diagnostic!(idres::ExpectedValueIdentifierDiag, ExpectedValueIdentifier);
impl_intodiag_diagnostic!(idres::AssignToConstDiag, AssignToConst);
impl_intodiag_diagnostic!(idres::ExpectedTypeIdentifierDiag, ExpectedTypeIdentifier);

impl_intodiag_diagnostic!(
    idres::ExpectedTypeArgIdentifierDiag,
    ExpectedTypeArgIdentifier
);

impl_intodiag_diagnostic!(
    idres::ExpectedOracleIdentifierDiag,
    ExpectedOracleIdentifier
);

impl_intodiag_diagnostic!(
    idres::ExpectedPackageIdentifierDiag,
    ExpectedPackageIdentifier
);

impl_intodiag_diagnostic!(
    idres::ExpectedPackageInstanceIdentifierDiag,
    ExpectedPackageInstanceIdentifier
);

impl_intodiag_diagnostic!(idres::ExpectedGameIdentifierDiag, ExpectedGameIdentifier);

impl_intodiag_diagnostic!(
    idres::ExpectedGameInstanceIdentifierDiag,
    ExpectedGameInstanceIdentifier
);

impl_intodiag_diagnostic!(
    idres::ExpectedAssumptionIdentifierDiag,
    ExpectedAssumptionIdentifier
);

impl_intodiag_diagnostic!(
    idres::PackageDoesNotImportOracleDiag,
    PackageDoesNotImportOracle
);

impl_intodiag_diagnostic!(
    idres::PackageDoesNotDefineOracleDiag,
    PackageDoesNotDefineOracle
);

impl_intodiag_diagnostic!(idres::AdversaryAsCalleeDiag, AdversaryAsCallee);

impl_intodiag_diagnostic!(idres::CantRedefineBuiltinDiag, CantRedefineBuiltin);

impl_intodiag_diagnostic!(idres::AlreadyDefinedDiag, AlreadyDefined);

impl DiagFrom<idres::Diagnostic> for Diagnostic {
    fn diag_from<'a>(value: idres::Diagnostic, resolver: Resolver<'a>) -> Self {
        match value {
            idres::Diagnostic::MissingResolution(diag) => {
                MissingResolution::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::UndefinedIdentifier(diag) => {
                UndefinedIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedConstValueIdentifier(diag) => {
                ExpectedConstValueIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedValueIdentifier(diag) => {
                ExpectedValueIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedTypeIdentifier(diag) => {
                ExpectedTypeIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedTypeArgIdentifier(diag) => {
                ExpectedTypeArgIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedOracleIdentifier(diag) => {
                ExpectedOracleIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedPackageIdentifier(diag) => {
                ExpectedPackageIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedPackageInstanceIdentifier(diag) => {
                ExpectedPackageInstanceIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedGameIdentifier(diag) => {
                ExpectedGameIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedGameInstanceIdentifier(diag) => {
                ExpectedGameInstanceIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::ExpectedAssumptionIdentifier(diag) => {
                ExpectedAssumptionIdentifier::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::AssignToConst(diag) => {
                AssignToConst::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::PackageDoesNotImportOracle(diag) => {
                PackageDoesNotImportOracle::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::PackageDoesNotDefineOracle(diag) => {
                PackageDoesNotDefineOracle::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::AdversaryAsCallee(diag) => {
                AdversaryAsCallee::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::CantRedefineBuiltin(diag) => {
                CantRedefineBuiltin::diag_from(diag, resolver).into()
            }
            idres::Diagnostic::AlreadyDefined(diag) => {
                AlreadyDefined::diag_from(diag, resolver).into()
            }
        }
    }
}
