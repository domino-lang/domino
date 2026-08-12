#![allow(unused_assignments)]

use miette::SourceSpan;

use domino_ast::{
    arena::{Arena, Ref},
    ast_nodes::{
        game,
        identifier::{self, Identifier as AstIdentifier, *},
        InArena, NodeType,
    },
    GlobalRefId,
};
use domino_diagnostic::{NamedSource, Resolver};

use crate::DeclarationType;

pub type Diagnostics = Arena<Diagnostic>;

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
pub enum Diagnostic {
    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedIdentifier(#[from] UndefinedIdentifier),

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
}

impl Diagnostic {
    pub fn at(&self) -> GlobalRefId {
        match self {
            Diagnostic::UndefinedIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedValueIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedTypeIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedTypeArgIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedOracleIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedPackageIdentifier(node) => node.global_ref,
            Diagnostic::ExpectedPackageInstanceIdentifier(node) => node.global_ref,
            Diagnostic::AssignToConst(node) => node.global_ref,
            Diagnostic::PackageDoesNotImportOracle(node) => node.global_ref,
            Diagnostic::PackageDoesNotDefineOracle(node) => node.global_ref,
            Diagnostic::AdversaryAsCallee(node) => node.global_ref,
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
#[error("undefined identifier")]
#[diagnostic(code(domino::resolve::idents::undefined))]
pub struct UndefinedIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub global_ref: GlobalRefId,

    #[source_code]
    pub source_code: NamedSource,
}

impl UndefinedIdentifier {
    pub fn new<IK: IdentifierKind>(dx: Resolver, ident: Ref<AstIdentifier<IK>>) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
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

impl ExpectedValueIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            source_code,
            global_ref: ident.global_ref_id(),
            decl_type: decl.decl_type(),
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

impl AssignToConst {
    pub fn new<IK: IdentifierKind>(dx: Resolver, ident: Ref<AstIdentifier<IK>>) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
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

impl ExpectedTypeIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
            decl_type: decl.decl_type(),
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

impl ExpectedTypeArgIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
            decl_type: decl.decl_type(),
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

impl ExpectedOracleIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
            decl_type: decl.decl_type(),
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

impl ExpectedPackageIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
            decl_type: decl.decl_type(),
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

impl ExpectedPackageInstanceIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: impl crate::Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            global_ref: ident.global_ref_id(),
            source_code,
            decl_type: decl.decl_type(),
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

impl PackageDoesNotImportOracle {
    pub fn new(
        dx: Resolver,
        oracle_ident: Ref<identifier::OracleCompositionIdentifier>,
        pkg_inst_ident: Ref<identifier::PackageInstanceIdentifier>,
        inst: Option<Ref<game::InstanceBlock>>,
    ) -> Self {
        let compose_oracle = dx.span(oracle_ident);
        let compose_pkg_inst_left = dx.span(pkg_inst_ident);
        let pkg_inst = inst.map(|inst| dx.span(inst));
        let source_code = dx.named_source(oracle_ident);
        Self {
            compose_oracle,
            compose_pkg_inst_left,
            pkg_inst,
            global_ref: oracle_ident.global_ref_id(),
            source_code,
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

impl PackageDoesNotDefineOracle {
    pub fn new(
        dx: Resolver,
        oracle_ident: Ref<identifier::OracleCompositionIdentifier>,
        pkg_inst_ident: Ref<identifier::PackageInstanceIdentifier>,
        inst: Option<Ref<game::InstanceBlock>>,
    ) -> Self {
        let compose_oracle = dx.span(oracle_ident);
        let compose_pkg_inst_left = dx.span(pkg_inst_ident);
        let pkg_inst = inst.map(|inst| dx.span(inst));
        let source_code = dx.named_source(oracle_ident);
        Self {
            compose_oracle,
            compose_pkg_inst_left,
            pkg_inst,
            global_ref: oracle_ident.global_ref_id(),
            source_code,
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

impl AdversaryAsCallee {
    pub fn new(dx: Resolver, at: Ref<identifier::OracleCompositionIdentifier>) -> Self {
        let global_ref = at.global_ref_id();
        let source_code = dx.named_source(at);
        let at = dx.span(at);
        Self {
            at,
            global_ref,
            source_code,
        }
    }
}
