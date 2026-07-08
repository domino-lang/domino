use std::backtrace::Backtrace;

use domino_ast::{
    arena::Ref,
    ast_nodes::{
        identifier::{Identifier as AstIdentifier, *},
        InArena, NodeType,
    },
};
use domino_diagnostic::{NamedSource, Resolver};
use miette::SourceSpan;

use crate::Declaration;

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
    AssignToConst(#[from] AssignToConst),
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

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("undefined identifier")]
#[diagnostic(code(domino::resolve::idents::undefined))]
pub struct UndefinedIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

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
        Self { at, source_code }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected a value identifier, got a {decl_type}", decl_type = decl.decl_type())]
#[diagnostic(code(domino::resolve::idents::expected_value))]
pub struct ExpectedValueIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub decl: Declaration,

    #[source_code]
    pub source_code: NamedSource,
}

impl ExpectedValueIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            source_code,
            decl,
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("assigning to a constant")]
#[diagnostic(code(domino::resolve::idents::assign_to_const))]
pub struct AssignToConst {
    #[label("this identifier is a constant")]
    pub at: SourceSpan,

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
        Self { at, source_code }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an type identifier, got a {decl_type}", decl_type = decl.decl_type())]
#[diagnostic(code(domino::resolve::idents::expected_type))]
pub struct ExpectedTypeIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub decl: Declaration,

    #[source_code]
    pub source_code: NamedSource,
}

impl ExpectedTypeIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        dbg!(Backtrace::capture());
        dbg!(decl);
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            source_code,
            decl,
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an type arg identifier, got a {decl_type}", decl_type = decl.decl_type())]
#[diagnostic(code(domino::resolve::idents::expected_type_arg))]
pub struct ExpectedTypeArgIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub decl: Declaration,

    #[source_code]
    pub source_code: NamedSource,
}

impl ExpectedTypeArgIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            source_code,
            decl,
        }
    }
}

#[derive(Debug, Clone, miette::Diagnostic, thiserror::Error)]
#[error("expected an oracle identifier, got a {decl_type}", decl_type = decl.decl_type())]
#[diagnostic(code(domino::resolve::idents::expected_oracle))]
pub struct ExpectedOracleIdentifier {
    #[label("this identifier")]
    pub at: SourceSpan,

    pub decl: Declaration,

    #[source_code]
    pub source_code: NamedSource,
}

impl ExpectedOracleIdentifier {
    pub fn new<IK: IdentifierKind>(
        dx: Resolver,
        ident: Ref<AstIdentifier<IK>>,
        decl: Declaration,
    ) -> Self
    where
        AstIdentifier<IK>: InArena + NodeType,
    {
        let at = dx.span(ident);
        let source_code = dx.named_source(ident);
        Self {
            at,
            source_code,
            decl,
        }
    }
}
