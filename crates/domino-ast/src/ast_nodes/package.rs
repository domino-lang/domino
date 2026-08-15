use crate::{
    arena::Ref,
    ast_nodes::{
        common, expressions,
        identifier::{
            OracleImportIdentifierKind, PackageConstValueIdentifierKind, PackageIdentifier,
            PackageTypeArgumentIdentifierKind, PackageTypeIdentifierKind,
        },
        list::{List, ListNoDelim, Semicolon},
        oracles::{OracleDefinition, OracleSignature},
        package, params, types, Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct PurePackageExpressionKind;

impl expressions::ExpressionKind for PurePackageExpressionKind {
    type TypeKind = types::PackageTypeKind;
    type ValueIdentifierKind = PackageConstValueIdentifierKind;
}

pub type Expression = expressions::Expression<PurePackageExpressionKind>;
pub type BinOpExpression = expressions::BinOpExpression<PurePackageExpressionKind>;
pub type UnOpExpression = expressions::UnOpExpression<PurePackageExpressionKind>;
pub type TableIndexExpression = expressions::TableIndexExpression<PurePackageExpressionKind>;
pub type ParenExpression = expressions::ParenExpression<PurePackageExpressionKind>;
pub type CallExpression = expressions::CallExpression<PurePackageExpressionKind>;
pub type TupleExpression = expressions::TupleExpression<PurePackageExpressionKind>;
pub type ExprList = expressions::ExprList<PurePackageExpressionKind>;

pub type SampleExpression = expressions::SampleExpression<PurePackageExpressionKind>;
pub type OracleInvocationExpression =
    expressions::OracleInvocationExpression<PurePackageExpressionKind>;

pub type PackageTypeDeclList = common::TypeDeclList<PackageTypeIdentifierKind>;
pub type PackageTypeParamBlock = params::TypeParamBlock<PackageTypeIdentifierKind>;

pub type PackageConstDecl = common::ValueDecl<package::PurePackageExpressionKind>;
pub type PackageConstDeclList = common::ConstDeclList<package::PurePackageExpressionKind>;
pub type PackageConstParamBlock = params::ConstParamBlock<package::PurePackageExpressionKind>;

#[derive(Debug, Clone, Copy)]
pub struct StateBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<PackageConstDeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ImportOraclesBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<OracleDeclList>,
}

pub type OracleDeclList = List<OracleSignature<OracleImportIdentifierKind>, Semicolon>;
pub type PackageItemList = ListNoDelim<PackageItem>;

pub type PackageType = types::Type<PackageTypeIdentifierKind>;
pub type PackageArgumentedType = types::ArgumentedType<PackageTypeArgumentIdentifierKind>;
pub type PackageTypeArgument = types::TypeArgument<PackageTypeArgumentIdentifierKind>;

#[derive(Debug, Clone, Copy)]
pub struct Package {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<PackageIdentifier>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<PackageItemList>,
}

#[derive(Debug, Clone, Copy)]
pub enum PackageItem {
    TypeParams(Ref<PackageTypeParamBlock>),
    ConstParams(Ref<PackageConstParamBlock>),
    State(Ref<StateBlock>),
    ImportOracles(Ref<ImportOraclesBlock>),
    OracleDefinition(Ref<OracleDefinition>),
}
