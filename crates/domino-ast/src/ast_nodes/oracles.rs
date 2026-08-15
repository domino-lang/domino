use crate::{
    arena::Ref,
    ast_nodes::{
        expressions,
        identifier::{
            Identifier, OracleDefinitionIdentifierKind, OracleIdentifierKind,
            OracleValueIdentifierKind, ValueIdentifierKind,
        },
        list::{Comma, List},
        statements::StatementList,
        types::{self, Type},
        Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct OracleExpressionKind;

impl expressions::ExpressionKind for OracleExpressionKind {
    type TypeKind = types::PackageTypeKind;
    type ValueIdentifierKind = OracleValueIdentifierKind;
}

pub type OracleExpression = expressions::Expression<OracleExpressionKind>;

pub type BinOpExpression = expressions::BinOpExpression<OracleExpressionKind>;

pub type UnOpExpression = expressions::UnOpExpression<OracleExpressionKind>;

pub type OracleInvocationExpression = expressions::OracleInvocationExpression<OracleExpressionKind>;

pub type ExprList = expressions::ExprList<OracleExpressionKind>;

pub type TableIndexExpression = expressions::TableIndexExpression<OracleExpressionKind>;

pub type SampleExpression = expressions::SampleExpression<OracleExpressionKind>;

pub type ParenExpression = expressions::ParenExpression<OracleExpressionKind>;

pub type CallExpression = expressions::CallExpression<OracleExpressionKind>;

pub type TupleExpression = expressions::TupleExpression<OracleExpressionKind>;

/// oracle <gap> <name> <gap> ( <decl_list> )
#[derive(Debug, Clone, Copy)]
pub struct OracleSignature<OI: OracleIdentifierKind> {
    pub name: Ref<Identifier<OI>>,
    pub trivia: Ref<Trivia>,
    pub args: Ref<OracleValueDeclList>,
    pub ret_ty: Option<OracleReturnType>,
}

#[derive(Debug, Clone, Copy)]
pub struct OracleReturnType {
    pub pre_arrow_trivia: Ref<Trivia>,
    pub post_arrow_trivia: Ref<Trivia>,
    pub ty: Ref<Type<types::PackageTypeKind>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ArgDecl<IK: ValueIdentifierKind> {
    pub name: Ref<Identifier<IK>>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub post_colon_trivia: Ref<Trivia>,
    pub ty: Ref<Type<types::PackageTypeKind>>,
}

pub type OracleValueArgDecl = ArgDecl<OracleValueIdentifierKind>;

/// A list of declarations, usually comma separated. Usually surrounded by parenthises
pub type OracleValueDeclList = List<ArgDecl<OracleValueIdentifierKind>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct OracleDefinition {
    pub sig_trivia: Ref<Trivia>,
    pub oracle_sig: Ref<OracleSignature<OracleDefinitionIdentifierKind>>,
    pub brace_trivia: Ref<Trivia>,
    pub statements: Ref<StatementList>,
}
