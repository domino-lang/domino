//! This module contains the types for a unified expressions type.
//! It unifies the expressions in oracle code, which may be effectful (abort, sample, invoke),
//! and those in constant positions, which may not.
//!
//! Main goals:
//!  -  Make illegal states _representable_: we want to be able to parse code where effectful
//!     expressions are used in illegal places, so we can generate nice error messges.
//!  -  A mechanism for validating and making easy to reuse type invariants that effectful expressions
//!     do not occor in illegal positions.
//!
//! Nice benefit: Less code duplication between expression types.
//!
//! Approach:
//!  -  We have a single Expression type that is generic over an ExpressionKind trait. That trait
//!     might have associated types for the respective IdentifierKinds used in the given context.
//!  -  We define resolution types for pure expressios, which then only have the variants legal in
//!     pure contexts, and have the regular expression subtype as data.

use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{Identifier, OracleImportIdentifier, ValueIdentifierKind},
        list::{Comma, List},
        types::{Type, TypeKind},
        Trivia,
    },
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Eq,
    Neq,
    Lte,
    Lt,
    Gte,
    Gt,

    Add,
    Sub,
    Mul,
    Div,
    Mod,

    And,
    Or,
}

pub trait ExpressionKind {
    type TypeKind: TypeKind;
    type ValueIdentifierKind: ValueIdentifierKind;
}

#[derive(Debug, Clone, Copy)]
pub enum Expression<EK: ExpressionKind> {
    TableIndex(Ref<TableIndexExpression<EK>>),
    Paren(Ref<ParenExpression<EK>>),
    Tuple(Ref<TupleExpression<EK>>),
    Call(Ref<CallExpression<EK>>),
    Identifier(Ref<Identifier<EK::ValueIdentifierKind>>),
    BinOp(Ref<BinOpExpression<EK>>),
    UnOp(Ref<UnOpExpression<EK>>),

    Invoke(Ref<OracleInvocationExpression<EK>>),
    Sample(Ref<SampleExpression<EK>>),

    String,
    Int,
}

/// A list of expressions.
/// Usually comma separated and surrounded by parentheses
pub type ExprList<EK: ExpressionKind> = List<Expression<EK>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct BinOpExpression<EK: ExpressionKind> {
    pub lhs: Ref<Expression<EK>>,
    pub pre_op_trivia: Ref<Trivia>,
    pub op: BinOp,
    pub post_op_trivia: Ref<Trivia>,
    pub rhs: Ref<Expression<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct UnOpExpression<EK: ExpressionKind> {
    pub op: UnOp,
    pub trivia: Ref<Trivia>,
    pub expr: Ref<Expression<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct OracleInvocationExpression<EK: ExpressionKind> {
    /// The name of the invoked oracle.
    pub oracle_name: Ref<OracleImportIdentifier>,

    /// Trivia between name and (
    pub oracle_name_trivia: Ref<Trivia>,

    pub args: Ref<ExprList<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct TableIndexExpression<EK: ExpressionKind> {
    pub table_name: Ref<Identifier<EK::ValueIdentifierKind>>,
    pub table_name_trivia: Ref<Trivia>,
    pub index_trivia: Ref<Trivia>,
    pub index: Ref<Expression<EK>>,
    pub index_trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct SampleExpression<EK: ExpressionKind> {
    pub ty: Ref<Type<EK::TypeKind>>,
    // TODO: sample names
}

#[derive(Debug, Clone, Copy)]
pub struct ParenExpression<EK: ExpressionKind> {
    pub expr_trivia: Ref<Trivia>,
    pub expr: Ref<Expression<EK>>,
    pub trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct CallExpression<EK: ExpressionKind> {
    pub name: Ref<Expression<EK>>,
    pub trivia: Ref<Trivia>,
    pub args: Ref<ExprList<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct TupleExpression<EK: ExpressionKind>(pub Ref<ExprList<EK>>);

#[derive(Clone, Debug)]
pub struct ParseBinOpError(pub String);

impl core::str::FromStr for BinOp {
    type Err = ParseBinOpError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bin_op = match s {
            "or" => BinOp::Or,
            "and" => BinOp::And,

            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,

            "==" => BinOp::Eq,
            "!=" => BinOp::Neq,
            ">=" => BinOp::Gte,
            ">" => BinOp::Gt,
            "<=" => BinOp::Lte,
            "<" => BinOp::Lt,

            other => return Err(ParseBinOpError(other.to_string())),
        };

        Ok(bin_op)
    }
}
