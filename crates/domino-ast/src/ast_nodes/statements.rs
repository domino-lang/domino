use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::OracleValueIdentifier,
        list::{Comma, List, ListNoDelim},
        oracles::OracleExpression,
        Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub enum Statement {
    Abort,
    Assert(Ref<AssertStatement>),
    Assign(Ref<AssignStatement>),
    Expression(Ref<ExpressionStatement>),
    IfThenElse(Ref<IfThenElseStatement>),
    Return(Ref<ReturnStatement>),
}

pub type StatementList = ListNoDelim<Statement>;

#[derive(Debug, Clone, Copy)]
pub struct AssertStatement {
    pub expr_trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
    pub semicolon_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct AssignStatement {
    pub pat: Ref<Pattern>,
    pub pre_arrow_trivia: Ref<Trivia>,
    pub post_arrow_trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
    pub semicolon_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct IfThenElseStatement {
    pub cond_trivia: Ref<Trivia>,
    pub cond: Ref<OracleExpression>,
    pub cond_brace_trivia: Ref<Trivia>,
    pub then_block: Ref<StatementList>,
    pub else_block: Option<ElseBlock>,
}

#[derive(Debug, Clone, Copy)]
pub struct ElseBlock {
    pub pre_else_trivia: Ref<Trivia>,
    pub post_else_trivia: Ref<Trivia>,
    pub block: Ref<StatementList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ReturnStatement {
    pub trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
    pub semicolon_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct ExpressionStatement {
    pub expr: Ref<OracleExpression>,
    pub semicolon_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub enum Pattern {
    Identifier(Ref<OracleValueIdentifier>),
    Table(Ref<TablePattern>),
    Tuple(Ref<TuplePattern>),
}

/// Assignment to a table. The table must already be in scope. Since we require the identifier to
/// be bound, we can use Identifier<OracleExpression> instead of Identifier<AssignedIdentifier>.
#[derive(Debug, Clone, Copy)]
pub struct TablePattern {
    pub table_name: Ref<OracleValueIdentifier>,
    pub table_name_trivia: Ref<Trivia>,
    pub index_trivia: Ref<Trivia>,
    pub index: Ref<OracleExpression>,
    pub index_trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct TuplePattern {
    pub items: Ref<PatternList>,
}

pub type PatternList = List<Pattern, Comma>;
