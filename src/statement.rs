// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::SourceSpan;
use pest::Span;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CodeBlock(pub Vec<Statement>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    Abort(SourceSpan),
    Return(Option<Expression>, SourceSpan),
    Assign(Identifier, Option<Expression>, Expression, SourceSpan),
    Parse(Vec<Identifier>, Expression, SourceSpan),
    IfThenElse(IfThenElse),
    Sample(
        Identifier,
        Option<Expression>,
        Option<usize>,
        Type,
        Option<String>,
        SourceSpan,
    ),
    InvokeOracle(InvokeOracleStatement),
    For(Identifier, Expression, Expression, CodeBlock, SourceSpan),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfThenElse {
    pub(crate) cond: Expression,
    pub(crate) then_block: CodeBlock,
    pub(crate) else_block: CodeBlock,
    pub(crate) then_span: SourceSpan,
    pub(crate) else_span: SourceSpan,
    pub(crate) full_span: SourceSpan,
}

impl Statement {
    pub fn file_pos(&self) -> SourceSpan {
        *match self {
            Statement::Abort(file_pos)
            | Statement::Return(_, file_pos)
            | Statement::Assign(_, _, _, file_pos)
            | Statement::Parse(_, _, file_pos)
            | Statement::IfThenElse(IfThenElse {
                full_span: file_pos,
                ..
            })
            | Statement::Sample(_, _, _, _, _, file_pos)
            | Statement::InvokeOracle(InvokeOracleStatement { file_pos, .. })
            | Statement::For(_, _, _, _, file_pos) => file_pos,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvokeOracleStatement {
    pub(crate) id: Identifier,
    pub(crate) opt_idx: Option<Expression>,
    pub(crate) name: String,
    pub(crate) args: Vec<Expression>,
    pub(crate) target_inst_name: Option<String>,
    pub(crate) ty: Option<Type>,
    pub(crate) file_pos: SourceSpan,
}

#[derive(Clone, PartialEq, PartialOrd, Ord, Eq, Hash, Debug)]
pub struct FilePosition {
    file_name: String,
    start_line_col: (usize, usize),
    end_line_col: (usize, usize),
}

impl FilePosition {
    pub fn new(file_name: String, line_start: usize, line_end: usize) -> FilePosition {
        FilePosition {
            file_name,
            start_line_col: (line_start, 0),
            end_line_col: (line_end, 0),
        }
    }

    pub fn from_span(file_name: impl ToString, span: Span) -> FilePosition {
        FilePosition {
            file_name: file_name.to_string(),
            start_line_col: span.start_pos().line_col(),
            end_line_col: span.end_pos().line_col(),
        }
    }

    pub fn file_name(&self) -> &str {
        &self.file_name
    }

    pub fn start(&self) -> (usize, usize) {
        self.start_line_col
    }

    pub fn end(&self) -> (usize, usize) {
        self.end_line_col
    }

    pub fn line_start(&self) -> usize {
        self.start_line_col.0
    }

    pub fn line_end(&self) -> usize {
        self.end_line_col.0
    }
}

impl std::fmt::Display for FilePosition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            file_name,
            start_line_col: (line_start, col_start),
            end_line_col: (line_end, col_end),
        } = self;

        write!(
            f,
            "{file_name}:{line_start}:{col_start}..{line_end}:{col_end}"
        )
    }
}

#[macro_export]
macro_rules! block {
    ( $( $s:expr ),* ) => {
        {
            CodeBlock(vec![ $( $s.clone(), )* ])
        }
    }
}
