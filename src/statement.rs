// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::SourceSpan;
use pest::Span;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CodeBlock(pub Vec<Statement>);

/// A pattern on the left-hand side of an assignment
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    /// Simple identifier: `x`
    Ident(Identifier),
    /// Table access: `T[index]`
    Table {
        ident: Identifier,
        index: Expression,
    },
    /// Tuple destructuring: `(a, b, c)`
    Tuple(Vec<Identifier>),
}

/// The right-hand side of an assignment
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssignmentRhs {
    /// Regular expression: `x <- expr`
    Expression(Expression),
    /// Sample from distribution: `x <- $Type`
    Sample {
        ty: Type,
        sample_name: Option<String>,
        sample_id: Option<usize>,
    },
    /// Oracle invocation: `x <- invoke Oracle(args)`
    Invoke {
        oracle_name: String,
        args: Vec<Expression>,
        target_inst_name: Option<String>,
        return_type: Option<Type>,
    },
}

/// An assignment statement: pattern <- rhs
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment {
    pub(crate) pattern: Pattern,
    pub(crate) rhs: AssignmentRhs,
}

/// Standalone oracle invocation (discards return value): invoke Oracle(args)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvokeOracle {
    pub oracle_name: String,
    pub args: Vec<Expression>,
    pub target_inst_name: Option<String>,
    pub file_pos: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    Abort(SourceSpan),
    Return(Option<Expression>, SourceSpan),
    Assignment(Assignment, SourceSpan),
    InvokeOracle(InvokeOracle),
    IfThenElse(IfThenElse),
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
        match self {
            Statement::Abort(file_pos)
            | Statement::Return(_, file_pos)
            | Statement::Assignment(_, file_pos)
            | Statement::For(_, _, _, _, file_pos) => *file_pos,
            Statement::InvokeOracle(InvokeOracle { file_pos, .. }) => *file_pos,
            Statement::IfThenElse(IfThenElse { full_span, .. }) => *full_span,
        }
    }
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
