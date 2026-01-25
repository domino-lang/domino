// SPDX-License-Identifier: MIT OR Apache-2.0

use std::ops::Deref as _;

use crate::identifier::Identifier;
use crate::types::Type;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Expression {
    kind: ExpressionKind,
}

impl Expression {
    pub(crate) fn boolean(b: bool) -> Self {
        Self {
            kind: ExpressionKind::BooleanLiteral(if b {
                "true".to_string()
            } else {
                "false".to_string()
            }),
        }
    }

    pub(crate) fn integer(i: i64) -> Self {
        Self {
            kind: ExpressionKind::IntegerLiteral(i),
        }
    }

    pub(crate) fn add(lhs: Expression, rhs: Expression) -> Self {
        Self {
            kind: ExpressionKind::Add(Box::new(lhs), Box::new(rhs)),
        }
    }

    pub(crate) fn into_kind(self) -> ExpressionKind {
        self.kind
    }

    pub(crate) fn from_kind(kind: ExpressionKind) -> Self {
        Self { kind }
    }

    pub(crate) fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub(crate) fn kind_mut(&mut self) -> &mut ExpressionKind {
        &mut self.kind
    }

    pub(crate) fn get_type(&self) -> Type {
        self.kind.get_type()
    }

    pub(crate) fn is_const(&self) -> bool {
        self.kind.is_const()
    }

    pub fn new_equals(exprs: Vec<Expression>) -> Expression {
        Expression {
            kind: ExpressionKind::Equals(exprs.into_iter().collect()),
        }
    }

    pub fn into_identifier(self) -> Option<Identifier> {
        if let ExpressionKind::Identifier(v) = self.kind {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_identifier_mut(&mut self) -> Option<&mut Identifier> {
        if let ExpressionKind::Identifier(v) = &mut self.kind {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_identifier(&self) -> Option<&Identifier> {
        if let ExpressionKind::Identifier(v) = &self.kind {
            Some(v)
        } else {
            None
        }
    }

    pub fn map<F>(&self, f: F) -> Expression
    where
        F: Fn(Expression) -> Expression,
    {
        self.borrow_map(&f)
    }

    pub fn walk(&mut self, f: &mut impl FnMut(&mut Expression) -> bool) {
        if !f(self) {
            return;
        }

        match &mut self.kind {
            ExpressionKind::Bot
            | ExpressionKind::EmptyTable(_)
            | ExpressionKind::None(_)
            | ExpressionKind::Sample(_)
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::BooleanLiteral(_)
            | ExpressionKind::Identifier(_) => {}

            ExpressionKind::Not(expr)
            | ExpressionKind::Some(expr)
            | ExpressionKind::Unwrap(expr)
            | ExpressionKind::TableAccess(_, expr) => expr.as_mut().walk(f),

            ExpressionKind::Tuple(exprs)
            | ExpressionKind::Equals(exprs)
            | ExpressionKind::And(exprs)
            | ExpressionKind::Or(exprs)
            | ExpressionKind::FnCall(_, exprs)
            | ExpressionKind::List(exprs)
            | ExpressionKind::Set(exprs)
            | ExpressionKind::Xor(exprs) => {
                for expr in exprs {
                    expr.walk(f)
                }
            }

            ExpressionKind::Add(lhs, rhs)
            | ExpressionKind::Sub(lhs, rhs)
            | ExpressionKind::Mul(lhs, rhs)
            | ExpressionKind::Div(lhs, rhs)
            | ExpressionKind::LessThen(lhs, rhs)
            | ExpressionKind::GreaterThen(lhs, rhs)
            | ExpressionKind::LessThenEq(lhs, rhs)
            | ExpressionKind::GreaterThenEq(lhs, rhs) => {
                lhs.as_mut().walk(f);
                rhs.as_mut().walk(f)
            }

            _ => {
                panic!("Expression: not implemented: {self:#?}")
            }
        }
    }

    pub fn borrow_map<F>(&self, f: &F) -> Expression
    where
        F: Fn(Expression) -> Expression,
    {
        let kind = match &self.kind {
            ExpressionKind::Bot
            | ExpressionKind::EmptyTable(_)
            | ExpressionKind::None(_)
            | ExpressionKind::Sample(_)
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::BooleanLiteral(_)
            | ExpressionKind::Identifier(_) => self.kind.clone(),

            ExpressionKind::Not(expr) => ExpressionKind::Not(Box::new(expr.borrow_map(f))),
            ExpressionKind::Some(expr) => ExpressionKind::Some(Box::new(expr.borrow_map(f))),
            ExpressionKind::Unwrap(expr) => ExpressionKind::Unwrap(Box::new(expr.borrow_map(f))),
            ExpressionKind::TableAccess(id, expr) => {
                ExpressionKind::TableAccess(id.clone(), Box::new(expr.borrow_map(f)))
            }
            ExpressionKind::Tuple(exprs) => {
                ExpressionKind::Tuple(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            ExpressionKind::Equals(exprs) => {
                ExpressionKind::Equals(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            ExpressionKind::Xor(exprs) => {
                ExpressionKind::Xor(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            ExpressionKind::And(exprs) => {
                ExpressionKind::And(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            ExpressionKind::Or(exprs) => {
                ExpressionKind::Or(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            ExpressionKind::Add(lhs, rhs) => {
                ExpressionKind::Add(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            ExpressionKind::Sub(lhs, rhs) => {
                ExpressionKind::Sub(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            ExpressionKind::Mul(lhs, rhs) => {
                ExpressionKind::Mul(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            ExpressionKind::Div(lhs, rhs) => {
                ExpressionKind::Div(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            ExpressionKind::LessThen(lhs, rhs) => {
                ExpressionKind::LessThen(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            ExpressionKind::GreaterThen(lhs, rhs) => ExpressionKind::GreaterThen(
                Box::new(lhs.borrow_map(f)),
                Box::new(rhs.borrow_map(f)),
            ),
            ExpressionKind::LessThenEq(lhs, rhs) => {
                ExpressionKind::LessThenEq(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            ExpressionKind::GreaterThenEq(lhs, rhs) => ExpressionKind::GreaterThenEq(
                Box::new(lhs.borrow_map(f)),
                Box::new(rhs.borrow_map(f)),
            ),
            ExpressionKind::FnCall(name, exprs) => ExpressionKind::FnCall(
                name.clone(),
                exprs.iter().map(|expr| expr.borrow_map(f)).collect(),
            ),
            ExpressionKind::List(exprs) => {
                ExpressionKind::List(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            ExpressionKind::Set(exprs) => {
                ExpressionKind::Set(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            _ => {
                panic!("Expression: not implemented: {self:#?}")
            }
        };

        f(Expression { kind })
    }

    pub fn mapfold<F, Ac>(&self, init: Ac, f: F) -> (Ac, Expression)
    where
        F: Fn(Ac, Expression) -> (Ac, Expression) + Copy,
        Ac: Clone,
    {
        let (ac, kind) = match &self.kind {
            ExpressionKind::Bot
            | ExpressionKind::EmptyTable(_)
            | ExpressionKind::None(_)
            | ExpressionKind::Sample(_)
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::BooleanLiteral(_)
            | ExpressionKind::Identifier(_) => (init, self.kind.clone()),

            ExpressionKind::Not(expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, ExpressionKind::Not(Box::new(e)))
            }
            ExpressionKind::Some(expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, ExpressionKind::Some(Box::new(e)))
            }
            ExpressionKind::Unwrap(expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, ExpressionKind::Unwrap(Box::new(e)))
            }
            ExpressionKind::TableAccess(id, expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, ExpressionKind::TableAccess(id.clone(), Box::new(e)))
            }
            ExpressionKind::Tuple(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::Tuple(newexprs))
            }
            ExpressionKind::Xor(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::Xor(newexprs))
            }
            ExpressionKind::Equals(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::Equals(newexprs))
            }
            ExpressionKind::And(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::And(newexprs))
            }
            ExpressionKind::Or(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::Or(newexprs))
            }
            ExpressionKind::Add(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, ExpressionKind::Add(Box::new(newlhs), Box::new(newrhs)))
            }
            ExpressionKind::Sub(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, ExpressionKind::Sub(Box::new(newlhs), Box::new(newrhs)))
            }
            ExpressionKind::Mul(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, ExpressionKind::Mul(Box::new(newlhs), Box::new(newrhs)))
            }
            ExpressionKind::Div(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, ExpressionKind::Div(Box::new(newlhs), Box::new(newrhs)))
            }
            ExpressionKind::LessThen(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (
                    ac,
                    ExpressionKind::LessThen(Box::new(newlhs), Box::new(newrhs)),
                )
            }
            ExpressionKind::GreaterThen(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (
                    ac,
                    ExpressionKind::GreaterThen(Box::new(newlhs), Box::new(newrhs)),
                )
            }
            ExpressionKind::LessThenEq(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (
                    ac,
                    ExpressionKind::LessThenEq(Box::new(newlhs), Box::new(newrhs)),
                )
            }
            ExpressionKind::GreaterThenEq(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (
                    ac,
                    ExpressionKind::GreaterThenEq(Box::new(newlhs), Box::new(newrhs)),
                )
            }
            ExpressionKind::FnCall(name, exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();

                (ac, ExpressionKind::FnCall(name.clone(), newexprs))
            }
            ExpressionKind::List(inner) => {
                let mut ac = init;
                let newexprs = inner
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::List(newexprs))
            }
            ExpressionKind::Set(inner) => {
                let mut ac = init;
                let newexprs = inner
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, ExpressionKind::Set(newexprs))
            }
            _ => {
                panic!("Expression: not implemented: {self:#?}")
            }
        };
        f(ac, Expression { kind })
    }
}

impl From<Identifier> for Expression {
    fn from(value: Identifier) -> Self {
        Expression {
            kind: ExpressionKind::Identifier(value),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExpressionKind {
    Bot,
    Sample(Type),
    StringLiteral(String),
    IntegerLiteral(i64),
    BooleanLiteral(String),
    Identifier(Identifier),
    EmptyTable(Type),
    TableAccess(Identifier, Box<Expression>),
    Tuple(Vec<Expression>),
    List(Vec<Expression>),
    Set(Vec<Expression>),
    FnCall(Identifier, Vec<Expression>),
    // or maybe at some point: FnCall(Box<Expression>, Vec<Expression>),
    None(Type),
    Some(Box<Expression>),
    Unwrap(Box<Expression>),

    // Scalar Operations:
    Not(Box<Expression>), // 1-x (not really, in fact: true \mapsto false; false \mapsto true)
    Neg(Box<Expression>), //  -x
    Inv(Box<Expression>), // 1/x

    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Pow(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),
    LessThen(Box<Expression>, Box<Expression>),
    GreaterThen(Box<Expression>, Box<Expression>),
    LessThenEq(Box<Expression>, Box<Expression>),
    GreaterThenEq(Box<Expression>, Box<Expression>),

    Equals(Vec<Expression>),
    And(Vec<Expression>),
    Or(Vec<Expression>),
    Xor(Vec<Expression>),

    // Set/List Operations:
    Sum(Box<Expression>),
    Prod(Box<Expression>),
    Any(Box<Expression>), // set/list or
    All(Box<Expression>), // set/list and
    Union(Box<Expression>),
    Cut(Box<Expression>),
    SetDiff(Box<Expression>),

    Concat(Vec<Expression>),
}

impl ExpressionKind {
    /*
    fn new_identifier(name: &str) -> Expression {
        Expression::Identifier(name.to_string())
    }
    */

    pub fn get_type(&self) -> Type {
        match self {
            ExpressionKind::Bot => Type::Empty,
            ExpressionKind::Sample(ty) => ty.clone(),
            ExpressionKind::StringLiteral(_) => Type::String,
            ExpressionKind::BooleanLiteral(_) => Type::Boolean,
            ExpressionKind::IntegerLiteral(_) => Type::Integer,
            ExpressionKind::Identifier(ident) => ident.get_type(),
            ExpressionKind::EmptyTable(t) => t.clone(),
            ExpressionKind::TableAccess(ident, _) => match ident.get_type() {
                Type::Table(_, value_type) => Type::Maybe(Box::new(value_type.deref().clone())),
                _ => unreachable!(),
            },
            ExpressionKind::Tuple(exprs) => {
                Type::Tuple(exprs.iter().map(|expr| expr.get_type()).collect())
            }
            ExpressionKind::List(exprs) if !exprs.is_empty() => {
                Type::List(Box::new(exprs[0].get_type()))
            }
            ExpressionKind::List(_exprs) => todo!(),
            ExpressionKind::Set(exprs) if !exprs.is_empty() => {
                Type::Set(Box::new(exprs[0].get_type()))
            }
            ExpressionKind::Set(_exprs) => todo!(),
            ExpressionKind::FnCall(ident, _) => match ident.get_type() {
                Type::Fn(_args, ret_type) => *ret_type.clone(),
                other => unreachable!(
                    "found non-function type {:?} when calling function `{}`",
                    other,
                    ident.ident()
                ),
            },
            ExpressionKind::None(ty) => Type::Maybe(Box::new(ty.clone())),
            ExpressionKind::Some(expr) => Type::Maybe(Box::new(expr.get_type())),
            ExpressionKind::Unwrap(expr) => match expr.get_type() {
                Type::Maybe(ty) => *ty,
                _ => unreachable!("Unwrapping non-maybe {expr:?}", expr = expr),
            },

            ExpressionKind::Sum(expr)
            | ExpressionKind::Prod(expr)
            | ExpressionKind::Neg(expr)
            | ExpressionKind::Inv(expr)
            | ExpressionKind::Add(expr, _)
            | ExpressionKind::Sub(expr, _)
            | ExpressionKind::Mul(expr, _)
            | ExpressionKind::Div(expr, _)
            | ExpressionKind::Pow(expr, _)
            | ExpressionKind::Mod(expr, _) => expr.get_type(),

            ExpressionKind::GreaterThen(_, _)
            | ExpressionKind::LessThen(_, _)
            | ExpressionKind::GreaterThenEq(_, _)
            | ExpressionKind::LessThenEq(_, _)
            | ExpressionKind::Not(_)
            | ExpressionKind::Any(_)
            | ExpressionKind::All(_)
            | ExpressionKind::Equals(_)
            | ExpressionKind::And(_)
            | ExpressionKind::Or(_)
            | ExpressionKind::Xor(_) => Type::Boolean,

            ExpressionKind::Concat(exprs) => match exprs[0].get_type() {
                Type::List(t) => *t,
                _ => unreachable!(),
            },

            ExpressionKind::Union(expr)
            | ExpressionKind::Cut(expr)
            | ExpressionKind::SetDiff(expr) => match expr.get_type() {
                Type::List(t) => *t,
                _ => unreachable!(),
            },
        }
    }

    pub fn is_const(&self) -> bool {
        match self {
            ExpressionKind::Bot
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::EmptyTable(_)
            | ExpressionKind::None(_)
            | ExpressionKind::BooleanLiteral(_) => true,

            ExpressionKind::TableAccess(_, _)
            | ExpressionKind::FnCall(_, _)
            | ExpressionKind::Sample(_) => false,

            ExpressionKind::Not(expression)
            | ExpressionKind::Neg(expression)
            | ExpressionKind::Inv(expression)
            | ExpressionKind::Some(expression)
            | ExpressionKind::Unwrap(expression)
            | ExpressionKind::Sum(expression)
            | ExpressionKind::Prod(expression)
            | ExpressionKind::Any(expression)
            | ExpressionKind::All(expression)
            | ExpressionKind::Union(expression)
            | ExpressionKind::Cut(expression)
            | ExpressionKind::SetDiff(expression) => expression.is_const(),

            ExpressionKind::Identifier(ident) => ident.is_const(),

            ExpressionKind::Tuple(exprs)
            | ExpressionKind::List(exprs)
            | ExpressionKind::Set(exprs)
            | ExpressionKind::Equals(exprs)
            | ExpressionKind::And(exprs)
            | ExpressionKind::Or(exprs)
            | ExpressionKind::Xor(exprs)
            | ExpressionKind::Concat(exprs) => exprs.iter().all(Expression::is_const),

            ExpressionKind::Add(lhs, rhs)
            | ExpressionKind::Sub(lhs, rhs)
            | ExpressionKind::Mul(lhs, rhs)
            | ExpressionKind::Div(lhs, rhs)
            | ExpressionKind::Pow(lhs, rhs)
            | ExpressionKind::Mod(lhs, rhs)
            | ExpressionKind::GreaterThen(lhs, rhs)
            | ExpressionKind::LessThen(lhs, rhs)
            | ExpressionKind::GreaterThenEq(lhs, rhs)
            | ExpressionKind::LessThenEq(lhs, rhs) => lhs.is_const() && rhs.is_const(),
        }
    }
}

#[macro_export]
macro_rules! tuple {
    ( $($e:expr),* ) => {
        {
            ExpressionKind::Tuple(vec![ $( $e.clone(), )* ])
        }
    };
}

#[macro_export]
macro_rules! list {
    ( $($e:expr),* ) => {
        {
            ExpressionKind::List(vec![ $( $e.clone(), )* ])
        }
    };
}

#[macro_export]
macro_rules! oracleinvoc {
    ( $name:expr, $($e:expr),* ) => {
        {
            ExpressionKind::OracleInvoc(
                $name.to_string(),
                vec![ $( $e.clone(), )* ],
            )
        }
    };
}

#[macro_export]
macro_rules! fncall {
    ( $name:expr, $($e:expr),* ) => {
        {
            ExpressionKind::FnCall(
                Identifier::Scalar($name.to_string()),
                vec![ $( $e.clone(), )* ],
            )
        }
    };
}
