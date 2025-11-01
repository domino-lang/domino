// SPDX-License-Identifier: MIT OR Apache-2.0

use std::ops::Deref as _;

use crate::identifier::Identifier;
use crate::types::Type;

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expression {
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

impl Expression {
    /*
    fn new_identifier(name: &str) -> Expression {
        Expression::Identifier(name.to_string())
    }
    */

    pub fn get_type(&self) -> Type {
        match self {
            Expression::Bot => Type::Empty,
            Expression::Sample(ty) => ty.clone(),
            Expression::StringLiteral(_) => Type::String,
            Expression::BooleanLiteral(_) => Type::Boolean,
            Expression::IntegerLiteral(_) => Type::Integer,
            Expression::Identifier(ident) => ident.get_type(),
            Expression::EmptyTable(t) => t.clone(),
            Expression::TableAccess(ident, _) => match ident.get_type() {
                Type::Table(_, value_type) => Type::Maybe(Box::new(value_type.deref().clone())),
                _ => unreachable!(),
            },
            Expression::Tuple(exprs) => {
                Type::Tuple(exprs.iter().map(|expr| expr.get_type()).collect())
            }
            Expression::List(exprs) if !exprs.is_empty() => {
                Type::List(Box::new(exprs[0].get_type()))
            }
            Expression::List(_exprs) => todo!(),
            Expression::Set(exprs) if !exprs.is_empty() => Type::Set(Box::new(exprs[0].get_type())),
            Expression::Set(_exprs) => todo!(),
            Expression::FnCall(ident, _) => match ident.get_type() {
                Type::Fn(_args, ret_type) => *ret_type.clone(),
                other => unreachable!(
                    "found non-function type {:?} when calling function `{}`",
                    other,
                    ident.ident()
                ),
            },
            Expression::None(ty) => Type::Maybe(Box::new(ty.clone())),
            Expression::Some(expr) => Type::Maybe(Box::new(expr.get_type())),
            Expression::Unwrap(expr) => match expr.get_type() {
                Type::Maybe(ty) => *ty,
                _ => unreachable!("Unwrapping non-maybe {expr:?}", expr = expr),
            },

            Expression::Sum(expr)
            | Expression::Prod(expr)
            | Expression::Neg(expr)
            | Expression::Inv(expr)
            | Expression::Add(expr, _)
            | Expression::Sub(expr, _)
            | Expression::Mul(expr, _)
            | Expression::Div(expr, _)
            | Expression::Pow(expr, _)
            | Expression::Mod(expr, _) => expr.get_type(),

            Expression::Not(_)
            | Expression::Any(_)
            | Expression::All(_)
            | Expression::Equals(_)
            | Expression::And(_)
            | Expression::Or(_)
            | Expression::Xor(_) => Type::Boolean,

            Expression::Concat(exprs) => match exprs[0].get_type() {
                Type::List(t) => *t,
                _ => unreachable!(),
            },

            Expression::Union(expr) | Expression::Cut(expr) | Expression::SetDiff(expr) => {
                match expr.get_type() {
                    Type::List(t) => *t,
                    _ => unreachable!(),
                }
            }
        }
    }

    pub fn is_const(&self) -> bool {
        match self {
            Expression::Bot
            | Expression::StringLiteral(_)
            | Expression::IntegerLiteral(_)
            | Expression::EmptyTable(_)
            | Expression::None(_)
            | Expression::BooleanLiteral(_) => true,

            Expression::TableAccess(_, _) | Expression::FnCall(_, _) | Expression::Sample(_) => {
                false
            }

            Expression::Not(expression)
            | Expression::Neg(expression)
            | Expression::Inv(expression)
            | Expression::Some(expression)
            | Expression::Unwrap(expression)
            | Expression::Sum(expression)
            | Expression::Prod(expression)
            | Expression::Any(expression)
            | Expression::All(expression)
            | Expression::Union(expression)
            | Expression::Cut(expression)
            | Expression::SetDiff(expression) => expression.is_const(),

            Expression::Identifier(ident) => ident.is_const(),

            Expression::Tuple(exprs)
            | Expression::List(exprs)
            | Expression::Set(exprs)
            | Expression::Equals(exprs)
            | Expression::And(exprs)
            | Expression::Or(exprs)
            | Expression::Xor(exprs)
            | Expression::Concat(exprs) => exprs.iter().all(Expression::is_const),

            Expression::Add(lhs, rhs)
            | Expression::Sub(lhs, rhs)
            | Expression::Mul(lhs, rhs)
            | Expression::Div(lhs, rhs)
            | Expression::Pow(lhs, rhs)
            | Expression::Mod(lhs, rhs) => lhs.is_const() && rhs.is_const(),
        }
    }

    pub fn walk(&mut self, f: &mut impl FnMut(&mut Expression) -> bool) {
        if !f(self) {
            return;
        }

        match self {
            Expression::Bot
            | Expression::EmptyTable(_)
            | Expression::None(_)
            | Expression::Sample(_)
            | Expression::StringLiteral(_)
            | Expression::IntegerLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::Identifier(_) => {}

            Expression::Not(expr)
            | Expression::Some(expr)
            | Expression::Unwrap(expr)
            | Expression::TableAccess(_, expr) => expr.as_mut().walk(f),

            Expression::Tuple(exprs)
            | Expression::Equals(exprs)
            | Expression::And(exprs)
            | Expression::Or(exprs)
            | Expression::FnCall(_, exprs)
            | Expression::List(exprs)
            | Expression::Set(exprs)
            | Expression::Xor(exprs) => {
                for expr in exprs {
                    expr.walk(f)
                }
            }

            Expression::Add(lhs, rhs)
            | Expression::Sub(lhs, rhs)
            | Expression::Mul(lhs, rhs)
            | Expression::Div(lhs, rhs) => {
                lhs.as_mut().walk(f);
                rhs.as_mut().walk(f)
            }

            _ => {
                panic!("Expression: not implemented: {self:#?}")
            }
        }
    }

    pub fn map<F>(&self, f: F) -> Expression
    where
        F: Fn(Expression) -> Expression,
    {
        self.borrow_map(&f)
    }

    pub fn borrow_map<F>(&self, f: &F) -> Expression
    where
        F: Fn(Expression) -> Expression,
    {
        f(match &self {
            Expression::Bot
            | Expression::EmptyTable(_)
            | Expression::None(_)
            | Expression::Sample(_)
            | Expression::StringLiteral(_)
            | Expression::IntegerLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::Identifier(_) => self.clone(),

            Expression::Not(expr) => Expression::Not(Box::new(expr.borrow_map(f))),
            Expression::Some(expr) => Expression::Some(Box::new(expr.borrow_map(f))),
            Expression::Unwrap(expr) => Expression::Unwrap(Box::new(expr.borrow_map(f))),
            Expression::TableAccess(id, expr) => {
                Expression::TableAccess(id.clone(), Box::new(expr.borrow_map(f)))
            }
            Expression::Tuple(exprs) => {
                Expression::Tuple(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            Expression::Equals(exprs) => {
                Expression::Equals(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            Expression::Xor(exprs) => {
                Expression::Xor(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            Expression::And(exprs) => {
                Expression::And(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            Expression::Or(exprs) => {
                Expression::Or(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            Expression::Add(lhs, rhs) => {
                Expression::Add(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            Expression::Sub(lhs, rhs) => {
                Expression::Sub(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            Expression::Mul(lhs, rhs) => {
                Expression::Mul(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            Expression::Div(lhs, rhs) => {
                Expression::Div(Box::new(lhs.borrow_map(f)), Box::new(rhs.borrow_map(f)))
            }
            Expression::FnCall(name, exprs) => Expression::FnCall(
                name.clone(),
                exprs.iter().map(|expr| expr.borrow_map(f)).collect(),
            ),
            Expression::List(exprs) => {
                Expression::List(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            Expression::Set(exprs) => {
                Expression::Set(exprs.iter().map(|expr| expr.borrow_map(f)).collect())
            }
            _ => {
                panic!("Expression: not implemented: {self:#?}")
            }
        })
    }

    pub fn mapfold<F, Ac>(&self, init: Ac, f: F) -> (Ac, Expression)
    where
        F: Fn(Ac, Expression) -> (Ac, Expression) + Copy,
        Ac: Clone,
    {
        let (ac, ex) = match &self {
            Expression::Bot
            | Expression::EmptyTable(_)
            | Expression::None(_)
            | Expression::Sample(_)
            | Expression::StringLiteral(_)
            | Expression::IntegerLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::Identifier(_) => (init, self.clone()),

            Expression::Not(expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, Expression::Not(Box::new(e)))
            }
            Expression::Some(expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, Expression::Some(Box::new(e)))
            }
            Expression::Unwrap(expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, Expression::Unwrap(Box::new(e)))
            }
            Expression::TableAccess(id, expr) => {
                let (ac, e) = expr.mapfold(init, f);
                (ac, Expression::TableAccess(id.clone(), Box::new(e)))
            }
            Expression::Tuple(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::Tuple(newexprs))
            }
            Expression::Xor(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::Xor(newexprs))
            }
            Expression::Equals(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::Equals(newexprs))
            }
            Expression::And(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::And(newexprs))
            }
            Expression::Or(exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::Or(newexprs))
            }
            Expression::Add(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, Expression::Add(Box::new(newlhs), Box::new(newrhs)))
            }
            Expression::Sub(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, Expression::Sub(Box::new(newlhs), Box::new(newrhs)))
            }
            Expression::Mul(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, Expression::Mul(Box::new(newlhs), Box::new(newrhs)))
            }
            Expression::Div(lhs, rhs) => {
                let ac = init;
                let (ac, newlhs) = lhs.mapfold(ac, f);
                let (ac, newrhs) = rhs.mapfold(ac, f);
                (ac, Expression::Div(Box::new(newlhs), Box::new(newrhs)))
            }
            Expression::FnCall(name, exprs) => {
                let mut ac = init;
                let newexprs = exprs
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();

                (ac, Expression::FnCall(name.clone(), newexprs))
            }
            Expression::List(inner) => {
                let mut ac = init;
                let newexprs = inner
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::List(newexprs))
            }
            Expression::Set(inner) => {
                let mut ac = init;
                let newexprs = inner
                    .iter()
                    .map(|expr| {
                        let (newac, e) = expr.mapfold(ac.clone(), f);
                        ac = newac;
                        e
                    })
                    .collect();
                (ac, Expression::Set(newexprs))
            }
            _ => {
                panic!("Expression: not implemented: {self:#?}")
            }
        };
        f(ac, ex)
    }

    pub fn new_equals(exprs: Vec<&Expression>) -> Expression {
        Expression::Equals(exprs.into_iter().cloned().collect())
    }

    pub fn into_identifier(self) -> Option<Identifier> {
        if let Self::Identifier(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_identifier_mut(&mut self) -> Option<&mut Identifier> {
        if let Self::Identifier(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_identifier(&self) -> Option<&Identifier> {
        if let Self::Identifier(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[macro_export]
macro_rules! tuple {
    ( $($e:expr),* ) => {
        {
            Expression::Tuple(vec![ $( $e.clone(), )* ])
        }
    };
}

#[macro_export]
macro_rules! list {
    ( $($e:expr),* ) => {
        {
            Expression::List(vec![ $( $e.clone(), )* ])
        }
    };
}

#[macro_export]
macro_rules! oracleinvoc {
    ( $name:expr, $($e:expr),* ) => {
        {
            Expression::OracleInvoc(
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
            Expression::FnCall(
                Identifier::Scalar($name.to_string()),
                vec![ $( $e.clone(), )* ],
            )
        }
    };
}
