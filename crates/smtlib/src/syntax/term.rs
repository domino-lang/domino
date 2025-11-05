// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    identifier::Identifier,
    s_expr::{SExpr, SpecConstant},
    sort::Sort,
    tokens::{ReservedWord, Symbol},
};

#[derive(Debug, Clone)]
pub struct QualifiedIdentifier(pub Identifier, pub Option<Sort>);

impl From<QualifiedIdentifier> for SExpr {
    fn from(value: QualifiedIdentifier) -> Self {
        let QualifiedIdentifier(ident, sort) = value;
        if let Some(sort) = sort {
            let as_sexpr: SExpr = ReservedWord::As.into();
            SExpr::from_iter(vec![as_sexpr, ident.into(), sort.into()])
        } else {
            ident.into()
        }
    }
}

impl<T: Into<Symbol>> From<T> for QualifiedIdentifier {
    fn from(value: T) -> Self {
        QualifiedIdentifier(Identifier(value.into(), vec![]), None)
    }
}

#[derive(Debug, Clone)]
pub struct VarBinding(pub Symbol, pub Term);

impl From<VarBinding> for SExpr {
    fn from(value: VarBinding) -> Self {
        SExpr::SExpr(vec![value.0.into(), value.1.into()])
    }
}

#[derive(Debug, Clone)]
pub struct SortedVar(pub Symbol, pub Sort);

impl From<SortedVar> for SExpr {
    fn from(value: SortedVar) -> Self {
        SExpr::SExpr(vec![value.0.into(), value.1.into()])
    }
}

#[derive(Debug, Clone)]
pub struct Pattern(pub Symbol, pub Vec<Symbol>);

#[derive(Debug, Clone)]
pub struct MatchCase(pub Pattern, pub Term);

#[derive(Debug, Clone)]
pub enum Term {
    Const(SpecConstant),
    Base(QualifiedIdentifier, Vec<Term>),
    Let(Vec<VarBinding>, Box<Term>),
    ForAll(Vec<SortedVar>, Box<Term>),
    Exists(Vec<SortedVar>, Box<Term>),
    //Annotation(Box<Term>, Vec<Attribute>),
}

impl From<SpecConstant> for Term {
    fn from(value: SpecConstant) -> Self {
        Self::Const(value)
    }
}

impl<T: Into<QualifiedIdentifier>> From<T> for Term {
    fn from(value: T) -> Self {
        Self::Base(value.into(), vec![])
    }
}

impl From<Term> for SExpr {
    fn from(term: Term) -> Self {
        match term {
            Term::Const(con) => con.into(),
            Term::Base(qid, terms) => {
                if terms.is_empty() {
                    qid.into()
                } else {
                    let qid_sexpr: SExpr = qid.into();

                    SExpr::from_iter(Some(qid_sexpr).into_iter().chain(
                        terms.into_iter().map(|term| term.into()),
                        //.flat_map(|term| vec![term.into(), SExpr::HintNewline]),
                    ))
                }
            }
            Term::Let(bindings, term) => SExpr::SExpr(vec![
                ReservedWord::Let.into(),
                SExpr::from_iter(bindings),
                (*term).into(),
            ]),
            Term::ForAll(vars, term) => SExpr::SExpr(vec![
                ReservedWord::Forall.into(),
                SExpr::from_iter(vars),
                (*term).into(),
            ]),
            Term::Exists(vars, term) => SExpr::SExpr(vec![
                ReservedWord::Exists.into(),
                SExpr::from_iter(vars),
                (*term).into(),
            ]),
            // Term::Annotation(term, attrs) => SExpr::from_iter(vec![
            //     ReservedWord::Bang.into(),
            //     (*term).into(),
            // ]).chain(attrs.into_iter()),
        }
    }
}
