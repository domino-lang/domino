// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::Display;

use sspverif_smtlib::syntax::s_expr::SExpr;

use crate::transforms::samplify::Position as SamplePosition;
use crate::types::Type;

use super::sorts::Sort;

#[derive(Debug, Clone, PartialOrd, Ord, Eq, PartialEq, Hash)]
pub enum SmtExpr {
    Comment(String),
    Atom(String),
    List(Vec<SmtExpr>),
}

impl From<SExpr> for SmtExpr {
    fn from(value: SExpr) -> Self {
        match value {
            SExpr::Const(con) => SmtExpr::Atom(con.to_string()),
            SExpr::Symbol(sym) => SmtExpr::Atom(sym.to_string()),
            SExpr::SExpr(exprs) => {
                SmtExpr::List(exprs.into_iter().map(|expr| expr.into()).collect())
            }
            SExpr::Reserved(res) => SmtExpr::Atom(res.to_string()),
            SExpr::HintComment(com) => SmtExpr::Comment(com),
        }
    }
}

impl From<Vec<SmtExpr>> for SmtExpr {
    fn from(lst: Vec<SmtExpr>) -> Self {
        SmtExpr::List(lst)
    }
}

impl From<String> for SmtExpr {
    fn from(atom: String) -> Self {
        SmtExpr::Atom(atom)
    }
}

impl From<&str> for SmtExpr {
    fn from(atom: &str) -> Self {
        SmtExpr::Atom(atom.to_string())
    }
}

impl From<&String> for SmtExpr {
    fn from(atom: &String) -> Self {
        SmtExpr::Atom(atom.to_string())
    }
}

impl From<i64> for SmtExpr {
    fn from(num: i64) -> Self {
        SmtExpr::Atom(format!("{num}"))
    }
}
impl From<i32> for SmtExpr {
    fn from(num: i32) -> Self {
        SmtExpr::Atom(format!("{num}"))
    }
}
impl From<usize> for SmtExpr {
    fn from(num: usize) -> Self {
        SmtExpr::Atom(format!("{num}"))
    }
}

impl From<bool> for SmtExpr {
    fn from(value: bool) -> Self {
        SmtExpr::Atom(format!("{value}"))
    }
}

impl From<&SamplePosition> for SmtExpr {
    fn from(position: &SamplePosition) -> Self {
        (
            "sample-id",
            format!("\"{}\"", position.inst_name),
            format!("\"{}\"", position.oracle_name),
            format!("\"{}\"", position.sample_name),
        )
            .into()
    }
}

impl<V: Into<SmtExpr>> From<SmtNot<V>> for SmtExpr {
    fn from(value: SmtNot<V>) -> Self {
        SmtExpr::List(vec!["not".into(), value.0.into()])
    }
}

impl From<SmtOr> for SmtExpr {
    fn from(terms: SmtOr) -> Self {
        let mut list: Vec<SmtExpr> = vec!["or".into()];
        list.extend(terms.0);
        SmtExpr::List(list)
    }
}

impl From<SmtAnd> for SmtExpr {
    fn from(terms: SmtAnd) -> Self {
        let mut list: Vec<SmtExpr> = vec!["and".into()];
        list.extend(terms.0);
        SmtExpr::List(list)
    }
}

impl<PRE: Into<SmtExpr>, POST: Into<SmtExpr>> From<SmtImplies<PRE, POST>> for SmtExpr {
    fn from(value: SmtImplies<PRE, POST>) -> Self {
        SmtExpr::List(vec!["=>".into(), value.0.into(), value.1.into()])
    }
}

impl<B: Into<SmtExpr>> From<SmtAssert<B>> for SmtExpr {
    fn from(asrt: SmtAssert<B>) -> Self {
        SmtExpr::List(vec!["assert".into(), asrt.0.into()])
    }
}

impl<V: Into<SmtExpr>> From<SmtWrap<V>> for SmtExpr {
    fn from(val: SmtWrap<V>) -> Self {
        SmtExpr::List(vec![val.0.into()])
    }
}

impl<T1: Into<SmtExpr>> From<(T1,)> for SmtExpr {
    fn from(lst: (T1,)) -> SmtExpr {
        let (v1,) = lst;
        SmtExpr::List(vec![v1.into()])
    }
}

impl<T1: Into<SmtExpr>, T2: Into<SmtExpr>> From<(T1, T2)> for SmtExpr {
    fn from(lst: (T1, T2)) -> SmtExpr {
        let (v1, v2) = lst;
        SmtExpr::List(vec![v1.into(), v2.into()])
    }
}

impl<T1: Into<SmtExpr>, T2: Into<SmtExpr>, T3: Into<SmtExpr>> From<(T1, T2, T3)> for SmtExpr {
    fn from(lst: (T1, T2, T3)) -> SmtExpr {
        let (v1, v2, v3) = lst;
        SmtExpr::List(vec![v1.into(), v2.into(), v3.into()])
    }
}

impl<T1: Into<SmtExpr>, T2: Into<SmtExpr>, T3: Into<SmtExpr>, T4: Into<SmtExpr>>
    From<(T1, T2, T3, T4)> for SmtExpr
{
    fn from(lst: (T1, T2, T3, T4)) -> SmtExpr {
        let (v1, v2, v3, v4) = lst;
        SmtExpr::List(vec![v1.into(), v2.into(), v3.into(), v4.into()])
    }
}

impl<
        T1: Into<SmtExpr>,
        T2: Into<SmtExpr>,
        T3: Into<SmtExpr>,
        T4: Into<SmtExpr>,
        T5: Into<SmtExpr>,
    > From<(T1, T2, T3, T4, T5)> for SmtExpr
{
    fn from(lst: (T1, T2, T3, T4, T5)) -> SmtExpr {
        let (v1, v2, v3, v4, v5) = lst;
        SmtExpr::List(vec![v1.into(), v2.into(), v3.into(), v4.into(), v5.into()])
    }
}

impl<
        T1: Into<SmtExpr>,
        T2: Into<SmtExpr>,
        T3: Into<SmtExpr>,
        T4: Into<SmtExpr>,
        T5: Into<SmtExpr>,
        T6: Into<SmtExpr>,
    > From<(T1, T2, T3, T4, T5, T6)> for SmtExpr
{
    fn from(lst: (T1, T2, T3, T4, T5, T6)) -> SmtExpr {
        let (v1, v2, v3, v4, v5, v6) = lst;
        SmtExpr::List(vec![
            v1.into(),
            v2.into(),
            v3.into(),
            v4.into(),
            v5.into(),
            v6.into(),
        ])
    }
}

impl<
        T1: Into<SmtExpr>,
        T2: Into<SmtExpr>,
        T3: Into<SmtExpr>,
        T4: Into<SmtExpr>,
        T5: Into<SmtExpr>,
        T6: Into<SmtExpr>,
        T7: Into<SmtExpr>,
    > From<(T1, T2, T3, T4, T5, T6, T7)> for SmtExpr
{
    fn from(lst: (T1, T2, T3, T4, T5, T6, T7)) -> SmtExpr {
        let (v1, v2, v3, v4, v5, v6, v7) = lst;
        SmtExpr::List(vec![
            v1.into(),
            v2.into(),
            v3.into(),
            v4.into(),
            v5.into(),
            v6.into(),
            v7.into(),
        ])
    }
}

impl Display for SmtExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtExpr::Comment(str) => write!(f, "; {str}"),
            SmtExpr::Atom(str) => write!(f, "{str}"),
            SmtExpr::List(lst) => {
                let mut peek = lst.iter().peekable();

                write!(f, "(")?;
                while let Some(elem) = peek.next() {
                    elem.fmt(f)?;

                    if peek.peek().is_some() {
                        write!(f, " ")?;
                    }
                }
                writeln!(f, ")")
            }
        }
    }
}

impl From<Type> for SmtExpr {
    fn from(t: Type) -> SmtExpr {
        match t {
            Type::Bits(length) => {
                let length = match &length {
                    crate::types::CountSpec::Identifier(identifier) => {
                        identifier.as_theorem_identifier().unwrap().ident()
                    }
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                };

                SmtExpr::Atom(format!("Bits_{length}"))
            }
            Type::Maybe(t) => SmtExpr::List(vec![SmtExpr::Atom("Maybe".into()), (*t).into()]),
            Type::Boolean => SmtExpr::Atom("Bool".to_string()),
            Type::Empty => SmtExpr::Atom("Empty".to_string()),
            Type::Integer => SmtExpr::Atom("Int".into()),
            Type::Table(t_idx, t_val) => SmtExpr::List(vec![
                SmtExpr::Atom("Array".into()),
                (*t_idx).into(),
                Type::Maybe(t_val).into(),
            ]),
            Type::Tuple(types) => SmtExpr::List({
                let mut els = vec![SmtExpr::Atom(format!("Tuple{}", types.len()))];
                for t in types {
                    els.push(t.into());
                }
                els
            }),
            _ => {
                panic!("not implemented: {t:?}")
            }
        }
    }
}

impl From<&Type> for SmtExpr {
    fn from(t: &Type) -> SmtExpr {
        match t {
            Type::Bits(length) => {
                let length = match length {
                    crate::types::CountSpec::Identifier(identifier) => {
                        identifier.as_theorem_identifier().unwrap().ident()
                    }
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                };

                SmtExpr::Atom(format!("Bits_{length}"))
            }
            Type::Maybe(t) => SmtExpr::List(vec![SmtExpr::Atom("Maybe".into()), (&**t).into()]),
            Type::Boolean => SmtExpr::Atom("Bool".to_string()),
            Type::Integer => SmtExpr::Atom("Int".into()),
            Type::Table(t_idx, t_val) => SmtExpr::List(vec![
                SmtExpr::Atom("Array".into()),
                (&**t_idx).into(),
                Type::Maybe(t_val.clone()).into(),
            ]),
            Type::Tuple(types) => SmtExpr::List({
                let mut els = vec![SmtExpr::Atom(format!("Tuple{}", types.len()))];
                for t in types {
                    els.push(t.into());
                }
                els
            }),
            Type::Empty => SmtExpr::Atom("Empty".to_string()),
            _ => {
                panic!("not implemented: {t:?}")
            }
        }
    }
}

impl<C, T, E> From<SmtIte<C, T, E>> for SmtExpr
where
    C: Into<SmtExpr>,
    T: Into<SmtExpr>,
    E: Into<SmtExpr>,
{
    fn from(ite: SmtIte<C, T, E>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::Atom("ite".into()),
            ite.cond.into(),
            ite.then.into(),
            ite.els.into(),
        ])
    }
}

impl<C, E> From<SmtIs<C, E>> for SmtExpr
where
    C: Into<String>,
    E: Into<SmtExpr>,
{
    fn from(is: SmtIs<C, E>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::List(vec![
                SmtExpr::Atom("_".into()),
                SmtExpr::Atom("is".into()),
                SmtExpr::Atom(is.con.into()),
            ]),
            is.expr.into(),
        ])
    }
}

impl<L, R> From<SmtEq2<L, R>> for SmtExpr
where
    L: Into<SmtExpr>,
    R: Into<SmtExpr>,
{
    fn from(eq: SmtEq2<L, R>) -> Self {
        SmtExpr::List(vec![
            SmtExpr::Atom("=".to_string()),
            eq.lhs.into(),
            eq.rhs.into(),
        ])
    }
}

impl<B> From<SmtLet<B>> for SmtExpr
where
    B: Into<SmtExpr>,
{
    fn from(l: SmtLet<B>) -> SmtExpr {
        if l.bindings.is_empty() {
            return l.body.into();
        }

        SmtExpr::List(vec![
            SmtExpr::Atom(String::from("let")),
            SmtExpr::List(
                l.bindings
                    .into_iter()
                    .map(|(id, expr)| SmtExpr::List(vec![SmtExpr::Atom(id), expr]))
                    .collect(),
            ),
            l.body.into(),
        ])
    }
}

impl<T: Into<SmtExpr>> From<SmtAs<T>> for SmtExpr {
    fn from(smtas: SmtAs<T>) -> Self {
        ("as", smtas.term, smtas.sort).into()
    }
}

#[derive(Debug)]
pub struct SmtLet<B>
where
    B: Into<SmtExpr>,
{
    pub(crate) bindings: Vec<(String, SmtExpr)>,
    pub(crate) body: B,
}

pub(crate) struct SmtEq2<L, R>
where
    L: Into<SmtExpr>,
    R: Into<SmtExpr>,
{
    pub(crate) lhs: L,
    pub(crate) rhs: R,
}

pub(crate) struct SmtAs<T: Into<SmtExpr>> {
    pub(crate) term: T,
    pub(crate) sort: Sort,
}

pub(crate) struct SmtIte<C, T, E>
where
    C: Into<SmtExpr>,
    T: Into<SmtExpr>,
    E: Into<SmtExpr>,
{
    pub(crate) cond: C,
    pub(crate) then: T,
    pub(crate) els: E,
}

pub(crate) struct SmtIs<C, E>
where
    C: Into<String>,
    E: Into<SmtExpr>,
{
    pub(crate) con: C,
    pub(crate) expr: E,
}

pub(crate) struct SmtAssert<B: Into<SmtExpr>>(pub B);

pub(crate) struct SmtNot<V: Into<SmtExpr>>(pub V);

pub(crate) struct SmtOr(pub Vec<SmtExpr>);
pub(crate) struct SmtAnd(pub Vec<SmtExpr>);

pub(crate) struct SmtWrap<V: Into<SmtExpr>>(pub V);

pub(crate) struct SmtImplies<PRE, POST>(pub PRE, pub POST)
where
    PRE: Into<SmtExpr>,
    POST: Into<SmtExpr>;

pub(crate) struct SmtForall<B: Into<SmtExpr>> {
    pub(crate) bindings: Vec<(String, SmtExpr)>,
    pub(crate) body: B,
}

impl<B: Into<SmtExpr>> From<SmtForall<B>> for SmtExpr {
    /*
     * SMT-LIB 2.6 manual p. 27:
     * <sorted_var> ::= ( symbol sort )
     * <term>       ::= ... | ( forall ( 〈sorted_var 〉+ ) 〈term〉 )
     *
     */
    fn from(val: SmtForall<B>) -> Self {
        (
            "forall",
            SmtExpr::List(
                val.bindings
                    .into_iter()
                    .map(|(name, sort)| (name, sort).into())
                    .collect(),
            ),
            val.body,
        )
            .into()
    }
}

pub(crate) struct SmtLt<L: Into<SmtExpr>, R: Into<SmtExpr>>(pub L, pub R);

impl<L: Into<SmtExpr>, R: Into<SmtExpr>> From<SmtLt<L, R>> for SmtExpr {
    fn from(val: SmtLt<L, R>) -> Self {
        ("<", val.0, val.1).into()
    }
}

pub(crate) struct SmtGt<L: Into<SmtExpr>, R: Into<SmtExpr>>(pub L, pub R);

impl<L: Into<SmtExpr>, R: Into<SmtExpr>> From<SmtGt<L, R>> for SmtExpr {
    fn from(val: SmtGt<L, R>) -> Self {
        (">", val.0, val.1).into()
    }
}

pub(crate) struct SmtLte<L: Into<SmtExpr>, R: Into<SmtExpr>>(pub L, pub R);

impl<L: Into<SmtExpr>, R: Into<SmtExpr>> From<SmtLte<L, R>> for SmtExpr {
    fn from(val: SmtLte<L, R>) -> Self {
        ("not", (">", val.0, val.1)).into()
    }
}

pub(crate) struct SmtGte<L: Into<SmtExpr>, R: Into<SmtExpr>>(pub L, pub R);

impl<L: Into<SmtExpr>, R: Into<SmtExpr>> From<SmtGte<L, R>> for SmtExpr {
    fn from(val: SmtGte<L, R>) -> Self {
        ("not", ("<", val.0, val.1)).into()
    }
}

#[derive(Debug, Clone)]
pub struct SmtMatch<E, B>
where
    E: Into<SmtExpr>,
    B: Into<SmtExpr>,
{
    pub expr: E,
    pub cases: Vec<SmtMatchCase<B>>,
}

impl<E, B> From<SmtMatch<E, B>> for SmtExpr
where
    E: Into<SmtExpr>,
    B: Into<SmtExpr>,
{
    fn from(value: SmtMatch<E, B>) -> SmtExpr {
        let cases = value
            .cases
            .into_iter()
            .map(|case| {
                let pattern = if case.args.is_empty() {
                    case.constructor.into()
                } else {
                    let mut pattern = vec![case.constructor.into()];
                    pattern.extend(case.args.into_iter().map(|s| s.into()));
                    SmtExpr::List(pattern)
                };

                SmtExpr::List(vec![pattern, case.body.into()])
            })
            .collect();

        ("match", value.expr, SmtExpr::List(cases)).into()
    }
}

#[derive(Debug, Clone)]
pub struct SmtMatchCase<B>
where
    B: Into<SmtExpr>,
{
    pub constructor: String,
    pub args: Vec<String>,
    pub body: B,
}
