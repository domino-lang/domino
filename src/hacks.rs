// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::{Display, Result};

use crate::writers::smt::exprs::SmtExpr;

pub struct ReturnValueDeclaration;

impl From<ReturnValueDeclaration> for SmtExpr {
    fn from(_: ReturnValueDeclaration) -> Self {
        (
            "declare-datatypes",
            (("ReturnValue", 1),),
            ((
                "par",
                ("T",),
                (("mk-return-value", ("return-value", "T")), ("mk-abort",)),
            ),),
        )
            .into()
    }
}

pub struct SampleIdDeclaration;

impl From<SampleIdDeclaration> for SmtExpr {
    fn from(_: SampleIdDeclaration) -> Self {
        (
            "declare-datatype",
            "SampleId",
            ((
                "sample-id",
                ("sample-pkg-name", "String"),
                ("sample-oracle-name", "String"),
                ("sample-name", "String"),
            ),),
        )
            .into()
    }
}

pub struct MaybeDeclaration;

impl Display for MaybeDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        writeln!(
            f,
            "(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))"
        )
    }
}

impl From<MaybeDeclaration> for Vec<SmtExpr> {
    fn from(_val: MaybeDeclaration) -> Self {
        vec![(
            "declare-datatypes",
            (("Maybe", 1),),
            ((
                "par",
                ("T",),
                (("mk-some", ("maybe-get", "T")), ("mk-none",)),
            ),),
        )
            .into()]
    }
}

/*
impl IntoIterator for MaybeDeclaration {
    type Item = SmtExpr;

    type IntoIter = <Vec<SmtExpr> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        let tmp: Vec<SmtExpr> = self.into();
        tmp.into_iter()
    }
}
 */
pub struct TupleDeclaration(pub usize);

impl Display for TupleDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        let TupleDeclaration(n) = self;
        let n = *n;

        if n == 0 {
            return writeln!(f, "(declare-datatypes ((Tuple0 0)) ((mk-tuple0))))");
        }

        let types: String = (1..n + 1)
            .map(|i| format!("T{i}"))
            .collect::<Vec<_>>()
            .join(" ");

        let ds: String = (1..n + 1)
            .map(|i| format!("(el{n}-{i} T{i})"))
            .collect::<Vec<_>>()
            .join(" ");

        writeln!(
            f,
            "(declare-datatypes ((Tuple{n} {n})) ((par ({types}) ((mk-tuple{n} {ds})))))"
        )
    }
}

impl From<TupleDeclaration> for Vec<SmtExpr> {
    fn from(val: TupleDeclaration) -> Self {
        let TupleDeclaration(n) = val;

        if n == 0 {
            return vec![("declare-datatypes", (("Tuple0", n),), (("mk-typle0",),)).into()];
        }

        let types: Vec<SmtExpr> = (1..n + 1)
            .map(|i| format!("T{i}").into())
            .collect::<Vec<_>>();

        let ds: Vec<SmtExpr> = (1..n + 1)
            .map(|i| (format!("el{n}-{i}"), format!("T{i}")).into())
            .collect::<Vec<_>>();

        let mut fns = vec![format!("mk-tuple{n}").into()];
        fns.extend(ds);

        vec![(
            "declare-datatypes",
            ((format!("Tuple{n}"), n),),
            (("par", SmtExpr::List(types), (SmtExpr::List(fns),)),),
        )
            .into()]
    }
}

pub struct TuplesDeclaration(pub std::ops::Range<usize>);

impl Display for TuplesDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        let TuplesDeclaration(range) = self;
        let iter = range.clone().map(TupleDeclaration);
        for decl in iter {
            write!(f, "{decl}")?;
        }

        Ok(())
    }
}

impl From<TuplesDeclaration> for Vec<SmtExpr> {
    fn from(val: TuplesDeclaration) -> Self {
        val.0
            .flat_map(|i| <TupleDeclaration as Into<Vec<SmtExpr>>>::into(TupleDeclaration(i)))
            .collect()
    }
}

pub struct BitsDeclaration(pub String);

impl Display for BitsDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        let BitsDeclaration(id) = self;
        writeln!(f, "(declare-sort Bits_{id} 0)")
    }
}

impl From<BitsDeclaration> for Vec<SmtExpr> {
    fn from(val: BitsDeclaration) -> Self {
        let BitsDeclaration(id) = val;

        vec![("declare-sort", format!("Bits_{id}"), 0).into()]
    }
}

pub struct EmptyDeclaration;

impl Display for EmptyDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        writeln!(f, "(declare-datatype Empty ((mk-empty)) )")
    }
}

impl From<EmptyDeclaration> for Vec<SmtExpr> {
    fn from(_val: EmptyDeclaration) -> Self {
        vec![("declare-datatype", "Empty", (("mk-empty",),)).into()]
    }
}

macro_rules! impl_IntoIterator {
    ($ty:ident) => {
        impl IntoIterator for $ty {
            type Item = SmtExpr;
            type IntoIter = <Vec<SmtExpr> as IntoIterator>::IntoIter;

            fn into_iter(self) -> Self::IntoIter {
                let tmp: Vec<SmtExpr> = self.into();
                tmp.into_iter()
            }
        }
    };
}

impl_IntoIterator!(MaybeDeclaration);
impl_IntoIterator!(TupleDeclaration);
impl_IntoIterator!(TuplesDeclaration);
impl_IntoIterator!(EmptyDeclaration);
impl_IntoIterator!(BitsDeclaration);
