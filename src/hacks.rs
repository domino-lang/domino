use std::fmt::{Display, Result};

use crate::writers::smt::exprs::SmtExpr;

pub struct ReturnValueDeclaration;

impl Into<SmtExpr> for ReturnValueDeclaration {
    fn into(self) -> SmtExpr {
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

pub struct MaybeDeclaration;

impl Display for MaybeDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        writeln!(
            f,
            "(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))"
        )
    }
}

impl Into<Vec<SmtExpr>> for MaybeDeclaration {
    fn into(self) -> Vec<SmtExpr> {
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
            .map(|i| format!("(el{i} T{i})"))
            .collect::<Vec<_>>()
            .join(" ");

        writeln!(
            f,
            "(declare-datatypes ((Tuple{n} {n})) ((par ({types}) ((mk-tuple{n} {ds})))))"
        )
    }
}

impl Into<Vec<SmtExpr>> for TupleDeclaration {
    fn into(self) -> Vec<SmtExpr> {
        let TupleDeclaration(n) = self;

        if n == 0 {
            return vec![(
                "declare-datatypes",
                ((format!("Tuple0"), n),),
                ((("mk-typle0",),)),
            )
                .into()];
        }

        let types: Vec<SmtExpr> = (1..n + 1)
            .map(|i| format!("T{i}").into())
            .collect::<Vec<_>>();

        let ds: Vec<SmtExpr> = (1..n + 1)
            .map(|i| (format!("el{i}"), format!("T{i}")).into())
            .collect::<Vec<_>>();

        let mut fns = vec![format!("mk-tuple{n}").into()];
        fns.extend(ds.into_iter());

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
        let iter = range.clone().map(|i| TupleDeclaration(i));
        for decl in iter {
            write!(f, "{decl}")?;
        }

        Ok(())
    }
}

impl Into<Vec<SmtExpr>> for TuplesDeclaration {
    fn into(self) -> Vec<SmtExpr> {
        self.0
            .map(|i| <TupleDeclaration as Into<Vec<SmtExpr>>>::into(TupleDeclaration(i)))
            .flatten()
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

impl Into<Vec<SmtExpr>> for BitsDeclaration {
    fn into(self) -> Vec<SmtExpr> {
        let BitsDeclaration(id) = self;

        vec![("declare-sort", format!("Bits_{id}"), 0).into()]
    }
}

pub struct EmptyDeclaration;

impl Display for EmptyDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result {
        writeln!(f, "(declare-datatype Empty ((mk-empty)) )")
    }
}

impl Into<Vec<SmtExpr>> for EmptyDeclaration {
    fn into(self) -> Vec<SmtExpr> {
        vec![("declare-datatype", "Empty", (("mk-empty",),)).into()]
    }
}

macro_rules! impl_IntoIterator {
    ($tipe:ident) => {
        impl IntoIterator for $tipe {
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
