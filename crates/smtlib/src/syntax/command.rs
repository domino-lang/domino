// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    s_expr::SExpr,
    sort::Sort,
    term::{SortedVar, Term},
    tokens::{Numeral, ReservedWord, StringLiteral, Symbol},
};

#[derive(Debug, Clone)]
pub enum CommandName {
    Not,
    Assert,
    CheckSat,
    CheckSatAssuming,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DeclareSort,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineSort,
    Echo,
    GetModel,
    Push,
    Pop,
    SetLogic,
}

impl From<CommandName> for Symbol {
    fn from(value: CommandName) -> Self {
        let name = match value {
            CommandName::Not => "not",
            CommandName::Assert => "assert",
            CommandName::CheckSat => "check-sat",
            CommandName::CheckSatAssuming => "check-sat-assuming",
            CommandName::DeclareConst => "declare-const",
            CommandName::DeclareDatatype => "declare-datatype",
            CommandName::DeclareDatatypes => "declare-datatypes",
            CommandName::DeclareFun => "declare-fun",
            CommandName::DeclareSort => "declare-sort",
            CommandName::DefineFun => "define-fun",
            CommandName::DefineFunRec => "define-fun-rec",
            CommandName::DefineFunsRec => "define-funs-rec",
            CommandName::DefineSort => "define-sort",
            CommandName::Echo => "echo",
            CommandName::GetModel => "get-model",
            CommandName::Push => "push",
            CommandName::Pop => "pop",
            CommandName::SetLogic => "set-logic",
        };

        Symbol::parse(name).unwrap()
    }
}

impl From<CommandName> for SExpr {
    fn from(value: CommandName) -> Self {
        Symbol::from(value).into()
    }
}

#[derive(Debug, Clone)]
pub struct SortDec(Symbol, Numeral);

impl From<SortDec> for SExpr {
    fn from(value: SortDec) -> Self {
        SExpr::SExpr(vec![value.0.into(), value.1.into()])
    }
}

#[derive(Debug, Clone)]
pub struct SelectorDec(Symbol, Sort);

impl SelectorDec {
    pub fn new(sym: Symbol, sort: Sort) -> Self {
        Self(sym, sort)
    }
}

impl From<SelectorDec> for SExpr {
    fn from(value: SelectorDec) -> Self {
        SExpr::SExpr(vec![value.0.into(), value.1.into()])
    }
}

#[derive(Debug, Clone)]
pub struct ConstructorDec(Symbol, Vec<SelectorDec>);

impl ConstructorDec {
    pub fn new(sym: Symbol, selectors: impl IntoIterator<Item = SelectorDec>) -> Self {
        Self(sym, selectors.into_iter().collect())
    }
}

impl From<ConstructorDec> for SExpr {
    fn from(value: ConstructorDec) -> Self {
        let name_sexpr: SExpr = value.0.into();
        SExpr::from_iter(
            Some(name_sexpr)
                .into_iter()
                .chain(value.1.into_iter().map(|sel| sel.into())),
        )
    }
}

#[derive(Debug, Clone)]
pub struct DatatypeDec(Vec<Symbol>, Vec<ConstructorDec>);

impl DatatypeDec {
    pub fn new(par_syms: Vec<Symbol>, cons: impl IntoIterator<Item = ConstructorDec>) -> Self {
        Self(par_syms, cons.into_iter().collect())
    }
}

impl From<DatatypeDec> for SExpr {
    fn from(value: DatatypeDec) -> Self {
        if value.0.is_empty() {
            SExpr::from_iter(value.1)
        } else {
            SExpr::SExpr(vec![
                ReservedWord::Par.into(),
                SExpr::from_iter(value.0),
                SExpr::from_iter(value.1),
            ])
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDec(Symbol, Vec<SortedVar>, Sort);

impl From<FunctionDec> for SExpr {
    fn from(value: FunctionDec) -> Self {
        SExpr::SExpr(vec![
            value.0.into(),
            SExpr::from_iter(value.1),
            value.2.into(),
        ])
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDef(Symbol, Vec<SortedVar>, Sort, Term);

#[derive(Debug, Clone)]
pub enum PropLiteral {
    Basic(Symbol),
    Not(Symbol),
}

impl From<PropLiteral> for SExpr {
    fn from(value: PropLiteral) -> Self {
        match value {
            PropLiteral::Basic(sym) => sym.into(),
            PropLiteral::Not(sym) => SExpr::SExpr(vec![
                SExpr::Symbol(Symbol::parse("not").unwrap()),
                sym.into(),
            ]),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Command {
    Assert(Term),
    CheckSat,
    CheckSatAssuming(Vec<PropLiteral>),
    DeclareConst(Symbol, Sort),
    DeclareDatatype(Symbol, DatatypeDec),
    DeclareDatatypes(Vec<(SortDec, DatatypeDec)>),
    DeclareFun(Symbol, Vec<Sort>, Sort),
    DefineFun(FunctionDef),
    DefineFunRec(FunctionDef),
    DefineFunsRec(Vec<(FunctionDec, Term)>),
    DefineSort(Symbol, Vec<Symbol>, Sort),
    Echo(StringLiteral),
    GetModel,
    Push(Numeral),
    Pop(Numeral),
    SetLogic(Symbol),
}

impl From<Command> for SExpr {
    fn from(cmd: Command) -> Self {
        match cmd {
            Command::Assert(term) => SExpr::SExpr(vec![CommandName::Assert.into(), term.into()]),
            Command::CheckSat => CommandName::CheckSat.into(),
            Command::CheckSatAssuming(_) => todo!(),
            Command::DeclareConst(sym, sort) => SExpr::SExpr(vec![
                CommandName::DeclareConst.into(),
                sym.into(),
                sort.into(),
            ]),
            Command::DeclareDatatype(sym, dec) => SExpr::SExpr(vec![
                CommandName::DeclareDatatype.into(),
                sym.into(),
                dec.into(),
            ]),
            Command::DeclareDatatypes(spec) => {
                let (sorts, decs): (Vec<_>, Vec<_>) = spec.into_iter().unzip();
                SExpr::SExpr(vec![
                    CommandName::DeclareDatatypes.into(),
                    SExpr::from_iter(sorts),
                    SExpr::from_iter(decs),
                ])
            }
            Command::DeclareFun(sym, arg_sorts, sort) => SExpr::SExpr(vec![
                CommandName::DeclareFun.into(),
                sym.into(),
                SExpr::from_iter(arg_sorts),
                sort.into(),
            ]),
            Command::DefineFun(fundef) => SExpr::SExpr(vec![
                CommandName::DefineFun.into(),
                fundef.0.into(),
                SExpr::from_iter(fundef.1),
                fundef.2.into(),
                fundef.3.into(),
            ]),
            Command::DefineFunRec(fundef) => SExpr::SExpr(vec![
                CommandName::DefineFunRec.into(),
                fundef.0.into(),
                SExpr::from_iter(fundef.1),
                fundef.2.into(),
                fundef.3.into(),
            ]),
            Command::DefineFunsRec(spec) => {
                let (decs, bodies): (Vec<_>, Vec<_>) = spec.into_iter().unzip();

                SExpr::SExpr(vec![
                    CommandName::DefineFunsRec.into(),
                    SExpr::from_iter(decs),
                    SExpr::from_iter(bodies),
                ])
            }
            Command::DefineSort(sym, args, sort) => SExpr::SExpr(vec![
                CommandName::DefineSort.into(),
                sym.into(),
                SExpr::from_iter(args),
                sort.into(),
            ]),
            Command::Echo(text) => SExpr::SExpr(vec![CommandName::Echo.into(), text.into()]),
            Command::GetModel => CommandName::GetModel.into(),
            Command::Push(count) => SExpr::SExpr(vec![CommandName::Push.into(), count.into()]),
            Command::Pop(count) => SExpr::SExpr(vec![CommandName::Pop.into(), count.into()]),
            Command::SetLogic(sym) => SExpr::SExpr(vec![CommandName::SetLogic.into(), sym.into()]),
        }
    }
}
