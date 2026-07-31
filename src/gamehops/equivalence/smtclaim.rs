use miette::Diagnostic;
use thiserror::Error;

use crate::writers::smt::exprs::SmtExpr;

#[derive(Error, Diagnostic, Debug)]
#[error("custom smt in invariant file:\n{smt}")]
#[diagnostic(code(domino::theorem::custom_smt), severity(Warning))]
pub struct CustomSmtWarning {
    pub smt: SmtExpr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClaimType {
    RawSmt,
    Function,
    Lemma,
    Relation,
    Invariant,
    LeftPackageInvariant,
    RightPackageInvariant,
    LeftGameInvariant,
    RightGameInvariant,
}

impl ClaimType {
    pub fn guess_from_smt(smt: &SmtExpr) -> (ClaimType, String) {
        if let SmtExpr::List(list) = smt {
            if list[0] == "define-fun".into() {
                let SmtExpr::Atom(funname) = &list[1] else {
                    unreachable!()
                };
                if funname == "invariant" {
                    return (ClaimType::Invariant, "invariant".to_string());
                } else if let SmtExpr::List(args) = &list[2] {
                    if args.len() == 2 {
                        return (ClaimType::Relation, funname.to_string());
                    } else if args.len() >= 4 {
                        let indices: Vec<_> = funname.match_indices("-").collect();
                        if indices.len() >= 4 {
                            let funname =
                                &funname[(indices[0].0 + 1)..(indices[indices.len() - 3].0)];

                            return (ClaimType::Lemma, funname.to_string());
                        }
                    }
                }
                // some define-fun but not some useable claim type
                return (ClaimType::Function, funname.to_string());
            }
        }
        // not a define-fun, big warning!
        eprintln!(
            "{:?}",
            miette::Report::new(CustomSmtWarning { smt: smt.clone() })
        );
        (ClaimType::RawSmt, String::default())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SmtClaim {
    ty: ClaimType,
    smt: SmtExpr,
    name: String,
}

impl SmtClaim {
    pub fn new(ty: ClaimType, smt: SmtExpr, name: String) -> Self {
        Self { ty, smt, name }
    }

    pub fn new_package_invariant(
        ty: ClaimType,
        smt: SmtExpr,
        game_name: &str,
        pkg_name: &str,
    ) -> Self {
        Self {
            ty,
            smt,
            name: format!("package-invariant!{game_name}-{pkg_name}!"),
        }
    }

    pub fn new_game_invariant(ty: ClaimType, smt: SmtExpr, game_name: &str) -> Self {
        Self {
            ty,
            smt,
            name: format!("game-invariant!{game_name}!"),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn smt(&self) -> &SmtExpr {
        &self.smt
    }

    pub fn ty(&self) -> &ClaimType {
        &self.ty
    }
}
