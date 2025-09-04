use thiserror::Error;

use crate::identifier::Identifier;
use crate::package::OracleSig;
use miette::Diagnostic;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum OracleContext {
    Package {
        pkg_name: String,
    },

    PackageInstance {
        pkg_name: String,
        pkg_inst_name: String,
        game_name: String,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Declaration {
    Identifier(Identifier),
    Oracle(OracleContext, OracleSig),
}

impl Declaration {
    pub fn into_identifier(self) -> Result<Identifier, Self> {
        match self {
            Declaration::Identifier(ident) => Ok(ident),
            Declaration::Oracle(_, _) => Err(self),
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum Error {
    #[error("identifier `{0}` already declared with {1:?}")]
    AlreadyDefined(String, Declaration),
}

#[derive(Debug, Clone)]
pub struct Scope {
    entries: Vec<HashMap<String, Declaration>>,
    types: HashSet<Declaration>,
}

impl Default for Scope {
    fn default() -> Self {
        Self::new()
    }
}

impl Scope {
    pub fn new() -> Scope {
        Scope {
            entries: vec![],
            types: HashSet::new(),
        }
    }

    pub fn enter(&mut self) {
        self.entries.push(HashMap::new())
    }

    pub fn leave(&mut self) {
        if !self.entries.is_empty() {
            self.entries.pop();
        } else {
            panic!("scope leave: scope stack is empty");
        }
    }

    pub fn known_types(&self) -> HashSet<Declaration> {
        self.types.clone()
    }

    /* Error conditions:
     *  - No scope at all
     *  - Identifier exists somewhere in the scope tower already
     */
    pub fn declare(&mut self, id: &str, scope_type: Declaration) -> Result<(), Error> {
        self.types.insert(scope_type.clone());
        if self.lookup(id).is_none() {
            if let Some(last) = self.entries.last_mut() {
                last.insert(id.to_string(), scope_type.clone());
                Ok(())
            } else {
                panic!("scope declare: scope stack is empty");
            }
        } else {
            Err(Error::AlreadyDefined(
                id.to_string(),
                self.lookup(id).unwrap(),
            )) // already defined
        }
    }

    pub fn lookup(&self, id: &str) -> Option<Declaration> {
        /* Only needed for debug printing
        match &id {
            Identifier::Local(name)
            | Identifier::Scalar(name)
            | Identifier::State { name, .. }
            | Identifier::Params {
                name_in_pkg: name, ..
            } => {
                let print_names: Vec<&str> = vec![];
                let do_print = print_names.iter().any(|print_name| name == print_name);

                if do_print {
                    eprintln!("DEBUG Scope lookup {id:?}");
                }
            }
        }
        */

        for table in self.entries.clone().into_iter().rev() {
            if let Some(t) = table.get(id) {
                return Some(t.clone());
            }
        }

        None
    }

    pub fn lookup_identifier(&self, id: &str) -> Option<Identifier> {
        self.lookup(id).and_then(|decl| match decl {
            Declaration::Identifier(identifier) => Some(identifier),
            Declaration::Oracle(_, _) => None,
        })
    }
}

#[cfg(test)]
mod test {
    use super::Declaration;
    use crate::{expressions::Expression, types};

    use super::Scope;

    /* Properties:
    - (enter then) only lookup -> fails trivially (not tested)
    - (enter then) declare then lookup -> success
    - access variable that was declared inside a block after leaving -> fails
    - access varable that was declared, then enter and leave -> success
    */

    #[test]
    fn declare_then_lookup_succeeds() {
        let id = "test_id";
        let t = types::Type::Integer;

        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(
                id,
                Declaration::Identifier(crate::identifier::Identifier::PackageIdentifier(
                    crate::identifier::pkg_ident::PackageIdentifier::Const(
                        crate::identifier::pkg_ident::PackageConstIdentifier {
                            pkg_name: "SomePkg".to_string(),
                            name: id.to_string(),
                            ty: t.clone(),
                            game_assignment: None,
                            pkg_inst_name: None,
                            game_name: None,
                            game_inst_name: None,
                            theorem_name: None,
                        },
                    ),
                )),
            )
            .expect("declare failed");

        let decl = scope.lookup(id).expect("lookup failed");

        // TODO: use this instead, once it doesn't require nightly:
        //assert_matches!(t_, Type::Type(t_), "t_ should be a real type, found {t_:?}");

        if let Declaration::Identifier(ident) = decl {
            let t_ = Expression::Identifier(ident).get_type();
            assert_eq!(t, t_, "lookup returned wrong type");
        } else {
            panic!("t_ should be a real type, found {decl:?}");
        }
    }

    #[test]
    fn gone_after_leave() {
        let id = "test_id";
        let t = types::Type::Integer;

        let mut scope = Scope::new();
        scope.enter();
        scope.enter();
        scope
            .declare(
                id,
                Declaration::Identifier(crate::identifier::Identifier::PackageIdentifier(
                    crate::identifier::pkg_ident::PackageIdentifier::Const(
                        crate::identifier::pkg_ident::PackageConstIdentifier {
                            pkg_name: "SomePkg".to_string(),
                            name: id.to_string(),
                            ty: t.clone(),
                            game_assignment: None,
                            pkg_inst_name: None,
                            game_name: None,
                            game_inst_name: None,
                            theorem_name: None,
                        },
                    ),
                )),
            )
            .expect("declare failed");
        scope.leave();

        assert_eq!(None, scope.lookup(id));
    }

    #[test]
    fn still_there_after_enter_and_leave() {
        let id = "test_id";
        let id2 = "test_id2";
        let t = types::Type::Integer;
        let t2 = types::Type::String;

        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(
                id,
                Declaration::Identifier(crate::identifier::Identifier::PackageIdentifier(
                    crate::identifier::pkg_ident::PackageIdentifier::Const(
                        crate::identifier::pkg_ident::PackageConstIdentifier {
                            pkg_name: "SomePkg".to_string(),
                            name: id.to_string(),
                            ty: t.clone(),
                            game_assignment: None,
                            pkg_inst_name: None,
                            game_name: None,
                            game_inst_name: None,
                            theorem_name: None,
                        },
                    ),
                )),
            )
            .expect("declare id failed");

        scope.enter();
        scope
            .declare(
                id2,
                Declaration::Identifier(crate::identifier::Identifier::PackageIdentifier(
                    crate::identifier::pkg_ident::PackageIdentifier::Const(
                        crate::identifier::pkg_ident::PackageConstIdentifier {
                            pkg_name: "SomePkg".to_string(),
                            name: id2.to_string(),
                            ty: t2.clone(),
                            game_assignment: None,
                            pkg_inst_name: None,
                            game_name: None,
                            game_inst_name: None,
                            theorem_name: None,
                        },
                    ),
                )),
            )
            .expect("declare id2 failed");
        scope.leave();

        let decl = scope.lookup(id).expect("lookup failed");

        // TODO: use this instead, once it doesn't require nightly:
        //assert_matches!(t_, Type::Type(t_), "t_ should be a real type, found {t_:?}");

        if let Declaration::Identifier(ident) = decl {
            let t_ = Expression::Identifier(ident).get_type();
            assert_eq!(t, t_, "lookup returned wrong type");
        } else {
            panic!("t_ should be a real type, found {decl:?}");
        }
    }
}
