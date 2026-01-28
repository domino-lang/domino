// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::identifier::{pkg_ident::PackageIdentifier, Identifier};

#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Type {
    kind: TypeKind,
}

impl Type {
    pub fn from_kind(kind: TypeKind) -> Self {
        Self { kind }
    }

    pub(crate) fn empty() -> Type {
        Self {
            kind: TypeKind::Empty,
        }
    }

    pub(crate) fn boolean() -> Type {
        Self {
            kind: TypeKind::Boolean,
        }
    }

    pub(crate) fn integer() -> Type {
        Self {
            kind: TypeKind::Integer,
        }
    }

    pub(crate) fn string() -> Type {
        Self {
            kind: TypeKind::String,
        }
    }

    pub(crate) fn unknown() -> Self {
        Self {
            kind: TypeKind::Unknown,
        }
    }

    pub(crate) fn maybe(ty: Type) -> Self {
        Self {
            kind: TypeKind::Maybe(Box::new(ty)),
        }
    }

    pub(crate) fn tuple(tys: Vec<Type>) -> Self {
        Self {
            kind: TypeKind::Tuple(tys),
        }
    }

    pub(crate) fn list(ty: Type) -> Self {
        Self {
            kind: TypeKind::List(Box::new(ty)),
        }
    }

    pub(crate) fn set(ty: Type) -> Self {
        Self {
            kind: TypeKind::Set(Box::new(ty)),
        }
    }

    pub(crate) fn table(key: Type, value: Type) -> Self {
        Self {
            kind: TypeKind::Table(Box::new(key), Box::new(value)),
        }
    }

    pub(crate) fn fun(args: Vec<Type>, ret: Type) -> Self {
        Self {
            kind: TypeKind::Fn(args, Box::new(ret)),
        }
    }

    pub(crate) fn bits(countspec: CountSpec) -> Self {
        Self {
            kind: TypeKind::Bits(countspec),
        }
    }

    pub(crate) fn user_defined(name: String) -> Self {
        Self {
            kind: TypeKind::UserDefined(name),
        }
    }

    pub fn into_kind(self) -> TypeKind {
        self.kind
    }

    pub fn kind<'a>(&'a self) -> &'a TypeKind {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut TypeKind {
        &mut self.kind
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum TypeKind {
    Unknown,
    Empty,
    Integer,
    String,
    Boolean,
    Bits(CountSpec),     // Bits strings of length ...
    AddiGroupEl(String), // name of the group
    MultGroupEl(String), // name of the group
    List(Box<Type>),
    Set(Box<Type>),
    Tuple(Vec<Type>),
    Table(Box<Type>, Box<Type>),
    Maybe(Box<Type>),
    Fn(Vec<Type>, Box<Type>), // arg types, return type
    UserDefined(String),
}

impl TypeKind {
    /// Returns `true` if the type kind is [`Integer`].
    ///
    /// [`Integer`]: TypeKind::Integer
    #[must_use]
    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Integer)
    }

    /// Returns `true` if the type kind is [`Unknown`].
    ///
    /// [`Unknown`]: TypeKind::Unknown
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl Type {
    pub(crate) fn rewrite_type(&self, rules: &[(Type, Type)]) -> Self {
        if let Some((_, replace)) = rules.iter().find(|(search, _)| self == search) {
            replace.clone()
        } else {
            match self.kind() {
                TypeKind::Bits(CountSpec::Identifier(id)) if matches!(id.as_ref(), Identifier::PackageIdentifier(PackageIdentifier::Const(pkg_const_ident )) if &pkg_const_ident.name == "n" && pkg_const_ident.ty.kind().is_integer() ) => {
                    assert!(!rules.is_empty(), "no type rewrite rules found despite identifier in CountSpec: {id:?}");
                    self.clone()
                }

                TypeKind::Empty
                | TypeKind::Integer
                | TypeKind::String
                | TypeKind::Boolean
                | TypeKind::Bits(_) // NB: This is a fallthrough, the Identifier case is handled above
                | TypeKind::AddiGroupEl(_)
                | TypeKind::MultGroupEl(_) => self.clone(),

                TypeKind::List(t) => Type::from_kind(TypeKind::List(Box::new(t.rewrite_type(rules)))),
                TypeKind::Maybe(t) => Type::from_kind(TypeKind::Maybe(Box::new(t.rewrite_type(rules)))),
                TypeKind::Set(t) => Type::from_kind(TypeKind::Set(Box::new(t.rewrite_type(rules)))),

                TypeKind::Tuple(ts) => Type::from_kind(TypeKind::Tuple(ts.iter().map(|t| t.rewrite_type(rules)).collect())),
                TypeKind::Table(t1, t2) => Type::from_kind(TypeKind::Table(
                    Box::new(t1.rewrite_type(rules)),
                    Box::new(t2.rewrite_type(rules)),
                )),
                TypeKind::Fn(ts, t) => Type::from_kind(TypeKind::Fn(
                    ts.iter().map(|t| t.rewrite_type(rules)).collect(),
                    Box::new(t.rewrite_type(rules)),
                )),
                TypeKind::Unknown => unreachable!(),
                TypeKind::UserDefined(_) => unreachable!(),
            }
        }
    }

    pub(crate) fn types_match(&self, other: &Self) -> bool {
        match (self.kind(), other.kind()) {
            (TypeKind::Bits(l), TypeKind::Bits(r)) => l.countspecs_match(r),

            (TypeKind::List(l), TypeKind::List(r))
            | (TypeKind::Set(l), TypeKind::Set(r))
            | (TypeKind::Maybe(l), TypeKind::Maybe(r)) => l.types_match(r.as_ref()),

            (TypeKind::Table(lk, lv), TypeKind::Table(rk, rv)) => {
                lk.types_match(rk.as_ref()) && lv.types_match(rv)
            }

            (TypeKind::Tuple(l), TypeKind::Tuple(r)) => {
                l.len() == r.len() && l.iter().zip(r.iter()).all(|(l, r)| Type::types_match(l, r))
            }

            (TypeKind::Fn(largs, lty), TypeKind::Fn(rargs, rty)) => {
                largs
                    .iter()
                    .zip(rargs.iter())
                    .all(|(l, r)| Type::types_match(l, r))
                    && lty.types_match(rty.as_ref())
            }

            (lother, rother) => lother == rother,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ty_str_bytes = Vec::with_capacity(256);

        crate::writers::pseudocode::writer::Writer::new(&mut ty_str_bytes)
            .write_type(self)
            .map_err(|_| std::fmt::Error)?;

        let ty_str = String::from_utf8(ty_str_bytes).map_err(|_| std::fmt::Error)?;
        write!(f, "{ty_str}")
    }
}

/// Describes the length of Bits types
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum CountSpec {
    Identifier(Box<Identifier>),
    Literal(u64),
    Any,
}

impl CountSpec {
    pub(crate) fn countspecs_match(&self, other: &Self) -> bool {
        if let (Self::Identifier(l), Self::Identifier(r)) = (self, other) {
            l.identifiers_match(r)
        } else {
            self == other
        }
    }
}

impl std::fmt::Display for CountSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CountSpec::Identifier(identifier) => write!(f, "{}", identifier.ident_ref()),
            CountSpec::Literal(n) => write!(f, "{n}"),
            CountSpec::Any => write!(f, "*"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::identifier::{
        pkg_ident::{PackageConstIdentifier, PackageIdentifier},
        Identifier,
    };

    use super::{CountSpec, Type, TypeKind};

    #[test]
    fn display_countspec() {
        assert_eq!("*", format!("{}", CountSpec::Any));
        assert_eq!("42", format!("{}", CountSpec::Literal(42)));
        assert_eq!(
            "n",
            format!(
                "{}",
                CountSpec::Identifier(Box::new(Identifier::PackageIdentifier(
                    PackageIdentifier::Const(PackageConstIdentifier {
                        pkg_name: "SomePackage".to_string(),
                        name: "n".to_string(),
                        pkg_inst_name: None,
                        ty: Type::from_kind(TypeKind::Integer),
                        game_assignment: None,
                        game_inst_name: None,
                        game_name: None,
                        theorem_name: None,
                    })
                )))
            )
        );
    }
}
