// SPDX-License-Identifier: MIT OR Apache-2.0

//! A generic, project-independent pretty-printer for values found in an SMT model: unwraps
//! `store`/`(as const ..)` array chains into [`Pretty::Map`], `mk-tupleN` into [`Pretty::Tuple`],
//! `sample-id` into [`Pretty::SampleId`], and any other constructor application it recognizes
//! (via a [`CtorMap`]) into a labeled [`Pretty::Record`]. Anything unrecognized still renders,
//! just less prettily ([`Pretty::Unknown`]).

use std::fmt;

use crate::modelview::ctors::CtorMap;
use crate::writers::smt::exprs::SmtExpr;

#[derive(Debug, Clone)]
pub enum Pretty {
    Bool(bool),
    Int(i64),
    Str(String),
    /// An opaque, finite-domain element such as `@Bits_n_4`, or any other bare atom we didn't
    /// otherwise recognize.
    Opaque(String),
    SampleId {
        pkg: String,
        oracle: String,
        name: String,
    },
    Tuple(Vec<Pretty>),
    Maybe(Option<Box<Pretty>>),
    Map {
        entries: Vec<(Pretty, Pretty)>,
        default: Box<Pretty>,
    },
    Record {
        label: String,
        fields: Vec<(String, Pretty)>,
    },
    /// A function application we don't have any special handling or ctor-map entry for.
    Unknown(String),
}

impl fmt::Display for Pretty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pretty::Bool(b) => write!(f, "{b}"),
            Pretty::Int(i) => write!(f, "{i}"),
            Pretty::Str(s) => write!(f, "{s:?}"),
            Pretty::Opaque(s) => write!(f, "{s}"),
            Pretty::SampleId { pkg, oracle, name } => write!(f, "{pkg}.{oracle}/{name}"),
            Pretty::Tuple(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, ")")
            }
            Pretty::Maybe(None) => write!(f, "None"),
            Pretty::Maybe(Some(v)) => write!(f, "Some({v})"),
            Pretty::Map { entries, default } => {
                write!(f, "{{")?;
                for (k, v) in entries {
                    write!(f, "{k} -> {v}, ")?;
                }
                write!(f, "_ -> {default}}}")
            }
            Pretty::Record { label, fields } => {
                if fields.is_empty() {
                    return write!(f, "{label}");
                }
                write!(f, "{label} {{ ")?;
                for (i, (name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {value}")?;
                }
                write!(f, " }}")
            }
            Pretty::Unknown(raw) => write!(f, "{raw}"),
        }
    }
}

fn is_atom(expr: &SmtExpr, atom: &str) -> bool {
    matches!(expr, SmtExpr::Atom(a) if a == atom)
}

fn as_atom(expr: &SmtExpr) -> Option<&str> {
    match expr {
        SmtExpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}

/// The symbol being applied in a function application, unwrapping a sort ascription in head
/// position: cvc5 disambiguates parametric constructors like `mk-some` by writing the
/// application as `((as mk-some (Maybe Bits_n)) arg)` rather than plain `(mk-some arg)`.
fn effective_head(expr: &SmtExpr) -> Option<&str> {
    match expr {
        SmtExpr::Atom(a) => Some(a.as_str()),
        SmtExpr::List(items) if items.len() == 3 && is_atom(&items[0], "as") => as_atom(&items[1]),
        _ => None,
    }
}

/// Tries to interpret `expr` as a `store`/`(as const ..)` array literal chain.
fn interpret_map(expr: &SmtExpr, ctors: &CtorMap) -> Option<Pretty> {
    match expr {
        SmtExpr::List(items) if items.len() == 4 && is_atom(&items[0], "store") => {
            let mut map = interpret_map(&items[1], ctors)?;
            let key = interpret(&items[2], ctors);
            let value = interpret(&items[3], ctors);
            if let Pretty::Map { entries, .. } = &mut map {
                entries.push((key, value));
            }
            Some(map)
        }
        SmtExpr::List(items) if items.len() == 2 => {
            if let SmtExpr::List(as_const) = &items[0] {
                if as_const.len() == 3
                    && is_atom(&as_const[0], "as")
                    && is_atom(&as_const[1], "const")
                {
                    return Some(Pretty::Map {
                        entries: vec![],
                        default: Box::new(interpret(&items[1], ctors)),
                    });
                }
            }
            None
        }
        _ => None,
    }
}

/// Interprets a raw SMT value expression (the body of a model entry, or a sub-term of one) into
/// a [`Pretty`] tree, using `ctors` to recognize and label Domino-generated constructors.
pub fn interpret(expr: &SmtExpr, ctors: &CtorMap) -> Pretty {
    if let Some(map) = interpret_map(expr, ctors) {
        return map;
    }

    match expr {
        SmtExpr::Comment(_) => Pretty::Unknown(String::new()),
        SmtExpr::Atom(atom) => interpret_atom(atom, ctors),
        SmtExpr::List(items) if items.is_empty() => Pretty::Unknown("()".to_string()),
        SmtExpr::List(items) => interpret_application(items, ctors),
    }
}

/// Nullary constructors (no fields) are represented as bare symbols in SMT-LIB, not as a
/// 1-element application -- e.g. `mk-none`, or a zero-field package state like
/// `mk-pkg-state-ReductionMac-<params>`. Those need to be recognized here too, not just in
/// [`interpret_application`].
fn interpret_atom(atom: &str, ctors: &CtorMap) -> Pretty {
    match atom {
        "true" => Pretty::Bool(true),
        "false" => Pretty::Bool(false),
        "mk-none" => Pretty::Maybe(None),
        _ => {
            if let Ok(i) = atom.parse::<i64>() {
                Pretty::Int(i)
            } else if let Some(stripped) = atom.strip_prefix('"').and_then(|s| s.strip_suffix('"'))
            {
                Pretty::Str(stripped.to_string())
            } else if let Some(ctor) = ctors.get(atom) {
                let label = if ctor.label.is_empty() {
                    atom.to_string()
                } else {
                    ctor.label.clone()
                };
                // see the arity-mismatch comment in `interpret_application`: if the project has
                // drifted, don't claim fields that weren't actually applied.
                if ctor.fields.is_empty() {
                    Pretty::Record {
                        label,
                        fields: vec![],
                    }
                } else {
                    Pretty::Opaque(atom.to_string())
                }
            } else {
                Pretty::Opaque(atom.to_string())
            }
        }
    }
}

fn interpret_application(items: &[SmtExpr], ctors: &CtorMap) -> Pretty {
    let head = effective_head(&items[0]);
    let args = &items[1..];

    match head {
        // (- N): negative integer literal
        Some("-") if args.len() == 1 => {
            if let Pretty::Int(i) = interpret(&args[0], ctors) {
                return Pretty::Int(-i);
            }
            render_unknown(items)
        }
        // (as X Sort): sort ascription, only the value matters to us
        Some("as") if args.len() == 2 => interpret(&args[0], ctors),
        // (sample-id "pkg" "oracle" "name")
        Some("sample-id") if args.len() == 3 => {
            let unquote = |e: &SmtExpr| match interpret(e, ctors) {
                Pretty::Str(s) => s,
                other => other.to_string(),
            };
            Pretty::SampleId {
                pkg: unquote(&args[0]),
                oracle: unquote(&args[1]),
                name: unquote(&args[2]),
            }
        }
        Some(head) if head.starts_with("mk-tuple") => Pretty::Tuple(
            args.iter()
                .map(|arg| interpret(arg, ctors))
                .collect::<Vec<_>>(),
        ),
        Some("mk-some") if args.len() == 1 => {
            Pretty::Maybe(Some(Box::new(interpret(&args[0], ctors))))
        }
        Some("mk-none") => Pretty::Maybe(None),
        Some(head) => {
            if let Some(ctor) = ctors.get(head) {
                let label = if ctor.label.is_empty() {
                    head.to_string()
                } else {
                    ctor.label.clone()
                };

                // The project may have changed since this model was generated (e.g. a package's
                // state or a theorem's consts were added/removed): if the field count we derived
                // from the *current* project doesn't match the arity actually applied in the
                // model, trust the model's arity and fall back to positional placeholders rather
                // than risk silently mislabeling a value under the wrong field name.
                let fields = if ctor.fields.len() == args.len() {
                    ctor.fields
                        .iter()
                        .cloned()
                        .zip(args.iter())
                        .map(|(name, arg)| (name, interpret(arg, ctors)))
                        .collect()
                } else {
                    args.iter()
                        .enumerate()
                        .map(|(i, arg)| (format!("[[field {i}]]"), interpret(arg, ctors)))
                        .collect()
                };
                Pretty::Record { label, fields }
            } else {
                render_unknown(items)
            }
        }
        None => render_unknown(items),
    }
}

fn render_unknown(items: &[SmtExpr]) -> Pretty {
    Pretty::Unknown(SmtExpr::List(items.to_vec()).to_string())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::modelview::ctors::CtorInfo;

    fn atom(s: &str) -> SmtExpr {
        SmtExpr::Atom(s.to_string())
    }

    fn list(items: Vec<SmtExpr>) -> SmtExpr {
        SmtExpr::List(items)
    }

    #[test]
    fn interprets_plain_leaves() {
        let ctors = CtorMap::new();
        assert!(matches!(interpret(&atom("true"), &ctors), Pretty::Bool(true)));
        assert!(matches!(interpret(&atom("false"), &ctors), Pretty::Bool(false)));
        assert!(matches!(interpret(&atom("42"), &ctors), Pretty::Int(42)));
        assert!(matches!(
            interpret(&list(vec![atom("-"), atom("4")]), &ctors),
            Pretty::Int(-4)
        ));
        assert!(matches!(interpret(&atom("@Bits_n_3"), &ctors), Pretty::Opaque(s) if s == "@Bits_n_3"));
    }

    #[test]
    fn interprets_as_wrapper() {
        let ctors = CtorMap::new();
        let expr = list(vec![atom("as"), atom("@Bits_n_0"), atom("Bits_n")]);
        assert!(matches!(interpret(&expr, &ctors), Pretty::Opaque(s) if s == "@Bits_n_0"));
    }

    #[test]
    fn interprets_tuple_and_maybe() {
        let ctors = CtorMap::new();

        let tuple = list(vec![atom("mk-tuple2"), atom("1"), atom("2")]);
        match interpret(&tuple, &ctors) {
            Pretty::Tuple(items) => assert_eq!(items.len(), 2),
            other => panic!("expected tuple, got {other:?}"),
        }

        let some = list(vec![atom("mk-some"), atom("7")]);
        assert!(matches!(interpret(&some, &ctors), Pretty::Maybe(Some(_))));
        assert!(matches!(interpret(&atom("mk-none"), &ctors), Pretty::Maybe(None)));
    }

    #[test]
    fn interprets_sample_id() {
        let ctors = CtorMap::new();
        let expr = list(vec![
            atom("sample-id"),
            atom("\"PRF\""),
            atom("\"NewKey\""),
            atom("\"1\""),
        ]);
        match interpret(&expr, &ctors) {
            Pretty::SampleId { pkg, oracle, name } => {
                assert_eq!(pkg, "PRF");
                assert_eq!(oracle, "NewKey");
                assert_eq!(name, "1");
            }
            other => panic!("expected sample id, got {other:?}"),
        }
    }

    #[test]
    fn interprets_store_chains_as_maps() {
        let ctors = CtorMap::new();
        // ((as const (Array Int Bool)) false)
        let base = list(vec![
            list(vec![atom("as"), atom("const"), atom("(Array Int Bool)")]),
            atom("false"),
        ]);
        // (store BASE 0 true)
        let expr = list(vec![atom("store"), base, atom("0"), atom("true")]);

        match interpret(&expr, &ctors) {
            Pretty::Map { entries, default } => {
                assert_eq!(entries.len(), 1);
                assert!(matches!(*default, Pretty::Bool(false)));
                assert!(matches!(entries[0].0, Pretty::Int(0)));
                assert!(matches!(entries[0].1, Pretty::Bool(true)));
            }
            other => panic!("expected map, got {other:?}"),
        }
    }

    #[test]
    fn interprets_known_constructor_as_record_with_matching_arity() {
        let mut ctors = CtorMap::new();
        ctors.insert(
            "mk-foo".to_string(),
            CtorInfo {
                label: "Foo".to_string(),
                fields: vec!["a".to_string(), "b".to_string()],
            },
        );

        let expr = list(vec![atom("mk-foo"), atom("1"), atom("true")]);
        match interpret(&expr, &ctors) {
            Pretty::Record { label, fields } => {
                assert_eq!(label, "Foo");
                assert_eq!(fields[0].0, "a");
                assert_eq!(fields[1].0, "b");
            }
            other => panic!("expected record, got {other:?}"),
        }
    }

    #[test]
    fn falls_back_to_placeholders_on_arity_mismatch() {
        // simulates the project having drifted since the model was generated: the ctor map
        // (built from the *current* project) expects 3 fields, but the model only applied 2.
        let mut ctors = CtorMap::new();
        ctors.insert(
            "mk-foo".to_string(),
            CtorInfo {
                label: "Foo".to_string(),
                fields: vec!["a".to_string(), "b".to_string(), "c".to_string()],
            },
        );

        let expr = list(vec![atom("mk-foo"), atom("1"), atom("2")]);
        match interpret(&expr, &ctors) {
            Pretty::Record { fields, .. } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "[[field 0]]");
                assert_eq!(fields[1].0, "[[field 1]]");
            }
            other => panic!("expected record, got {other:?}"),
        }
    }
}
