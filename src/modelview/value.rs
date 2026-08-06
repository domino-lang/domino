// SPDX-License-Identifier: MIT OR Apache-2.0

//! A generic, project-independent pretty-printer for values found in an SMT model: unwraps
//! `store`/`(as const ..)` array chains into [`Pretty::Map`], `mk-tupleN` into [`Pretty::Tuple`],
//! `sample-id` into [`Pretty::SampleId`], and any other constructor application it recognizes
//! (via a [`CtorMap`]) into a labeled [`Pretty::Record`]. Anything unrecognized still renders,
//! just less prettily ([`Pretty::Unknown`]).

use std::fmt;

use crate::modelview::ctors::CtorMap;
use crate::util::smtmodel::SmtModelEntry;
use crate::writers::smt::exprs::SmtExpr;

#[derive(Debug, Clone, PartialEq)]
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
    /// An uninterpreted (theorem) function, reconstructed from cvc5's nested-`ite` model as a
    /// list of specific input tuples mapped to a value, plus a catch-all default.
    FnTable {
        entries: Vec<(Vec<Option<Pretty>>, Pretty)>,
        default: Box<Pretty>,
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
                write!(f, "{{ ")?;
                for (k, v) in entries {
                    write!(f, "{k}: {v}, ")?;
                }
                write!(f, "..: {default} }}")
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
            Pretty::FnTable { entries, default } => {
                write!(f, "{{ ")?;
                for (keys, value) in entries {
                    write!(f, "{}: {value}, ", format_fn_key(keys))?;
                }
                write!(f, "..: {default} }}")
            }
            Pretty::Unknown(raw) => write!(f, "{raw}"),
        }
    }
}

fn format_fn_key(keys: &[Option<Pretty>]) -> String {
    let rendered: Vec<String> = keys
        .iter()
        .map(|k| match k {
            Some(v) => v.to_string(),
            None => "_".to_string(),
        })
        .collect();
    if rendered.len() == 1 {
        rendered.into_iter().next().unwrap()
    } else {
        format!("({})", rendered.join(", "))
    }
}

/// Renders a single `label: value` line, or (if `value` is compound, e.g. a long `Tuple`, a
/// nested `Record`/`Map`/`FnTable`) a heading line plus recursively indented sub-lines.
fn render_named(pad: &str, indent: usize, label: String, value: &Pretty) -> Vec<String> {
    if value.is_compound() {
        let mut lines = vec![format!("{pad}{label}:")];
        lines.extend(value.render_lines(indent + 1));
        lines
    } else {
        vec![format!("{pad}{label}: {value}")]
    }
}

/// Above this rendered width, a value that could otherwise be inlined (a `Tuple`, or a `Maybe`
/// wrapping one) is instead split into its own indented block, one line per element. Also used
/// as the two-column display's per-column width cap, so a long tuple doesn't dominate a whole row
/// the way a long `Map`/`Record` dump used to before those got block-rendering too.
pub const MAX_INLINE_WIDTH: usize = 60;

impl Pretty {
    /// Whether this value is best rendered as its own indented block (a heading line followed by
    /// nested lines) rather than inline after a `name: ` prefix.
    pub fn is_compound(&self) -> bool {
        match self {
            Pretty::Record { fields, .. } => !fields.is_empty(),
            Pretty::Map { entries, .. } => !entries.is_empty(),
            Pretty::FnTable { .. } => true,
            Pretty::Tuple(items) => {
                !items.is_empty() && self.to_string().chars().count() > MAX_INLINE_WIDTH
            }
            // a `Some(...)` wrapping a long tuple (or other compound value) should still get
            // split, rather than hiding the overflow behind the wrapper.
            Pretty::Maybe(Some(inner)) => inner.is_compound(),
            _ => false,
        }
    }

    /// Renders this value as a list of indented lines: compound fields get their own heading
    /// line followed by recursively indented sub-lines, everything else is a single
    /// `name: value` line. `indent` is the current indentation level (each level is 2 spaces).
    pub fn render_lines(&self, indent: usize) -> Vec<String> {
        let pad = "  ".repeat(indent);
        match self {
            Pretty::Record { fields, .. } if !fields.is_empty() => fields
                .iter()
                .flat_map(|(name, value)| render_named(&pad, indent, name.clone(), value))
                .collect(),
            Pretty::FnTable { entries, default } => {
                let mut lines: Vec<String> = entries
                    .iter()
                    .flat_map(|(keys, value)| render_named(&pad, indent, format_fn_key(keys), value))
                    .collect();
                lines.extend(render_named(&pad, indent, "..".to_string(), default));
                lines
            }
            Pretty::Map { entries, default } if !entries.is_empty() => {
                let mut lines: Vec<String> = entries
                    .iter()
                    .flat_map(|(key, value)| render_named(&pad, indent, key.to_string(), value))
                    .collect();
                lines.extend(render_named(&pad, indent, "..".to_string(), default));
                lines
            }
            Pretty::Tuple(items) if self.is_compound() => items
                .iter()
                .enumerate()
                .flat_map(|(i, item)| render_named(&pad, indent, format!("_{i}"), item))
                .collect(),
            Pretty::Maybe(Some(inner)) if self.is_compound() => {
                let mut lines = vec![format!("{pad}Some:")];
                lines.extend(inner.render_lines(indent + 1));
                lines
            }
            other => vec![format!("{pad}{other}")],
        }
    }

    /// Renders two values (e.g. the same field on the left/right side of an equivalence) as
    /// paired lines suitable for a two-column display, keeping both sides' row counts in sync so
    /// that unrelated fields further down don't drift out of alignment.
    ///
    /// When both sides are records with the exact same field names in the same order (the common
    /// case: left/right game states share the same underlying constructor, see
    /// [`crate::modelview::ctors`]), fields are recursively paired by name so mismatched values
    /// (e.g. one side having an extra `Map` override the other lacks) still line up next to each
    /// other. Otherwise, both sides are rendered independently and zipped row-by-row, padding the
    /// shorter side with blank lines.
    pub fn render_pair_lines(left: &Pretty, right: &Pretty, indent: usize) -> Vec<(String, String)> {
        let pad = "  ".repeat(indent);

        if let (Pretty::Record { fields: lf, .. }, Pretty::Record { fields: rf, .. }) =
            (left, right)
        {
            let names_match = !lf.is_empty()
                && lf.len() == rf.len()
                && lf.iter().zip(rf).all(|(l, r)| l.0 == r.0);
            if names_match {
                let mut lines = Vec::new();
                for ((name, lval), (_, rval)) in lf.iter().zip(rf) {
                    if lval.is_compound() || rval.is_compound() {
                        lines.push((format!("{pad}{name}:"), format!("{pad}{name}:")));
                        lines.extend(Pretty::render_pair_lines(lval, rval, indent + 1));
                    } else {
                        lines.push((
                            format!("{pad}{name}: {lval}"),
                            format!("{pad}{name}: {rval}"),
                        ));
                    }
                }
                return lines;
            }
        }

        let left_lines = left.render_lines(indent);
        let right_lines = right.render_lines(indent);
        let rows = left_lines.len().max(right_lines.len());
        (0..rows)
            .map(|i| {
                (
                    left_lines.get(i).cloned().unwrap_or_default(),
                    right_lines.get(i).cloned().unwrap_or_default(),
                )
            })
            .collect()
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

/// Cap on the number of case-split entries extracted from a function's `ite` body, as a safety
/// net against pathologically deep decision trees.
const MAX_FN_ENTRIES: usize = 64;

/// Interprets a `define-fun` model entry that takes arguments (an uninterpreted/theorem
/// function) as a [`Pretty::FnTable`]: cvc5 represents such a function as a chain of nested
/// `ite`s case-splitting on equality with specific argument values, bottoming out in a default
/// value for everything else. Entries with no arguments are interpreted as plain values.
pub fn interpret_function(entry: &SmtModelEntry, ctors: &CtorMap) -> Pretty {
    let arg_names: Vec<String> = entry.args().iter().map(|(name, _)| name.clone()).collect();
    if arg_names.is_empty() {
        return interpret(&entry.value_expr(), ctors);
    }

    let mut entries = Vec::new();
    let prefix = vec![None; arg_names.len()];
    let default = flatten_ite(&entry.value_expr(), &arg_names, ctors, &prefix, &mut entries);
    Pretty::FnTable {
        entries,
        default: Box::new(default),
    }
}

/// Extracts equality constraints on named arguments from an `ite` condition: `(= argN c)`,
/// `(= c argN)`, or a conjunction (`and ...`) of such equalities. Returns an empty list if the
/// condition isn't shaped like a case-split on the function's arguments (in which case the
/// caller treats the whole `ite` as an opaque leaf value instead).
fn parse_condition<'e>(cond: &'e SmtExpr, arg_names: &[String]) -> Vec<(usize, &'e SmtExpr)> {
    fn arg_index(expr: &SmtExpr, arg_names: &[String]) -> Option<usize> {
        match expr {
            SmtExpr::Atom(a) => arg_names.iter().position(|name| name == a),
            _ => None,
        }
    }

    match cond {
        SmtExpr::List(items) if items.len() == 3 && is_atom(&items[0], "=") => {
            let (lhs, rhs) = (&items[1], &items[2]);
            if let Some(idx) = arg_index(lhs, arg_names) {
                vec![(idx, rhs)]
            } else if let Some(idx) = arg_index(rhs, arg_names) {
                vec![(idx, lhs)]
            } else {
                vec![]
            }
        }
        SmtExpr::List(items) if items.len() > 1 && is_atom(&items[0], "and") => items[1..]
            .iter()
            .flat_map(|c| parse_condition(c, arg_names))
            .collect(),
        _ => vec![],
    }
}

/// Recursively walks a function body, splitting it into `(input tuple, value)` case-split
/// entries pushed to `out`, and returns the value that applies to `prefix` when none of the
/// case-split's deeper conditions hold (i.e. this subtree's own default).
fn flatten_ite(
    expr: &SmtExpr,
    arg_names: &[String],
    ctors: &CtorMap,
    prefix: &[Option<Pretty>],
    out: &mut Vec<(Vec<Option<Pretty>>, Pretty)>,
) -> Pretty {
    if out.len() < MAX_FN_ENTRIES {
        if let SmtExpr::List(items) = expr {
            if items.len() == 4 && is_atom(&items[0], "ite") {
                let conds = parse_condition(&items[1], arg_names);
                if !conds.is_empty() {
                    let mut then_prefix = prefix.to_vec();
                    for (idx, value_expr) in &conds {
                        then_prefix[*idx] = Some(interpret(value_expr, ctors));
                    }
                    let then_value = flatten_ite(&items[2], arg_names, ctors, &then_prefix, out);
                    out.push((then_prefix, then_value));
                    return flatten_ite(&items[3], arg_names, ctors, prefix, out);
                }
            }
        }
    }

    interpret(expr, ctors)
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

    #[test]
    fn interprets_nullary_function_entry_as_plain_value() {
        let ctors = CtorMap::new();
        let entry = SmtModelEntry::IntEntry {
            name: "foo".to_string(),
            args: vec![],
            value: 42,
        };
        assert!(matches!(interpret_function(&entry, &ctors), Pretty::Int(42)));
    }

    #[test]
    fn interprets_single_arg_function_as_table_with_default() {
        let ctors = CtorMap::new();
        // (ite (= _arg_1 7) 99 6)
        let body = list(vec![
            atom("ite"),
            list(vec![atom("="), atom("_arg_1"), atom("7")]),
            atom("99"),
            atom("6"),
        ]);
        let entry = SmtModelEntry::UnknownEntry {
            name: "<<func-f>>".to_string(),
            args: vec![("_arg_1".to_string(), "Int".to_string())],
            ty: "Int".to_string(),
            value: body,
        };

        match interpret_function(&entry, &ctors) {
            Pretty::FnTable { entries, default } => {
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].0, vec![Some(Pretty::Int(7))]);
                assert!(matches!(entries[0].1, Pretty::Int(99)));
                assert!(matches!(*default, Pretty::Int(6)));
            }
            other => panic!("expected fn table, got {other:?}"),
        }
    }

    #[test]
    fn interprets_multi_arg_nested_function_as_single_point_override() {
        let ctors = CtorMap::new();
        // mirrors cvc5's real output for a 2-arg uninterpreted function with one override point:
        // (ite (= _arg_1 7) (ite (= _arg_2 12) 5 6) 6)
        let body = list(vec![
            atom("ite"),
            list(vec![atom("="), atom("_arg_1"), atom("7")]),
            list(vec![
                atom("ite"),
                list(vec![atom("="), atom("_arg_2"), atom("12")]),
                atom("5"),
                atom("6"),
            ]),
            atom("6"),
        ]);
        let entry = SmtModelEntry::UnknownEntry {
            name: "<<func-mac>>".to_string(),
            args: vec![
                ("_arg_1".to_string(), "Int".to_string()),
                ("_arg_2".to_string(), "Int".to_string()),
            ],
            ty: "Int".to_string(),
            value: body,
        };

        match interpret_function(&entry, &ctors) {
            Pretty::FnTable { entries, default } => {
                // the fully-specified point (7, 12) -> 5, and the partial-match fallback
                // (7, _) -> 6 should both show up, in more-specific-first order.
                assert_eq!(entries.len(), 2);
                assert_eq!(
                    entries[0].0,
                    vec![Some(Pretty::Int(7)), Some(Pretty::Int(12))]
                );
                assert!(matches!(entries[0].1, Pretty::Int(5)));
                assert_eq!(entries[1].0, vec![Some(Pretty::Int(7)), None]);
                assert!(matches!(entries[1].1, Pretty::Int(6)));
                assert!(matches!(*default, Pretty::Int(6)));
            }
            other => panic!("expected fn table, got {other:?}"),
        }
    }
}
