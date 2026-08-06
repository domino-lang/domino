// SPDX-License-Identifier: MIT OR Apache-2.0

//! Best-effort, readable-not-compileable translation of a claim's SMT-LIB
//! boolean expression into EasyCrypt-flavored surface syntax.
//!
//! This only translates the logical formula (the `body` of a
//! `define-lemma`/`define-state-relation`), never the surrounding Domino
//! macro syntax -- see [`crate::writers::claim_source`], which captures the
//! Domino source verbatim instead and calls into this module per claim.
//!
//! This is deliberately not a semantically-faithful compiler target: sorts
//! like `Bits_128` have no canonical EasyCrypt spelling without knowing the
//! target proof's own type aliases, so those (and any construct this module
//! doesn't specifically recognize) are passed through as plain function
//! application / raw text rather than guessed at. The goal is a formula a
//! human proof reviewer can read next to the original Domino/SMT source, not
//! one EasyCrypt's own parser would accept.

use crate::writers::smt::exprs::SmtExpr;

fn atom(expr: &SmtExpr) -> Option<&str> {
    match expr {
        SmtExpr::Atom(s) => Some(s.as_str()),
        _ => None,
    }
}

/// Renders `expr` as a raw, parenthesized s-expression -- the fallback for
/// anything this translator doesn't specifically recognize, so nothing is
/// silently dropped.
fn raw(expr: &SmtExpr) -> String {
    match expr {
        SmtExpr::Atom(s) => s.clone(),
        SmtExpr::Comment(s) => format!(";; {s}"),
        SmtExpr::List(items) => {
            format!("({})", items.iter().map(raw).collect::<Vec<_>>().join(" "))
        }
    }
}

fn parenthesize(s: String) -> String {
    format!("({s})")
}

/// Joins already-translated `terms` with `sep`, wrapping in parens if
/// there's more than one (a lone term needs no extra parens).
fn infix(terms: &[String], sep: &str) -> String {
    match terms {
        [] => String::new(),
        [only] => only.clone(),
        _ => parenthesize(terms.join(sep)),
    }
}

/// SMT-LIB's chainable operators (`=`, `<`, `<=`, `>`, `>=` with more than
/// two arguments mean every *consecutive* pair satisfies the relation, which
/// EasyCrypt has no direct syntax for; expand into a conjunction over
/// consecutive pairs, which is equivalence-preserving for these).
///
/// The common two-argument case is left unparenthesized (unlike `infix`):
/// comparisons bind tighter than `/\`/`\/`/`=>` in every convention this is
/// meant to read naturally under, and they never nest inside arithmetic, so
/// there's no precedence hazard in leaving them bare -- and it's the
/// difference between `(a = b /\ c = d)` and the much noisier
/// `((a = b) /\ (c = d))` once one of these sits inside a conjunction.
fn chained(args: &[String], op: &str) -> String {
    match args {
        [a, b] => format!("{a} {op} {b}"),
        _ => {
            let pairs: Vec<String> = args
                .windows(2)
                .map(|w| format!("{} {op} {}", w[0], w[1]))
                .collect();
            parenthesize(pairs.join(" /\\ "))
        }
    }
}

/// `distinct` means *all* pairs differ, not just consecutive ones -- unlike
/// `chained`, this needs the full pairwise expansion to stay faithful.
fn all_pairs_distinct(args: &[String]) -> String {
    if let [a, b] = args {
        return format!("{a} <> {b}");
    }
    let mut pairs = Vec::new();
    for i in 0..args.len() {
        for j in (i + 1)..args.len() {
            pairs.push(format!("{} <> {}", args[i], args[j]));
        }
    }
    parenthesize(pairs.join(" /\\ "))
}

fn translate_sort(sort: &SmtExpr) -> String {
    match sort {
        SmtExpr::Atom(name) => match name.as_str() {
            "Int" => "int".to_string(),
            "Bool" => "bool".to_string(),
            other => other.to_string(),
        },
        SmtExpr::List(items) => {
            let head = items.first().and_then(atom);
            match head {
                Some("Maybe") if items.len() == 2 => {
                    format!("{} option", translate_sort(&items[1]))
                }
                Some("Array") if items.len() == 3 => format!(
                    "{} -> {}",
                    translate_sort(&items[1]),
                    translate_sort(&items[2])
                ),
                Some(name) if name.starts_with("Tuple") && items.len() > 1 => items[1..]
                    .iter()
                    .map(translate_sort)
                    .collect::<Vec<_>>()
                    .join(" * "),
                _ => raw(sort),
            }
        }
        SmtExpr::Comment(_) => raw(sort),
    }
}

fn translate_binding(binding: &SmtExpr) -> String {
    match binding {
        SmtExpr::List(items) if items.len() == 2 => {
            format!("{}: {}", raw(&items[0]), translate_sort(&items[1]))
        }
        other => raw(other),
    }
}

/// Parses a `elN-K` tuple-projection function name (domino's naming for the
/// K-th selector of an N-ary tuple, e.g. `el2-1`, `el11-7`) into `(n, k)`.
fn parse_tuple_selector(name: &str) -> Option<(u32, u32)> {
    let rest = name.strip_prefix("el")?;
    let (n, k) = rest.split_once('-')?;
    Some((n.parse().ok()?, k.parse().ok()?))
}

fn parse_tuple_constructor(name: &str) -> Option<u32> {
    name.strip_prefix("mk-tuple")?.parse().ok()
}

/// A handful of bare-atom (zero-arity, no parens) constants that show up
/// written without an enclosing `(...)`, most often inside an `(as none (Maybe
/// T))` sort ascription.
fn translate_atom(name: &str) -> String {
    match name {
        "none" | "mk-none" => "None".to_string(),
        other => other.to_string(),
    }
}

/// Translates one SMT-LIB term (a claim's body, or a subterm of it) into
/// EasyCrypt-flavored surface syntax. See the module docs for what "best
/// effort" means here.
pub fn translate_term(expr: &SmtExpr) -> String {
    match expr {
        SmtExpr::Atom(s) => translate_atom(s),
        SmtExpr::Comment(_) => raw(expr),
        SmtExpr::List(items) => translate_list(items),
    }
}

fn translate_list(items: &[SmtExpr]) -> String {
    let Some(head) = items.first().and_then(atom) else {
        return raw(&SmtExpr::List(items.to_vec()));
    };
    let args = &items[1..];
    let t: Vec<String> = args.iter().map(translate_term).collect();

    match head {
        "and" if args.is_empty() => "true".to_string(),
        "and" => infix(&t, " /\\ "),
        "or" if args.is_empty() => "false".to_string(),
        "or" => infix(&t, " \\/ "),
        "not" if args.len() == 1 => format!("!({})", t[0]),
        "=>" if args.len() == 2 => parenthesize(format!("{} => {}", t[0], t[1])),
        "<=>" if args.len() == 2 => parenthesize(format!("{} <=> {}", t[0], t[1])),
        "=" if args.len() >= 2 => chained(&t, "="),
        "distinct" if args.len() >= 2 => all_pairs_distinct(&t),
        "<" | ">" | "<=" | ">=" if args.len() >= 2 => chained(&t, head),
        "+" if !args.is_empty() => infix(&t, " + "),
        "*" if !args.is_empty() => infix(&t, " * "),
        "-" if args.len() == 1 => format!("-({})", t[0]),
        "-" if args.len() >= 2 => infix(&t, " - "),
        "ite" if args.len() == 3 => {
            parenthesize(format!("if {} then {} else {}", t[0], t[1], t[2]))
        }
        "forall" | "exists" if args.len() == 2 => {
            let SmtExpr::List(bindings) = &args[0] else {
                return raw(&SmtExpr::List(items.to_vec()));
            };
            let bindings = bindings
                .iter()
                .map(translate_binding)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{head} ({bindings}), {}", t[1])
        }
        "let" if args.len() == 2 => {
            let SmtExpr::List(bindings) = &args[0] else {
                return raw(&SmtExpr::List(items.to_vec()));
            };
            let prefix: String = bindings
                .iter()
                .map(|b| match b {
                    SmtExpr::List(pair) if pair.len() == 2 => {
                        format!("let {} = {} in ", raw(&pair[0]), translate_term(&pair[1]))
                    }
                    other => format!("let {} in ", raw(other)),
                })
                .collect();
            format!("{prefix}{}", t[1])
        }
        // Sort ascription, e.g. `(as mk-none (Maybe Int))` -- the sort is
        // there to disambiguate a polymorphic constructor for the solver;
        // for a human reader the value alone is clearer.
        "as" if args.len() == 2 => t[0].clone(),
        "none" | "mk-none" if args.is_empty() => "None".to_string(),
        "some" | "mk-some" if args.len() == 1 => format!("Some({})", t[0]),
        "is-mk-none" | "is-none" if args.len() == 1 => parenthesize(format!("{} = None", t[0])),
        "is-mk-some" | "is-some" if args.len() == 1 => parenthesize(format!("{} <> None", t[0])),
        "maybe-get" if args.len() == 1 => format!("oget({})", t[0]),
        "select" if args.len() == 2 => format!("{}.[{}]", t[0], t[1]),
        "store" if args.len() == 3 => format!("{}.[{} <- {}]", t[0], t[1], t[2]),
        _ if args.len() == 1 && parse_tuple_selector(head).is_some() => {
            let (_, k) = parse_tuple_selector(head).unwrap();
            format!("{}.`{k}", t[0])
        }
        _ if !args.is_empty() && parse_tuple_constructor(head).is_some() => {
            parenthesize(t.join(", "))
        }
        _ => {
            if t.is_empty() {
                head.to_string()
            } else {
                format!("{head}({})", t.join(", "))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::smtparser::SmtParser;

    #[derive(Default)]
    struct Capture(Option<SmtExpr>);
    impl SmtParser<SmtExpr> for Capture {
        fn handle_atom(&mut self, content: &str) -> crate::util::smtparser::Result<SmtExpr> {
            Ok(SmtExpr::Atom(content.to_string()))
        }
        fn handle_list(
            &mut self,
            content: Vec<SmtExpr>,
        ) -> crate::util::smtparser::Result<SmtExpr> {
            Ok(SmtExpr::List(content))
        }
        fn handle_sexp(&mut self, parsed: SmtExpr) -> crate::util::smtparser::Result<()> {
            self.0 = Some(parsed);
            Ok(())
        }
    }

    fn parse(s: &str) -> SmtExpr {
        let mut c = Capture::default();
        c.parse_sexp(s).expect("test input should parse");
        c.0.expect("expected exactly one top-level expression")
    }

    fn translate(s: &str) -> String {
        translate_term(&parse(s))
    }

    #[test]
    fn boolean_connectives() {
        assert_eq!(translate("(and a b c)"), "(a /\\ b /\\ c)");
        assert_eq!(translate("(or a b)"), "(a \\/ b)");
        assert_eq!(translate("(not a)"), "!(a)");
        assert_eq!(translate("(=> a b)"), "(a => b)");
    }

    #[test]
    fn chained_equality_and_comparison() {
        assert_eq!(translate("(= a b)"), "a = b");
        assert_eq!(translate("(= a b c)"), "(a = b /\\ b = c)");
        assert_eq!(translate("(< i (- h 1))"), "i < (h - 1)");
    }

    #[test]
    fn distinct_is_all_pairs_not_just_consecutive() {
        assert_eq!(
            translate("(distinct a b c)"),
            "(a <> b /\\ a <> c /\\ b <> c)"
        );
    }

    #[test]
    fn ite_becomes_if_then_else() {
        assert_eq!(translate("(ite c t e)"), "(if c then t else e)");
    }

    #[test]
    fn forall_binder_translates_sorts() {
        assert_eq!(
            translate("(forall ((kid Int)) (> kid 0))"),
            "forall (kid: int), kid > 0"
        );
    }

    #[test]
    fn maybe_and_option_helpers() {
        assert_eq!(translate("(is-mk-none x)"), "(x = None)");
        assert_eq!(translate("(is-mk-some x)"), "(x <> None)");
        assert_eq!(translate("(maybe-get x)"), "oget(x)");
        assert_eq!(translate("(as mk-none (Maybe Int))"), "None");
        assert_eq!(translate("(mk-some x)"), "Some(x)");
    }

    #[test]
    fn tuple_constructors_and_selectors_are_generic_over_arity() {
        assert_eq!(translate("(mk-tuple2 a b)"), "(a, b)");
        assert_eq!(translate("(el2-1 x)"), "x.`1");
        assert_eq!(translate("(el11-7 x)"), "x.`7");
    }

    #[test]
    fn array_select_and_store() {
        assert_eq!(translate("(select arr idx)"), "arr.[idx]");
        assert_eq!(translate("(store arr idx v)"), "arr.[idx <- v]");
    }

    #[test]
    fn dotted_state_accessors_pass_through_unchanged() {
        assert_eq!(
            translate("(= old-state-left.Pkg.field old-state-right.Pkg.field)"),
            "old-state-left.Pkg.field = old-state-right.Pkg.field"
        );
    }

    #[test]
    fn unknown_function_falls_back_to_application_syntax() {
        assert_eq!(
            translate("(kem-correctness pk sk)"),
            "kem-correctness(pk, sk)"
        );
    }

    #[test]
    fn sort_translation_covers_maybe_array_and_tuple() {
        assert_eq!(translate_sort(&parse("(Maybe Bool)")), "bool option");
        assert_eq!(
            translate_sort(&parse("(Array (Tuple2 Bool Bool) (Maybe Bool))")),
            "bool * bool -> bool option"
        );
    }

    #[test]
    fn a_realistic_yao_style_case_lemma() {
        // Mirrors example-projects/yao's
        // relation-case-i-lt-hminusone-assumptions-... shape.
        let out = translate(
            "(=> (< i (- h 1)) (= (select st.z (mk-tuple2 i l)) (select st2.z (mk-tuple2 i l))))",
        );
        assert_eq!(out, "(i < (h - 1) => st.z.[(i, l)] = st2.z.[(i, l)])");
    }
}
