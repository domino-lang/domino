// SPDX-License-Identifier: MIT OR Apache-2.0

//! Identifier mangling: turning arbitrary Domino identifiers into names that
//! are legal EasyCrypt and, within one namespace, collision-free.

use std::collections::HashMap;

/// The EasyCrypt lexer's reserved words, sorted. Source: `ecLexer.mll`, as
/// recorded in `docs/stories/easycrypt/00-overview.md` §8.1.
const KEYWORDS: &[&str] = &[
    "abbrev",
    "abort",
    "abstract",
    "admit",
    "admitted",
    "algebra",
    "alias",
    "apply",
    "as",
    "assert",
    "assumption",
    "async",
    "auto",
    "axiom",
    "axiomatized",
    "beta",
    "by",
    "byehoare",
    "byequiv",
    "byphoare",
    "bypr",
    "byupto",
    "call",
    "case",
    "cbv",
    "cfold",
    "change",
    "check",
    "class",
    "clear",
    "clone",
    "congr",
    "conseq",
    "const",
    "coq",
    "debug",
    "declare",
    "delta",
    "do",
    "done",
    "dump",
    "eager",
    "ecall",
    "edit",
    "ehoare",
    "elif",
    "elim",
    "else",
    "end",
    "equiv",
    "eta",
    "exact",
    "exfalso",
    "exists",
    "exit",
    "exlim",
    "expect",
    "export",
    "fail",
    "fel",
    "first",
    "fission",
    "fix",
    "for",
    "forall",
    "from",
    "fun",
    "fusion",
    "gen",
    "glob",
    "goal",
    "have",
    "hint",
    "hoare",
    "idtac",
    "if",
    "import",
    "in",
    "include",
    "inductive",
    "inline",
    "instance",
    "interleave",
    "iota",
    "is",
    "islossless",
    "kill",
    "last",
    "left",
    "lemma",
    "let",
    "local",
    "locate",
    "logic",
    "match",
    "modpath",
    "module",
    "move",
    "notation",
    "of",
    "op",
    "outline",
    "phoare",
    "pose",
    "pr_bounded",
    "pragma",
    "pred",
    "print",
    "proc",
    "progress",
    "proof",
    "prover",
    "qed",
    "rcondf",
    "rcondt",
    "realize",
    "reflexivity",
    "remove",
    "rename",
    "replace",
    "require",
    "res",
    "return",
    "rewrite",
    "right",
    "rnd",
    "rndsem",
    "rwnormal",
    "search",
    "section",
    "seq",
    "sim",
    "simplify",
    "skip",
    "smt",
    "solve",
    "sp",
    "split",
    "splitwhile",
    "subst",
    "suff",
    "swap",
    "symmetry",
    "then",
    "theory",
    "time",
    "timeout",
    "transitivity",
    "trivial",
    "try",
    "type",
    "undo",
    "unroll",
    "var",
    "weakmem",
    "while",
    "with",
    "wlog",
    "wp",
    "zeta",
];

fn is_keyword(name: &str) -> bool {
    KEYWORDS.binary_search(&name).is_ok()
}

/// The namespace a name is mangled into. Two names only collide if they are
/// mangled within the same [`NameKind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NameKind {
    Module,
    ModuleType,
    Type,
    Op,
    Proc,
    Var,
    Field,
    /// Top-level `lemma` names (story 07). Unlike [`NameKind::Proc`]/`Var`,
    /// an EasyCrypt lemma name has no lowercase-start requirement (verified
    /// against `r2026.06-12-g7e192dd`: `Hybrid0_Hybrid1_equiv` compiles as
    /// spelled) — mangling still escapes a keyword collision or a
    /// digit-leading name, but never force-prefixes on uppercase start the
    /// way `Var`/`Op`/etc. do.
    Lemma,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum NameError {
    #[error(
        "{kind:?} names `{a}` and `{b}` both mangle to `{mangled}`"
    )]
    Collision {
        kind: NameKind,
        a: String,
        b: String,
        mangled: String,
    },
}

/// Per-namespace mangled-name bookkeeping, so that repeat calls with the same
/// raw name are idempotent and distinct raw names that collide are caught.
#[derive(Debug, Default)]
pub struct Names {
    // mangled name -> the raw name that produced it, per namespace.
    seen: HashMap<NameKind, HashMap<String, String>>,
}

impl Names {
    pub fn new() -> Self {
        Self::default()
    }

    /// Mangle `raw` into a legal EasyCrypt identifier for `kind`, applying the
    /// rules in order:
    ///
    /// 1. Replace `-` with `_` (SMT-derived names such as
    ///    `keys-computed-correctly`).
    /// 2. For [`NameKind::Module`] / [`NameKind::ModuleType`]: uppercase the
    ///    first letter; prefix `M_` if it starts with a digit or `_`.
    /// 3. For every other kind: if the name starts with an uppercase letter,
    ///    or is an EasyCrypt keyword, prefix `d_`. A multi-character name
    ///    that merely *starts* with `_` (`_U`) is legal in EasyCrypt and is
    ///    left alone; a *bare* `_` (Domino's own discarded-binding
    ///    identifier) is EasyCrypt's wildcard pattern, not a legal bound
    ///    name, and gets the same `d_` prefix.
    /// 4. The `ec_` prefix is reserved for the exporter's own generated
    ///    names; a Domino identifier that already starts with `ec_` gets a
    ///    `d_` prefix too.
    /// 5. Two different raw names mangling to the same EasyCrypt name in the
    ///    same namespace is a hard [`NameError::Collision`], never a silent
    ///    rename.
    pub fn mangle(&mut self, kind: NameKind, raw: &str) -> Result<String, NameError> {
        let mangled = mangle_name(kind, raw);

        let namespace = self.seen.entry(kind).or_default();
        match namespace.get(&mangled) {
            Some(existing) if existing == raw => Ok(mangled),
            Some(existing) => Err(NameError::Collision {
                kind,
                a: existing.clone(),
                b: raw.to_string(),
                mangled,
            }),
            None => {
                namespace.insert(mangled.clone(), raw.to_string());
                Ok(mangled)
            }
        }
    }
}

fn mangle_name(kind: NameKind, raw: &str) -> String {
    let replaced = raw.replace('-', "_");

    match kind {
        NameKind::Module | NameKind::ModuleType => {
            let mut chars = replaced.chars();
            let uppercased = match chars.next() {
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
                None => String::new(),
            };
            let starts_with_digit_or_underscore = uppercased
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_digit() || c == '_');
            if starts_with_digit_or_underscore {
                format!("M_{uppercased}")
            } else {
                uppercased
            }
        }
        NameKind::Lemma => {
            let starts_with_digit = replaced.chars().next().is_some_and(|c| c.is_ascii_digit());
            let needs_prefix = starts_with_digit
                || is_keyword(&replaced)
                || replaced.starts_with("ec_")
                || replaced == "_";
            if needs_prefix {
                format!("d_{replaced}")
            } else {
                replaced
            }
        }
        _ => {
            let starts_uppercase = replaced.chars().next().is_some_and(|c| c.is_uppercase());
            // A *bare* `_` is EasyCrypt's wildcard/discard pattern, not a
            // legal bound identifier (`var _ : int;` is a parse error,
            // verified against `r2026.06-12-g7e192dd`) — unlike a
            // multi-character name that merely *starts* with `_`
            // (`_U`, left alone below), which is fine. Domino itself uses a
            // bare `_` as a genuine identifier for a discarded
            // tuple-pattern binding (`kem-dem-cca-ssp`'s own `Scheme_PKE`
            // package hits this for real, not just hypothetically), so
            // export must escape it rather than assume every leading-`_`
            // name is already legal.
            let is_bare_underscore = replaced == "_";
            let needs_prefix = starts_uppercase
                || is_keyword(&replaced)
                || replaced.starts_with("ec_")
                || is_bare_underscore;
            if needs_prefix {
                format!("d_{replaced}")
            } else {
                replaced
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keywords_are_sorted() {
        let mut sorted = KEYWORDS.to_vec();
        sorted.sort_unstable();
        assert_eq!(KEYWORDS, sorted.as_slice());
    }

    #[test]
    fn mangle_uppercase_var() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Proc, "NewKey").unwrap(), "d_NewKey");
        assert_eq!(names.mangle(NameKind::Var, "LTK").unwrap(), "d_LTK");
    }

    #[test]
    fn mangle_keywords() {
        let mut names = Names::new();
        assert_eq!(
            names.mangle(NameKind::Op, "return").unwrap(),
            "d_return"
        );
        assert_eq!(names.mangle(NameKind::Var, "res").unwrap(), "d_res");
    }

    #[test]
    fn mangle_leading_underscore_is_left_alone() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Var, "_U").unwrap(), "_U");
    }

    #[test]
    fn mangle_bare_underscore_is_escaped() {
        // `var _ : int;` is a parse error in EasyCrypt (`_` is the
        // wildcard/discard pattern, not a legal bound name) — verified
        // against `r2026.06-12-g7e192dd`, and hit for real by
        // `kem-dem-cca-ssp`'s `Scheme_PKE` package.
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Var, "_").unwrap(), "d__");
    }

    #[test]
    fn mangle_lowercase_passes_through() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Var, "state").unwrap(), "state");
    }

    #[test]
    fn mangle_dash_to_underscore() {
        let mut names = Names::new();
        assert_eq!(
            names.mangle(NameKind::Op, "keys-computed-correctly").unwrap(),
            "keys_computed_correctly"
        );
    }

    #[test]
    fn mangle_ec_prefix_is_reserved() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Var, "ec_foo").unwrap(), "d_ec_foo");
    }

    #[test]
    fn mangle_module_uppercases_first_letter() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Module, "fwd").unwrap(), "Fwd");
    }

    #[test]
    fn mangle_module_digit_start_gets_prefix() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Module, "1inst").unwrap(), "M_1inst");
    }

    #[test]
    fn mangle_same_raw_name_twice_is_idempotent() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Var, "H").unwrap(), "d_H");
        assert_eq!(names.mangle(NameKind::Var, "H").unwrap(), "d_H");
    }

    #[test]
    fn mangle_collision_is_a_hard_error() {
        let mut names = Names::new();
        names.mangle(NameKind::Var, "H").unwrap();
        let err = names.mangle(NameKind::Var, "d_H").unwrap_err();
        assert_eq!(
            err,
            NameError::Collision {
                kind: NameKind::Var,
                a: "H".to_string(),
                b: "d_H".to_string(),
                mangled: "d_H".to_string(),
            }
        );
    }

    #[test]
    fn mangle_lemma_does_not_prefix_uppercase_start() {
        let mut names = Names::new();
        assert_eq!(
            names.mangle(NameKind::Lemma, "Hybrid0_Hybrid1_equiv").unwrap(),
            "Hybrid0_Hybrid1_equiv"
        );
    }

    #[test]
    fn mangle_lemma_still_escapes_keywords_and_digit_start() {
        let mut names = Names::new();
        assert_eq!(names.mangle(NameKind::Lemma, "for").unwrap(), "d_for");
        assert_eq!(names.mangle(NameKind::Lemma, "1equiv").unwrap(), "d_1equiv");
    }

    #[test]
    fn mangle_collision_is_scoped_to_namespace() {
        let mut names = Names::new();
        names.mangle(NameKind::Var, "H").unwrap();
        // Same raw name in a different namespace does not collide.
        assert_eq!(names.mangle(NameKind::Proc, "H").unwrap(), "d_H");
    }
}
