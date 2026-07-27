// SPDX-License-Identifier: MIT OR Apache-2.0

//! Captures, per claim, the verbatim Domino macro source (`define-lemma` /
//! `define-state-relation` forms) from a hand-written `*.smt2` invariant
//! file, together with a structural classification of whether the claim's
//! body can see anything beyond the two "old" game states.
//!
//! This is intentionally decoupled from [`crate::gamehops::equivalence::smtrewrite`],
//! which rewrites the very same macros into solver-facing `define-fun`s: that
//! pipeline is proof-critical and discards spans/raw text as it goes, so
//! rather than entangle the two, this walks the raw macro AST a second time,
//! purely for documentation/export purposes (e.g. the HTML lemma-tree
//! viewer).

use std::collections::BTreeMap;

use crate::util::smtparser::{Result, SmtParser};
use crate::writers::smt::exprs::SmtExpr;

/// Which macro form actually defined a claim -- ground truth, unlike
/// [`crate::theorem::ClaimType::guess_from_name`], which only guesses from
/// the claim's name and is fooled by the common `relation-lemma-...` naming
/// convention (a lemma *about* a relation, not a `define-state-relation`
/// itself).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimKind {
    Lemma,
    StateRelation,
    /// A plain `define-fun` helper (e.g. `kem-correctness`) rather than a
    /// claim in its own right -- captured so that a lemma/relation calling
    /// it can show the helper's own definition alongside it (see
    /// [`crate::writers::html`]'s "referenced definitions" panel section).
    Function,
}

/// What we know about one `define-lemma`/`define-state-relation` claim from
/// the raw invariant source, independent of what the theorem's `lemmas {}`
/// block says about it.
#[derive(Debug, Clone)]
pub struct ClaimSource {
    pub kind: ClaimKind,
    /// The verbatim `(define-lemma ...)`/`(define-state-relation ...)` form,
    /// exactly as written in the invariant file (whitespace and all).
    pub domino_source: String,
    /// `true` if the claim's body refers to the oracle's return value
    /// (`return-left`/`return-right`, which bundle both the new/post-call
    /// game state and the oracle's output) or to any of the oracle's own
    /// call arguments; `false` if it only ever refers to the two old/pre-call
    /// game states. Always `false` for `define-state-relation`, which only
    /// ever binds the two old states.
    pub depends_on_new_state: bool,
    /// A readable-not-compileable EasyCrypt-flavored translation of just the
    /// claim's SMT boolean expression (not the surrounding Domino macro
    /// syntax) -- see [`crate::writers::easycrypt`].
    pub easycrypt_source: String,
}

fn arg_name(expr: &SmtExpr) -> Option<&str> {
    match expr {
        SmtExpr::Atom(name) => Some(name.as_str()),
        SmtExpr::List(items) => match items.first() {
            Some(SmtExpr::Atom(name)) => Some(name.as_str()),
            _ => None,
        },
        SmtExpr::Comment(_) => None,
    }
}

/// Whether `body` contains an atom that *is* `binder`, or that accesses one
/// of its dotted fields (e.g. body atom `return-left.value` references
/// binder `return-left`).
fn references_binder(body: &SmtExpr, binder: &str) -> bool {
    match body {
        SmtExpr::Atom(atom) => atom == binder || atom.starts_with(&format!("{binder}.")),
        SmtExpr::List(items) => items.iter().any(|item| references_binder(item, binder)),
        SmtExpr::Comment(_) => false,
    }
}

#[derive(Default)]
struct ClaimSourceCollector {
    sources: BTreeMap<String, ClaimSource>,
}

impl SmtParser<SmtExpr> for ClaimSourceCollector {
    fn handle_atom(&mut self, content: &str) -> Result<SmtExpr> {
        Ok(SmtExpr::Atom(content.to_string()))
    }

    fn handle_list(&mut self, content: Vec<SmtExpr>) -> Result<SmtExpr> {
        Ok(SmtExpr::List(content))
    }

    fn handle_sexp(&mut self, _parsed: SmtExpr) -> Result<()> {
        // We only care about the side effect of the handle_define_* overrides
        // below; the reconstructed top-level forms aren't needed here.
        Ok(())
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
        raw: &str,
    ) -> Result<SmtExpr> {
        self.sources.insert(
            funname.to_string(),
            ClaimSource {
                kind: ClaimKind::StateRelation,
                domino_source: raw.to_string(),
                // `define-state-relation` only ever binds the two old game
                // states -- there is no return value or oracle argument to
                // depend on structurally.
                depends_on_new_state: false,
                easycrypt_source: crate::writers::easycrypt::translate_term(&body),
            },
        );

        let funname_expr = self.handle_atom(funname)?;
        let args_expr = self.handle_list(args)?;
        let defun = self.handle_atom("define-state-relation")?;
        self.handle_list(vec![defun, funname_expr, args_expr, body])
    }

    fn handle_define_lemma(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
        raw: &str,
    ) -> Result<SmtExpr> {
        // Positional convention enforced by `smtrewrite::handle_define_lemma`:
        // (old-left old-right return-left return-right <oracle args...>).
        // Everything from position 2 onward -- the two return bindings
        // (which bundle new state + output) and any oracle-call arguments --
        // counts as "beyond old state" if the body ever refers to it.
        let binders_beyond_old_state: Vec<&str> =
            args.iter().skip(2).filter_map(arg_name).collect();
        let depends_on_new_state = binders_beyond_old_state
            .iter()
            .any(|binder| references_binder(&body, binder));

        self.sources.insert(
            funname.to_string(),
            ClaimSource {
                kind: ClaimKind::Lemma,
                domino_source: raw.to_string(),
                depends_on_new_state,
                easycrypt_source: crate::writers::easycrypt::translate_term(&body),
            },
        );

        let funname_expr = self.handle_atom(funname)?;
        let args_expr = self.handle_list(args)?;
        let defun = self.handle_atom("define-lemma")?;
        self.handle_list(vec![defun, funname_expr, args_expr, body])
    }

    /// Plain `define-fun` helpers (e.g. `kem-correctness`) aren't claims,
    /// but a lemma/relation that calls one is much easier to review with the
    /// helper's own definition shown alongside it. The shared `SmtParser`
    /// trait doesn't thread a raw source span through this particular
    /// handler (only the two macro forms above needed that), so this
    /// re-renders the definition from its parsed parts via `SmtExpr`'s
    /// existing `Display` impl instead -- structurally faithful, just not
    /// byte-identical to the original formatting/comments.
    fn handle_definefun(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        ty: &str,
        body: SmtExpr,
    ) -> Result<SmtExpr> {
        let rendered = SmtExpr::List(vec![
            SmtExpr::Atom("define-fun".to_string()),
            SmtExpr::Atom(funname.to_string()),
            SmtExpr::List(args.clone()),
            SmtExpr::Atom(ty.to_string()),
            body.clone(),
        ]);

        self.sources.insert(
            funname.to_string(),
            ClaimSource {
                kind: ClaimKind::Function,
                domino_source: rendered.to_string(),
                depends_on_new_state: false,
                easycrypt_source: crate::writers::easycrypt::translate_term(&body),
            },
        );

        let funname_expr = self.handle_atom(funname)?;
        let args_expr = self.handle_list(args)?;
        let ty_expr = self.handle_atom(ty)?;
        let defun = self.handle_atom("define-fun")?;
        self.handle_list(vec![defun, funname_expr, args_expr, ty_expr, body])
    }
}

/// Best-effort extraction of [`ClaimSource`] for every `define-lemma`/
/// `define-state-relation` form in `content`. Returns an empty map if the
/// file fails to parse (callers that need to surface such errors should get
/// them from the main solver-facing rewrite pass instead, which runs the
/// same grammar over the same files).
pub fn collect_claim_sources(content: &str) -> BTreeMap<String, ClaimSource> {
    let mut collector = ClaimSourceCollector::default();
    if collector.parse_sexps(content).is_err() {
        return BTreeMap::new();
    }
    collector.sources
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn state_relation_is_always_old_state_only() {
        let content = r#"
            (define-state-relation invariant
                (left-game right-game)
                (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st))
        "#;
        let sources = collect_claim_sources(content);
        let src = sources.get("invariant").expect("claim should be captured");
        assert!(!src.depends_on_new_state);
        assert!(src.domino_source.starts_with("(define-state-relation"));
    }

    #[test]
    fn lemma_referencing_only_old_state_is_old_state_only() {
        let content = r#"
            (define-lemma <relation-lemma-foo-A-B>
                (old-state-left old-state-right return-left return-right)
                (= old-state-left.Pkg.x old-state-right.Pkg.x))
        "#;
        let sources = collect_claim_sources(content);
        let src = sources
            .get("<relation-lemma-foo-A-B>")
            .expect("claim should be captured");
        assert!(!src.depends_on_new_state);
    }

    #[test]
    fn lemma_referencing_return_value_depends_on_new_state() {
        let content = r#"
            (define-lemma <relation-lemma-foo-A-B>
                (old-state-left old-state-right return-left return-right)
                (= return-left.value return-right.value))
        "#;
        let sources = collect_claim_sources(content);
        let src = sources
            .get("<relation-lemma-foo-A-B>")
            .expect("claim should be captured");
        assert!(src.depends_on_new_state);
        assert_eq!(
            src.easycrypt_source,
            "return-left.value = return-right.value"
        );
    }

    #[test]
    fn lemma_referencing_oracle_argument_depends_on_new_state() {
        let content = r#"
            (define-lemma <relation-case-A-B>
                (old-state-left old-state-right return-left return-right (i Int))
                (< i 10))
        "#;
        let sources = collect_claim_sources(content);
        let src = sources
            .get("<relation-case-A-B>")
            .expect("claim should be captured");
        assert!(src.depends_on_new_state);
    }
}
