// SPDX-License-Identifier: MIT OR Apache-2.0

//! EasyCrypt export: an AST that models EasyCrypt syntax
//! ([`ast`]), a total renderer from that AST to text ([`render`]), and
//! deterministic identifier mangling ([`names`]).
//!
//! Starting with [`types`] and [`typesfile`], later stories in the
//! `easycrypt` export epic translate Domino into this AST.

pub mod ast;
pub mod export;
pub mod game;
pub mod interfaces;
pub mod invariant;
pub mod names;
pub mod package;
pub mod proof;
pub mod render;
pub mod types;
pub mod typesfile;

#[cfg(test)]
mod tests;

/// Shared by every story's `*_compiles`-style tests, so "shell out to
/// `easycrypt compile`, skipping (not failing) when the binary isn't on
/// `PATH`" (`docs/stories/easycrypt/00-overview.md` §7) is written once.
#[cfg(test)]
pub(crate) mod test_support {
    use std::process::Command;

    fn easycrypt_available() -> bool {
        match Command::new("easycrypt").arg("config").output() {
            Ok(output) => output.status.success(),
            Err(_) => false,
        }
    }

    /// Asserts `easycrypt compile -I <dir> <file>` succeeds, given already
    /// fully-resolved paths. Skips (prints to stderr, doesn't fail) when
    /// `easycrypt` isn't on `PATH`.
    pub(crate) fn assert_compiles(dir: &str, file: &str) {
        assert_compiles_with_paths(&[dir], file);
    }

    /// Like [`assert_compiles`], but with one `-I <dir>` per entry in
    /// `dirs`. Since story 10 flattened `domino easycrypt`'s own output (no
    /// `packages/`/`games/` subdirectories any more — every real export
    /// compiles with a single `-I .`), this is only needed by a test that
    /// deliberately spreads its fixture across two *unrelated* directories
    /// (e.g. `invariant.rs`'s own `hybrid0_hybrid1_invariants_file_compiles`,
    /// which writes its rendered file to a scratch dir but reads `Types.ec`
    /// from a separate `testdata/` fixture dir).
    pub(crate) fn assert_compiles_with_paths(dirs: &[&str], file: &str) {
        let Some(output) = run_compile(dirs, file) else {
            return;
        };
        assert!(
            output.status.success(),
            "easycrypt compile failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_no_unused_memory_warning(&output);
    }

    /// Runs `easycrypt compile` with one `-I` per entry in `dirs`, or
    /// returns `None` (after saying so on stderr) when `easycrypt` isn't on
    /// `PATH`.
    fn run_compile(dirs: &[&str], file: &str) -> Option<std::process::Output> {
        if !easycrypt_available() {
            eprintln!("`easycrypt` not on PATH, skipping compile check");
            return None;
        }
        let mut args = vec!["compile".to_string()];
        for dir in dirs {
            args.push("-I".to_string());
            args.push(dir.to_string());
        }
        args.push(file.to_string());
        Some(
            Command::new("easycrypt")
                .args(&args)
                .output()
                .expect("failed to run easycrypt compile"),
        )
    }

    /// Story 15 §6: EasyCrypt accepts a relational formula whose `{1}`/`{2}`
    /// tag was silently discarded (a lemma binder shadowing a program
    /// variable) and reports it only as `unused memory `&1', while typing
    /// b` — a warning, exit code 0. Treat that warning as a failure, so the
    /// bug can't come back invisibly.
    fn assert_no_unused_memory_warning(output: &std::process::Output) {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !stdout.contains("unused memory") && !stderr.contains("unused memory"),
            "easycrypt compiled with an `unused memory` warning — a relational formula lost \
             its memory tag:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }

    /// Like [`assert_compiles_with_paths`], but for story 07's own
    /// `Eq_*.ec` proof skeletons: tolerates *exactly* the base case's known
    /// `smt(emptyE map_empty)` discharge gap (`docs/stories/easycrypt/
    /// 07-proof-skeleton.md` §6/§4 — "the base case may genuinely fail...
    /// report the goal rather than widening the `smt` call blindly", and a
    /// real `smt(…)` call, not `admit`, is itself the acceptance bar, not
    /// the base case actually discharging).
    ///
    /// **Narrowed by story 13, again by story 15.** Story 13's explicit
    /// `byequiv` relational precondition made the same-composition base case
    /// discharge; story 15 rewrote it as one `arg{side} = …` conjunct per
    /// side, because the per-parameter form was silently voided whenever a
    /// lemma binder shared a `run` parameter's name (`b{1} = b` collapsed to
    /// `b = b`). With that fixed, every `Simple4WHS` proof compiles clean, as
    /// do six of `Full4WHS`'s nine. What still needs this helper —
    /// confirmed failing only at the base case's `smt(emptyE map_empty)`,
    /// `cannot prove goal (strict)` — is `Eq_H0_H1_0.ec`, `Eq_H1_1_H2_0.ec`
    /// and `Eq_H3_1_H4.ec` (`Full4WHS`), and `kem-dem-cca-ssp`'s one hop:
    /// the two sides' game-state records are structurally different (a
    /// `forall &1 &2` induction step loses the tie between the two sides'
    /// `run` arguments that the top-level precondition fixed at `&m`), a
    /// `params_inv`/state-relation gap, not a precondition one. Do not widen
    /// the `smt` call to chase them. Everything else in the file, up to and
    /// including that one tactic, must still succeed, so any *other*
    /// failure (wrong syntax, a bad restriction, a bullet mismatch, …) still
    /// fails this assertion — and so does an `unused memory` warning, which
    /// is how a voided relational precondition shows up.
    pub(crate) fn assert_compiles_or_known_base_case_gap(dirs: &[&str], file: &str) {
        let Some(output) = run_compile(dirs, file) else {
            return;
        };
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Story 15: a base-case failure is tolerated, a voided precondition
        // is not — even in a file that fails for the known reason.
        assert_no_unused_memory_warning(&output);
        if output.status.success() {
            return;
        }
        assert!(
            stdout.contains("cannot prove goal (strict)")
                || stderr.contains("cannot prove goal (strict)"),
            "easycrypt compile failed with something other than the known base-case gap:\n\
             stdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::transforms::theorem_transforms::EquivalenceTransformError;
use names::NameError;

/// A Domino construct that has no EasyCrypt translation, encountered while
/// exporting a theorem. Carries the [`SourceSpan`] of the Domino node that
/// triggered it — see each variant's producing site for where that span
/// comes from, since not every Domino node carries one of its own (notably
/// [`crate::expressions::Expression`] and [`crate::types::Type`] don't;
/// callers thread a span down from the nearest enclosing spanned node).
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
pub enum EcExportError {
    #[error("EasyCrypt export does not support the Domino `{construct}` type")]
    UnsupportedType {
        construct: &'static str,
        #[label("this type has no EasyCrypt translation")]
        span: SourceSpan,
    },

    #[error("EasyCrypt export does not support the Domino `{construct}` expression")]
    UnsupportedExpression {
        construct: &'static str,
        #[label("this expression has no EasyCrypt translation")]
        span: SourceSpan,
    },

    #[error("EasyCrypt export does not support the Domino `{construct}` statement")]
    UnsupportedStatement {
        construct: &'static str,
        #[label("this statement has no EasyCrypt translation")]
        span: SourceSpan,
    },

    #[error("EasyCrypt export does not support package instances with type parameters")]
    PackageTypeParameters {
        #[label("this package instance has a non-empty `types {{ … }}` block")]
        span: SourceSpan,
    },

    #[error(transparent)]
    Name(#[from] NameError),

    #[error(transparent)]
    Invariant(#[from] invariant::InvariantError),

    /// The equivalence transform pipeline (`EquivalenceTransform`, run once
    /// per exported theorem before any translation) failed. The only way a
    /// parser-accepted project can hit this is a sample reachable through a
    /// loop `loopunroll` could not unroll — see
    /// [`EquivalenceTransformError`].
    #[error(transparent)]
    #[diagnostic(transparent)]
    Transform(#[from] EquivalenceTransformError),
}
