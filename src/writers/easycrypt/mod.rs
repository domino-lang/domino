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
pub mod lower;
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

    /// The transform pipeline (`EasyCryptTransform`, run once per exported
    /// theorem before any translation) failed. The only way a
    /// parser-accepted project can hit this is a sample reachable through a
    /// loop `loopunroll` could not unroll — see
    /// [`EquivalenceTransformError`]. A surviving loop *without* a sample is
    /// reported as [`EcExportError::UnsupportedStatement`] instead (see the
    /// `From` impl below).
    #[error(transparent)]
    #[diagnostic(transparent)]
    Transform(EquivalenceTransformError),

    /// Inlining an oracle for the debugger listing (story 08,
    /// [`lower::inline_oracle_ec`]) failed the same way the Domino listing
    /// would: the oracle is not exported, a callee is missing, or the
    /// composition is recursive.
    #[error(transparent)]
    #[diagnostic(transparent)]
    Inline(#[from] crate::debug::ir::InlineError),
}

impl From<EquivalenceTransformError> for EcExportError {
    /// `easycryptify` rejects a surviving `for` loop; that is the same hard
    /// error the writer itself raised for it before story 16, just raised
    /// earlier, so it keeps its shape and its span.
    fn from(err: EquivalenceTransformError) -> Self {
        match err {
            EquivalenceTransformError::EasyCryptUnsupportedLoop(e) => e.into(),
            other => EcExportError::Transform(other),
        }
    }
}

impl From<crate::transforms::easycryptify::EasyCryptifyError> for EcExportError {
    fn from(err: crate::transforms::easycryptify::EasyCryptifyError) -> Self {
        EquivalenceTransformError::from(err).into()
    }
}

impl From<crate::transforms::easycryptify::UnsupportedLoopError> for EcExportError {
    fn from(err: crate::transforms::easycryptify::UnsupportedLoopError) -> Self {
        EcExportError::UnsupportedStatement {
            construct: crate::transforms::easycryptify::UNSUPPORTED_FOR,
            span: err.span,
        }
    }
}
