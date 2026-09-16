// SPDX-License-Identifier: MIT OR Apache-2.0

//! EasyCrypt export: an AST that models EasyCrypt syntax
//! ([`ast`]), a total renderer from that AST to text ([`render`]), and
//! deterministic identifier mangling ([`names`]).
//!
//! Starting with [`types`] and [`typesfile`], later stories in the
//! `easycrypt` export epic translate Domino into this AST.

pub mod ast;
pub mod names;
pub mod package;
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
        if !easycrypt_available() {
            eprintln!("`easycrypt` not on PATH, skipping compile check");
            return;
        }
        let output = Command::new("easycrypt")
            .args(["compile", "-I", dir, file])
            .output()
            .expect("failed to run easycrypt compile");
        assert!(
            output.status.success(),
            "easycrypt compile failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

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
}
