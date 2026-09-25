// SPDX-License-Identifier: MIT OR Apache-2.0

//! Where a debug run writes its files (story 19 §4.6).
//!
//! The two Domino strategies write into the **same** directory and coexist, so every
//! artifact that both would write carries its strategy in its name:
//!
//! ```text
//! <oracle>/!all-claims!/
//!     inlined.txt                 shared: both lower the same Domino listing
//!     sequential_viewer.html   sequential_trace.json   sequential_summary.txt
//!     lockstep_viewer.html     lockstep_trace.json     lockstep_summary.txt
//!     sequential/  { smt/, models/, transcript.smt2 }
//!     lockstep/    { smt/, models/, transcript.smt2 }
//! ```
//!
//! The EasyCrypt listing has only one strategy, so its directory keeps the plain names
//! (`index.html`, `trace.json`, `summary.txt`, `smt/`, `models/`): nothing to disambiguate, and
//! `--tactics` keeps resolving `index.html` by relative href.

use std::path::{Path, PathBuf};

/// The directory a Domino all-claim run writes to, in place of `<claim>`.
pub const ALL_CLAIMS_DIR: &str = "!all-claims!";

/// The `_build` subdirectory the Domino listing's runs go under.
pub const DOMINO_DEBUG_DIR: &str = "_build/debug/domino";

/// How the artifact names of one run are spelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Layout {
    /// `index.html`, `trace.json`, `summary.txt`, `smt/`, `models/`.
    Plain,
    /// `<strategy>_viewer.html`, `<strategy>_trace.json`, `<strategy>_summary.txt`,
    /// `<strategy>/smt/`, `<strategy>/models/`.
    Strategy(&'static str),
}

impl Layout {
    /// The HTML viewer.
    pub fn viewer(self) -> String {
        match self {
            Layout::Plain => "index.html".to_string(),
            Layout::Strategy(s) => format!("{s}_viewer.html"),
        }
    }

    /// The JSON trace.
    pub fn trace(self) -> String {
        match self {
            Layout::Plain => "trace.json".to_string(),
            Layout::Strategy(s) => format!("{s}_trace.json"),
        }
    }

    /// The text summary.
    pub fn summary(self) -> String {
        match self {
            Layout::Plain => "summary.txt".to_string(),
            Layout::Strategy(s) => format!("{s}_summary.txt"),
        }
    }

    /// `name` (a file or directory that only this strategy writes) relative to the run's
    /// output directory: `smt`, `models/J1.smt2`, `transcript.smt2`.
    pub fn rel(self, name: &str) -> String {
        match self {
            Layout::Plain => name.to_string(),
            Layout::Strategy(s) => format!("{s}/{name}"),
        }
    }

    /// [`rel`](Self::rel), resolved under `out_dir`.
    pub fn path(self, out_dir: &Path, name: &str) -> PathBuf {
        out_dir.join(self.rel(name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_keeps_the_names_the_easycrypt_directory_has_always_had() {
        let l = Layout::Plain;
        assert_eq!(l.viewer(), "index.html");
        assert_eq!(l.trace(), "trace.json");
        assert_eq!(l.summary(), "summary.txt");
        assert_eq!(l.rel("models/J1.smt2"), "models/J1.smt2");
    }

    #[test]
    fn a_strategy_prefixes_every_name_it_owns() {
        let l = Layout::Strategy("lockstep");
        assert_eq!(l.viewer(), "lockstep_viewer.html");
        assert_eq!(l.trace(), "lockstep_trace.json");
        assert_eq!(l.summary(), "lockstep_summary.txt");
        assert_eq!(l.rel("smt"), "lockstep/smt");
        assert_eq!(
            l.path(Path::new("/o"), "transcript.smt2"),
            Path::new("/o/lockstep/transcript.smt2")
        );
    }
}
