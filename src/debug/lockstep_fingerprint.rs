// SPDX-License-Identifier: MIT OR Apache-2.0

//! The **fingerprint** of one oracle's joint tree (ADR 0008): a stable hash of everything lockstep
//! execution builds the tree from, so a saved tree can tell when the project has changed under
//! it. Source positions are left out, so moving code around or reformatting it changes
//! nothing; the Domino version is left out too.
//!
//! It has four parts, each hashed on its own so a stale tree can say what changed:
//!
//! - `code`: both sides' inlined EasyCrypt listings of the oracle (what lockstep walks: the
//!   code of every package instance the oracle reaches), with the oracle's signature.
//! - `constants`: both game instances' types and constants.
//! - `randomness`: the oracle's randomness mapping: its kind and the SMT of its conditions.
//! - `invariants`: the SMT of every loaded state relation, invariant and lemma.
//!
//! The hash is FNV-1a over 128 bits: stable across runs and platforms, and no dependency.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::debug::driver::{equivalence_of, DebugError};
use crate::project::Project;
use crate::theorem::{GameInstance, Theorem};
use crate::transforms::theorem_transforms::{EasyCryptTransform, EquivalenceTransform};
use crate::transforms::TheoremTransform;
use crate::writers::easycrypt::lower::inline_oracle_ec;
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::exprs::SmtExpr;

/// The parts, in the order they are hashed and named.
pub const PARTS: [&str; 4] = ["code", "constants", "randomness", "invariants"];

/// What part `part` of [`PARTS`] is, in words (the stale-tree warning).
pub fn describe_part(part: &str) -> &str {
    match part {
        "code" => "the oracle's code",
        "constants" => "the game constants",
        "randomness" => "the randomness mapping",
        "invariants" => "the invariants",
        other => other,
    }
}

/// The fingerprint of one oracle's joint tree: the hash of all parts, and of each.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fingerprint {
    /// Hex of the hash of all parts.
    pub hex: String,
    /// Hex of each part's hash, by name.
    pub parts: BTreeMap<String, String>,
}

impl Fingerprint {
    /// The fingerprint of `oracle`'s joint tree at `proofstep` of `theorem`.
    pub fn of<P: Project>(
        project: &P,
        theorem: &Theorem<'_>,
        proofstep: usize,
        oracle: &str,
    ) -> Result<Fingerprint, DebugError> {
        let eq = equivalence_of(theorem, proofstep)?;
        let sides = [eq.left_name(), eq.right_name()];

        let (theorem_ec, _) = EasyCryptTransform.transform_theorem(theorem)?;
        let mut code = String::new();
        for side in sides {
            let inst = theorem_ec
                .find_game_instance(side)
                .expect("the game instance exists");
            let inlined = inline_oracle_ec(inst, oracle)?;
            let _ = writeln!(
                code,
                "{side} {:?} -> {:?}\n{}",
                inlined.args, inlined.return_type, inlined.listing.text
            );
        }

        let mut constants = String::new();
        for side in sides {
            let inst = theorem
                .find_game_instance(side)
                .expect("the game instance exists");
            constants.push_str(&constants_of(inst));
        }

        let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(theorem)?;
        let mut eqctx = EquivalenceContext::new(eq, &theorem_eq, &auxs_eq);
        eqctx.load_invariants(project)?;
        let randomness = format!(
            "{:?}\n{}{}",
            eq.randomness_by_oracle_name(oracle),
            smt(&eqctx.emit_randomness_mapping_condition(oracle)),
            smt(&eqctx.emit_auto_randomness(oracle))
        );
        let invariants = smt(&eqctx.emit_invariant());

        Ok(Fingerprint::from_parts([
            code, constants, randomness, invariants,
        ]))
    }

    /// The fingerprint of the parts' texts, in the order of [`PARTS`].
    fn from_parts(texts: [String; 4]) -> Fingerprint {
        let parts: BTreeMap<String, String> = PARTS
            .iter()
            .zip(&texts)
            .map(|(name, text)| (name.to_string(), hex(fnv1a(text.as_bytes()))))
            .collect();
        let mut all = String::new();
        for name in PARTS {
            let _ = writeln!(all, "{name}={}", parts[name]);
        }
        Fingerprint {
            hex: hex(fnv1a(all.as_bytes())),
            parts,
        }
    }

    /// The parts that differ from `saved`'s (a saved tree's), in the order of [`PARTS`]. A part
    /// `saved` does not have counts as changed.
    pub fn changed_from(&self, saved: &BTreeMap<String, String>) -> Vec<&'static str> {
        PARTS
            .into_iter()
            .filter(|name| saved.get(*name) != self.parts.get(*name))
            .collect()
    }
}

/// Types and constants of a game instance, without source positions.
fn constants_of(inst: &GameInstance) -> String {
    let mut out = format!("{}\n", inst.name);
    for (name, ty) in &inst.types {
        let _ = writeln!(out, "type {name} = {ty:?}");
    }
    for (id, value) in &inst.consts {
        let _ = writeln!(out, "const {}: {:?} = {value:?}", id.name, id.ty);
    }
    out
}

fn smt(exprs: &[SmtExpr]) -> String {
    let mut out = String::new();
    for e in exprs {
        let _ = writeln!(out, "{e}");
    }
    out
}

/// FNV-1a, 128 bits.
fn fnv1a(bytes: &[u8]) -> u128 {
    const OFFSET: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
    bytes
        .iter()
        .fold(OFFSET, |h, &b| (h ^ u128::from(b)).wrapping_mul(PRIME))
}

fn hex(h: u128) -> String {
    format!("{h:032x}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use std::path::Path;

    const PROJECT: &str = "example-projects/hello-world-oracle-rename-new";
    const ORACLE: &str = "ChangeNameUsefulOracle";

    fn fingerprint(dir: &Path) -> Fingerprint {
        fingerprint_of(dir, ORACLE)
    }

    fn fingerprint_of(dir: &Path, oracle: &str) -> Fingerprint {
        let files = DirectoryFiles::load(dir).unwrap();
        let project = DirectoryProject::load(dir.to_path_buf(), &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        Fingerprint::of(&project, theorem, 0, oracle).unwrap()
    }

    /// A copy of the project with `edit` applied to the file `rel`.
    fn edited(rel: &str, edit: impl Fn(&str) -> String) -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        for sub in ["theorem", "packages", "games"] {
            std::fs::create_dir_all(dir.path().join(sub)).unwrap();
        }
        let src = Path::new(PROJECT);
        for entry in walk(src) {
            let rel = entry.strip_prefix(src).unwrap();
            std::fs::copy(&entry, dir.path().join(rel)).unwrap();
        }
        let path = dir.path().join(rel);
        let text = std::fs::read_to_string(&path).unwrap();
        let changed = edit(&text);
        assert_ne!(changed, text, "the edit changes {rel}");
        std::fs::write(&path, changed).unwrap();
        dir
    }

    fn walk(dir: &Path) -> Vec<std::path::PathBuf> {
        let mut out = Vec::new();
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n != "_build") {
                    out.extend(walk(&path));
                }
            } else {
                out.push(path);
            }
        }
        out
    }

    fn changed(dir: &tempfile::TempDir) -> Vec<&'static str> {
        fingerprint(dir.path()).changed_from(&fingerprint(Path::new(PROJECT)).parts)
    }

    #[test]
    fn the_fingerprint_is_stable_and_ignores_where_code_stands() {
        let a = fingerprint(Path::new(PROJECT));
        assert_eq!(a, fingerprint(Path::new(PROJECT)));
        // the same in every process and build profile: no hash seed, no pointer, no `HashMap`
        // order (a change to the project or to what is hashed changes it, and that is all)
        assert_eq!(a.hex, "68cf6f9107e54870fd9c11217fe6d47f");
        assert_eq!(
            a.parts.keys().collect::<Vec<_>>(),
            ["code", "constants", "invariants", "randomness"]
        );
        // moved down two lines and re-indented: no source position is hashed
        let moved = edited("packages/Rand.pkg.ssp", |t| {
            t.replacen("    state {", "\n\n    state {", 1)
                .replace("        ctr  <- (ctr + 1);", "  ctr <- (ctr + 1);")
        });
        assert_eq!(fingerprint(moved.path()).hex, a.hex);
    }

    #[test]
    fn the_fingerprint_names_the_part_that_changed() {
        let code = edited("packages/Rand.pkg.ssp", |t| {
            t.replace("(ctr + 1)", "(ctr + 2)")
        });
        assert_eq!(changed(&code), vec!["code"]);
        let invariant = edited("theorem/invariant.smt2", |t| {
            t.replace(
                "(= left.rand.ctr right.rand.ctr)",
                "(>= left.rand.ctr right.rand.ctr)",
            )
        });
        assert_eq!(changed(&invariant), vec!["invariants"]);
        let randomness = edited("theorem/proof.ssp", |t| {
            t.replacen("randomness: simple", "randomness: none", 1)
        });
        assert_eq!(changed(&randomness), vec!["randomness"]);
    }

    #[test]
    fn code_the_oracle_does_not_reach_is_not_in_its_fingerprint() {
        // `Fwd` is reached by `ChangeNameUsefulOracle` only
        let fwd = edited("packages/Fwd.pkg.ssp", |t| {
            t.replace("return z;", "return y;")
        });
        assert_eq!(changed(&fwd), vec!["code"]);
        let other = "AnotherUsefulOracle";
        assert_eq!(
            fingerprint_of(fwd.path(), other),
            fingerprint_of(Path::new(PROJECT), other)
        );
        // nor is an oracle of a reached package that this one does not call
        let useless = edited("packages/Rand.pkg.ssp", |t| {
            t.replace("assert (x == 1);", "assert (x == 2);")
        });
        assert_eq!(changed(&useless), Vec::<&str>::new());
    }
}
