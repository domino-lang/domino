// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt;

use miette::SourceSpan;

use crate::statement::CodeBlock;
use crate::types::Type;

pub use crate::packageinstance::PackageInstance;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct OracleSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub ty: Type,
}

impl OracleSig {
    pub(crate) fn types_match(&self, other: &Self) -> bool {
        self.ty.types_match(&other.ty)
            && self.args.len() == other.args.len()
            && self
                .args
                .iter()
                .zip(&other.args)
                .all(|((_, l), (_, r))| l.types_match(r))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OracleDef {
    pub sig: OracleSig,
    pub code: CodeBlock,
    pub file_pos: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Package {
    pub name: String,
    pub types: Vec<String>,
    pub params: Vec<(String, Type, SourceSpan)>,
    pub state: Vec<(String, Type, SourceSpan)>,
    pub oracles: Vec<OracleDef>,
    pub imports: Vec<(OracleSig, SourceSpan)>,

    pub file_name: String,
    pub file_contents: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge {
    from: usize,
    to: usize,
    sig: OracleSig,
}

impl Edge {
    pub fn new(from: usize, to: usize, sig: OracleSig) -> Self {
        Self { from, to, sig }
    }

    pub fn from(&self) -> usize {
        self.from
    }

    pub fn to(&self) -> usize {
        self.to
    }

    pub fn sig(&self) -> &OracleSig {
        &self.sig
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Export {
    to: usize,
    sig: OracleSig,
}

impl Export {
    pub fn new(to: usize, sig: OracleSig) -> Self {
        Self { to, sig }
    }
    pub fn to(&self) -> usize {
        self.to
    }

    pub fn sig(&self) -> &OracleSig {
        &self.sig
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Composition {
    pub pkgs: Vec<PackageInstance>,
    pub edges: Vec<Edge>, // (from, to, oraclesig)
    // TODO: how do we deal with the case where we have
    // e.g. multiple key packages that we Set into?
    // Idea: Add a name to this tuple that is used by
    // the invoking package
    // contemplation: globally unique oracle identifiers vs
    // multiple shades of local uniqueness
    pub exports: Vec<Export>,
    pub name: String,
    pub consts: Vec<(String, Type)>,
}

impl Composition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        self.exports
            .iter()
            .map(|export| export.sig().clone())
            .collect()
    }

    /// Topologically sorts the package instances in the game, such that rightmost games (i.e.
    /// those who don't import oracles themselves) come first.
    /// We need to do this because when defining the oracle code functions, the called functions
    /// need to be defined by the time we call them.
    pub fn ordered_pkgs_idx(&self) -> Vec<usize> {
        let mut result = Vec::new();
        let mut added_pkgs = vec![false; self.pkgs.len()];

        while result.len() < self.pkgs.len() {
            // one flag per package instance.
            // `true` means its dependencies are satisfied (i.e. all the oracles it imports have
            // already been added to `result`).
            // `false` means that the package instance imports an oracle that is wired up with a
            // package instance that hasn't been added to result yet.
            let candidates: Vec<_> = self
                .pkgs
                .iter()
                .enumerate()
                .map(|(pkg_inst_offs, _)| {
                    // whether all edges that originate in the current package instance point to
                    // package instances that have already been added
                    self.edges
                        .iter()
                        .filter(|edge| pkg_inst_offs == edge.from())
                        .all(|edge| added_pkgs[edge.to()])
                })
                .collect();

            let mut made_progress = false;

            for i in 0..self.pkgs.len() {
                if !added_pkgs[i] && candidates[i] {
                    result.push(i);
                    added_pkgs[i] = true;
                    made_progress = true;
                }
            }

            // this can't happen in acyclig graphs, which is what we are delaing with here
            assert!(
                made_progress,
                "error topologically sorting the package instance in the game"
            );
        }
        result
    }
}

impl Composition {
    #[allow(unused_mut)]
    pub fn map_pkg_inst<E, F>(&self, mut f: F) -> Result<Composition, E>
    where
        F: FnMut(&PackageInstance) -> Result<PackageInstance, E>,
    {
        Ok(Composition {
            pkgs: {
                let res: Result<Vec<_>, E> = self.pkgs.iter().map(f).collect();
                res?
            },
            ..self.clone()
        })
    }

    pub fn map_oracle<E>(
        &self,
        f: &mut impl FnMut(&OracleDef) -> Result<OracleDef, E>,
    ) -> Result<Composition, E> {
        self.map_pkg_inst(|pkg_inst| {
            Ok(PackageInstance {
                pkg: pkg_inst.pkg.map_oracle(f)?,
                ..pkg_inst.clone()
            })
        })
    }
}

impl Package {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn map_oracle<E>(
        &self,
        f: &mut impl FnMut(&OracleDef) -> Result<OracleDef, E>,
    ) -> Result<Package, E> {
        Ok(Package {
            oracles: {
                let res: Result<Vec<_>, E> = self.oracles.iter().map(f).collect();
                res?
            },
            ..self.clone()
        })
    }
}

impl fmt::Display for OracleSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Use `self.number` to refer to each positional data point.
        write!(
            f,
            "{}({}) -> {}",
            self.name,
            self.args
                .iter()
                .map(|(name, ty)| format!("{name}: {ty:?}"))
                .collect::<Vec<_>>()
                .join(", "),
            self.ty
        )
    }
}
