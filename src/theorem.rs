// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    gamehops::{
        reduction::{Assumption, Reduction},
        GameHop,
    },
    identifier::game_ident::GameConstIdentifier,
    package::{Composition, Edge, Export, Package},
    packageinstance::{game_inst_type_mapping_vec, instantiate::InstantiationContext},
    proof::Proof,
    types::Type,
};

////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct GameInstance {
    pub(crate) name: String,
    pub(crate) game: Composition,
    pub(crate) types: Vec<(String, Type)>,
    pub(crate) consts: Vec<(GameConstIdentifier, Expression)>,
}

mod instantiate {
    use crate::{
        package::Package,
        packageinstance::{instantiate::InstantiationContext, PackageInstance},
    };

    /*
    *
    *This function looks funny.
    It is doing working during a game-to-gameinstance rewrite,
    but does things for a pacakge-to-package instance rewrite.
    *
    * */
    pub(crate) fn rewrite_pkg_inst(
        inst_ctx: InstantiationContext,
        pkg_inst: &PackageInstance,
    ) -> PackageInstance {
        let mut pkg_inst = pkg_inst.clone();

        let new_oracles = pkg_inst
            .pkg
            .oracles
            .iter()
            .map(|oracle_def| inst_ctx.rewrite_oracle_def(oracle_def.clone()))
            .collect();

        // let new_split_oracles = pkg_inst
        //     .pkg
        //     .split_oracles
        //     .iter()
        //     .map(|split_oracle_def| inst_ctx.rewrite_split_oracle_def(split_oracle_def.clone()))
        //     .collect();

        let new_state = pkg_inst
            .pkg
            .state
            .iter()
            .cloned()
            .map(|(ident, ty, span)| (ident, inst_ctx.rewrite_type(ty), span))
            .collect();

        let new_params = pkg_inst
            .pkg
            .params
            .iter()
            .cloned()
            .map(|(ident, ty, span)| (ident, inst_ctx.rewrite_type(ty), span))
            .collect();

        let pkg = Package {
            oracles: new_oracles,
            state: new_state,
            params: new_params,
            // split_oracles: new_split_oracles,
            ..pkg_inst.pkg.clone()
        };

        for (_, expr) in &mut pkg_inst.params {
            *expr = inst_ctx.rewrite_expression(expr)
        }

        let new_params = pkg_inst
            .params
            .iter()
            .map(|(ident, expr)| {
                (
                    inst_ctx
                        .rewrite_pkg_identifier(
                            crate::identifier::pkg_ident::PackageIdentifier::Const(ident.clone()),
                        )
                        .into_const()
                        .unwrap(),
                    inst_ctx.rewrite_expression(expr),
                )
            })
            .collect();

        let new_types = pkg_inst.types.into_iter().map(|(n,t)| (n, inst_ctx.rewrite_type(t))).collect();
        PackageInstance {
            pkg,
            params: new_params,
            types: new_types,
            ..pkg_inst
        }
    }
}

impl GameInstance {
    pub(crate) fn new(
        game_inst_name: String,
        theorem_name: String,
        game: Composition,
        types: Vec<(String, Type)>,
        params: Vec<(GameConstIdentifier, Expression)>,
    ) -> GameInstance {
        let rewrite_types = game_inst_type_mapping_vec(&types);
        let inst_ctx: InstantiationContext = InstantiationContext::new_game_instantiation_context(
            &game_inst_name,
            &theorem_name,
            &params,
            &rewrite_types,
        );

        let new_pkg_instances = game
            .pkgs
            .iter()
            .map(|pkg_inst| -> crate::package::PackageInstance {
                instantiate::rewrite_pkg_inst(inst_ctx, pkg_inst)
            })
            .collect();

        let resolved_params = game
            .consts
            .iter()
            .map(|(ident, ty)| (ident.clone(), inst_ctx.rewrite_type(ty.clone())))
            .collect();

        let new_edges = game
            .edges
            .into_iter()
            .map(|edge| {
                Edge::new(
                    edge.from(),
                    edge.to(),
                    inst_ctx.rewrite_oracle_sig(edge.sig().clone()),
                    edge.alias().cloned(),
                )
            })
            .collect();

        let new_exports = game
            .exports
            .into_iter()
            .map(|export| {
                Export::new(
                    export.to(),
                    inst_ctx.rewrite_oracle_sig(export.sig().clone()),
                    export.alias().cloned(),
                )
            })
            .collect();

        let game = Composition {
            name: game.name.clone(),
            pkgs: new_pkg_instances,
            consts: resolved_params,
            edges: new_edges,
            exports: new_exports,
            invariants: game.invariants.clone(),

            // XXX: This probably needs rewriting
            type_params: game.type_params,
        };

        GameInstance {
            name: game_inst_name,
            game,
            types,
            consts: params,
        }
    }

    pub(crate) fn with_other_game(&self, game: Composition) -> GameInstance {
        GameInstance {
            game,
            ..self.clone()
        }
    }

    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn game_name(&self) -> &str {
        &self.game.name
    }

    pub(crate) fn game(&self) -> &Composition {
        &self.game
    }
}

/// Name of the (equivalence-wide, not oracle-scoped) claim that the invariant holds on the two
/// game instances' initial states. Used both to construct that claim (`verify_fn.rs`) and to
/// recognize it later (e.g. `domino-verify`'s model rendering).
pub const INITIAL_STATE_CLAIM_NAME: &str = "!initial-state!";

/// Internal SMT function name domino calls to assume the old-state invariant as a dependency of
/// every claim, and to check the induction base case on the initial state. This is deliberately
/// *not* `"invariant"`: no name is special to domino except this one — a `define-state-relation`
/// (or even a raw `define-fun`) named `invariant` is just an ordinary, unremarkable name, since
/// nothing looks for it. Domino always synthesizes this reserved, bracketed name itself as the
/// AND of every `define-state-relation` fragment declared in an oracle's invariant files
/// (`smtrewrite::synthesize_invariant` — `true` if there are none) *unless* the user has already
/// defined something under this exact name themselves (raw or via the macro), in which case that
/// collides with domino's own definition: `EquivalenceContext::load_invariants` warns and uses
/// the user's definition as-is instead of synthesizing one.
pub const DOMINO_INVARIANT_FN_NAME: &str = "<domino-invariant>";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClaimType {
    Lemma,
    Relation,
    Invariant,
    LeftPackageInvariant,
    RightPackageInvariant,
    LeftGameInvariant,
    RightGameInvariant,
    InitialState,
}

impl ClaimType {
    pub fn guess_from_name(name: &str) -> ClaimType {
        if name.starts_with("relation") {
            ClaimType::Relation
        } else if name.starts_with("invariant") {
            ClaimType::Invariant
        } else {
            ClaimType::Lemma
        }
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Ord, Eq)]
pub struct Claim {
    pub(crate) name: String,
    pub(crate) ty: ClaimType,
    pub(crate) dependencies: Vec<String>,
    pub(crate) admitted: bool,
    /// Whether this claim came from an explicit line in the `.ssp` file's `lemmas {}` block, as
    /// opposed to one of the claims domino injects automatically (the `equal-aborts`/
    /// `same-output`/`invariant` defaults, or an auto-generated invariant fragment claim). Used
    /// to decide whether an automatically generated claim should be overridden/dropped.
    pub(crate) user_declared: bool,
    /// From an explicit `with invariants [inv1, inv2]` modifier on this claim's `lemmas {}` line:
    /// restricts what's assumed on the old state, for this claim only, to exactly the named
    /// invariant fragments' conjunction instead of the full `invariant` (the AND of every
    /// fragment). `None` means the usual, unrestricted assumption.
    pub(crate) invariant_scope: Option<Vec<String>>,
}

impl Claim {
    pub fn from_tuple(data: (String, Vec<String>, bool, bool, Option<Vec<String>>)) -> Self {
        let (name, dependencies, admitted, user_declared, invariant_scope) = data;
        let ty = ClaimType::guess_from_name(&name);

        Self {
            name,
            ty,
            dependencies,
            admitted,
            user_declared,
            invariant_scope,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> ClaimType {
        self.ty
    }

    pub fn dependencies(&self) -> &[String] {
        &self.dependencies
    }

    pub fn is_admitted(&self) -> bool {
        self.admitted
    }
}

/// Returns the transitive closure of `root_name`'s dependencies within
/// `tree` (i.e. not just its direct `lemmas { root: [...] }` list, but
/// everything reachable by repeatedly following dependency edges), down to
/// the leaves -- claims with no further known dependencies, whether because
/// they're `admit`ted, proved outright with no hints, or a built-in like
/// `no-abort` that was never given its own `lemmas` entry. Returns `None` if
/// `root_name` isn't a claim in `tree`.
pub fn claim_closure(tree: &[Claim], root_name: &str) -> Option<Vec<Claim>> {
    let by_name: std::collections::BTreeMap<&str, &Claim> =
        tree.iter().map(|claim| (claim.name(), claim)).collect();
    let root = *by_name.get(root_name)?;

    let mut visited = std::collections::BTreeSet::new();
    let mut stack = vec![root];
    let mut closure = Vec::new();

    while let Some(claim) = stack.pop() {
        if !visited.insert(claim.name()) {
            continue;
        }
        closure.push(claim.clone());
        for dep in claim.dependencies() {
            if let Some(dep_claim) = by_name.get(dep.as_str()) {
                stack.push(dep_claim);
            }
        }
    }

    closure.sort_by(|a, b| a.name().cmp(b.name()));
    Some(closure)
}

#[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub enum RandomnessType {
    Custom,
    Simple,
    None,
}

#[derive(Clone, Debug)]
pub struct Theorem<'a> {
    pub name: String,
    pub types: Vec<String>,
    pub consts: Vec<(String, Type)>,
    pub instances: Vec<GameInstance>,
    pub assumptions: Vec<Assumption>,
    pub proofs: Vec<Proof<'a>>,
    pub game_hops: Vec<GameHop<'a>>,
    pub pkgs: Vec<Package>,
}

impl<'a> Theorem<'a> {
    pub(crate) fn with_new_instances(&self, instances: Vec<GameInstance>) -> Theorem<'a> {
        Theorem {
            instances,
            ..self.clone()
        }
    }

    pub(crate) fn reductions(&self) -> impl Iterator<Item = &Reduction<'_>> {
        self.game_hops.iter().filter_map(|hop| {
            if let GameHop::Reduction(red) = hop {
                Some(red)
            } else {
                None
            }
        })
    }

    pub(crate) fn find_game_instance(&self, game_inst_name: &str) -> Option<&GameInstance> {
        self.instances
            .iter()
            .find(|inst| inst.name == game_inst_name)
    }
}
