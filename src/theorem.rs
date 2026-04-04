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

        PackageInstance {
            pkg,
            params: new_params,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClaimType {
    Lemma,
    Relation,
    Invariant,
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
}

impl Claim {
    pub fn from_tuple(data: (String, Vec<String>)) -> Self {
        let (name, dependencies) = data;
        let ty = ClaimType::guess_from_name(&name);

        Self {
            name,
            ty,
            dependencies,
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
