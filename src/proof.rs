use crate::{
    expressions::Expression,
    gamehops::{
        equivalence::Equivalence,
        reduction::{Assumption, Reduction},
    },
    identifier::game_ident::GameConstIdentifier,
    package::{Composition, Package},
    packageinstance::instantiate::InstantiationContext,
    types::Type,
};

use crate::impl_Named;

////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub(crate) struct GameInstance {
    pub(crate) name: String,
    pub(crate) game: Composition,
    pub(crate) types: Vec<(String, Type)>,
    pub(crate) consts: Vec<(GameConstIdentifier, Expression)>,
}

impl_Named!(GameInstance);

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

        let new_split_oracles = pkg_inst
            .pkg
            .split_oracles
            .iter()
            .map(|split_oracle_def| inst_ctx.rewrite_split_oracle_def(split_oracle_def.clone()))
            .collect();

        let pkg = Package {
            oracles: new_oracles,
            split_oracles: new_split_oracles,
            ..pkg_inst.pkg.clone()
        };

        for (_, expr) in &mut pkg_inst.params {
            *expr = inst_ctx.rewrite_expression(expr)
        }

        for index in &mut pkg_inst.multi_instance_indices.indices {
            *index = inst_ctx.rewrite_expression(index);
        }

        PackageInstance { pkg, ..pkg_inst }
    }
}

impl GameInstance {
    pub(crate) fn new(
        game_inst_name: String,
        proof_name: String,
        game: Composition,
        types: Vec<(String, Type)>,
        params: Vec<(GameConstIdentifier, Expression)>,
    ) -> GameInstance {
        let inst_ctx: InstantiationContext = InstantiationContext::new_game_instantiation_context(
            &game_inst_name,
            &proof_name,
            &params,
            &types,
        );

        let new_pkg_instances = game
            .pkgs
            .iter()
            .map(|pkg_inst| -> crate::package::PackageInstance {
                instantiate::rewrite_pkg_inst(inst_ctx, pkg_inst)
            })
            .collect();

        let game = Composition {
            name: game.name.clone(),
            pkgs: new_pkg_instances,

            ..game
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

    pub(crate) fn types(&self) -> &[(String, Type)] {
        &self.types
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
    pub(crate) tipe: ClaimType,
    pub(crate) dependencies: Vec<String>,
}

impl Claim {
    pub fn from_tuple(data: (String, Vec<String>)) -> Self {
        let (name, dependencies) = data;
        let tipe = ClaimType::guess_from_name(&name);

        Self {
            name,
            tipe,
            dependencies,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn tipe(&self) -> ClaimType {
        self.tipe
    }

    pub fn dependencies(&self) -> &[String] {
        &self.dependencies
    }
}

impl crate::util::resolver::Named for Claim {
    fn as_name(&self) -> &str {
        self.name()
    }
}

// TODO: add a HybridArgument variant
#[derive(Debug, Clone)]
pub enum GameHop {
    Reduction(Reduction),
    Equivalence(Equivalence),
}

impl GameHop {
    /// Returns `true` if the game hop is [`Reduction`].
    ///
    /// [`Reduction`]: GameHop::Reduction
    #[must_use]
    pub fn is_reduction(&self) -> bool {
        matches!(self, Self::Reduction(..))
    }

    /// Returns `true` if the game hop is [`Equivalence`].
    ///
    /// [`Equivalence`]: GameHop::Equivalence
    #[must_use]
    pub fn is_equivalence(&self) -> bool {
        matches!(self, Self::Equivalence(..))
    }

    pub fn as_reduction(&self) -> Option<&Reduction> {
        if let Self::Reduction(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_equivalence(&self) -> Option<&Equivalence> {
        if let Self::Equivalence(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub(crate) name: String,
    pub(crate) consts: Vec<(String, Type)>,
    pub(crate) instances: Vec<GameInstance>,
    pub(crate) assumptions: Vec<Assumption>,
    pub(crate) game_hops: Vec<GameHop>,
    pub(crate) pkgs: Vec<Package>,
}

impl Proof {
    pub(crate) fn new(
        name: String,
        consts: Vec<(String, Type)>,
        instances: Vec<GameInstance>,
        assumptions: Vec<Assumption>,
        game_hops: Vec<GameHop>,
        pkgs: Vec<Package>,
    ) -> Proof {
        Proof {
            name,
            consts,
            instances,
            assumptions,
            game_hops,
            pkgs,
        }
    }

    pub(crate) fn with_new_instances(&self, instances: Vec<GameInstance>) -> Proof {
        Proof {
            instances,
            ..self.clone()
        }
    }

    pub(crate) fn as_name(&self) -> &str {
        &self.name
    }

    pub(crate) fn game_hops(&self) -> &[GameHop] {
        &self.game_hops
    }

    pub(crate) fn instances(&self) -> &[GameInstance] {
        &self.instances
    }

    pub(crate) fn assumptions(&self) -> &[Assumption] {
        &self.assumptions
    }

    pub(crate) fn packages(&self) -> &[Package] {
        &self.pkgs
    }

    pub(crate) fn find_game_instance(&self, game_inst_name: &str) -> Option<&GameInstance> {
        self.instances
            .iter()
            .find(|inst| inst.name == game_inst_name)
    }
}
