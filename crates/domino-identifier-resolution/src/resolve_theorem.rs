use std::collections::HashMap;

use domino_ast::{
    arena::Ref,
    ast_nodes::{identifier, theorem, NodeType},
    source::SourceLocation,
    Arenas, GlobalRefId, GlobalTable, LocationTable, PartialDenseTable,
};

use crate::{
    diag::{self, UndefinedIdentifier},
    resolutions::*,
    resolve_game::GameInfo,
    scope::*,
    util::get_text,
    BuiltinType, BuiltinValue, DeclarationType, PackageInfo,
};

#[derive(Debug, Clone)]
pub struct TheoremInfo {
    pub theorem: Ref<theorem::Theorem>,
    pub name: Ref<identifier::TheoremIdentifier>,
    pub const_params: HashMap<String, Ref<theorem::TheoremConstDecl>>,
    pub instances: HashMap<String, GameInstanceInfo>,
    pub assumptions: HashMap<String, Ref<theorem::AssumptionsItem>>,
}

#[derive(Debug, Clone)]
pub struct GameInstanceInfo {
    pub game_inst: Ref<theorem::InstanceBlock>,
    pub name: Ref<identifier::GameInstanceIdentifier>,
    pub game_name: Ref<identifier::GameIdentifier>,

    pub const_assignments: HashMap<String, Ref<theorem::InstanceConstAssignmentItem>>,
    pub ty_assignments: HashMap<String, Ref<theorem::InstanceTypeAssignmentItem>>,
}

#[derive(Debug)]
pub struct TheoremVisitorPartialTables<'a> {
    // theorem-specific tables
    pub theorem_names: &'a mut PartialDenseTable<identifier::TheoremIdentifier, TheoremResolution>,
    pub theorem_type_names:
        &'a mut PartialDenseTable<identifier::TheoremTypeIdentifier, TheoremTypeResolution>,
    pub theorem_type_arg_names: &'a mut PartialDenseTable<
        identifier::TheoremTypeArgumentIdentifier,
        TheoremTypeArgResolution,
    >,
    pub theorem_const_value_names: &'a mut PartialDenseTable<
        identifier::TheoremConstValueIdentifier,
        TheoremConstValueResolution,
    >,
    pub game_inst_names:
        &'a mut PartialDenseTable<identifier::GameInstanceIdentifier, GameInstanceResolution>,
    pub assumption_names:
        &'a mut PartialDenseTable<identifier::AssumptionIdentifier, AssumptionResolution>,
    pub lemma_names: &'a mut PartialDenseTable<identifier::LemmaIdentifier, LemmaResolution>,

    // shared tables (used for resolving game names in instantiation, oracle names in equivalences, etc.)
    pub game_names: &'a mut PartialDenseTable<identifier::GameIdentifier, GameResolution>,
    pub game_type_names:
        &'a mut PartialDenseTable<identifier::GameTypeIdentifier, GameTypeResolution>,
    pub game_const_value_names:
        &'a mut PartialDenseTable<identifier::GameConstValueIdentifier, GameConstValueResolution>,
    pub pkg_inst_names:
        &'a mut PartialDenseTable<identifier::PackageInstanceIdentifier, PackageInstanceResolution>,
    pub oracle_composition_import_names: &'a mut PartialDenseTable<
        identifier::OracleCompositionIdentifier,
        OracleCompositionImportResolution,
    >,
    pub oracle_composition_def_names: &'a mut PartialDenseTable<
        identifier::OracleCompositionIdentifier,
        OracleCompositionDefinitionResolution,
    >,
}

#[derive(Debug, Clone)]
enum Position {
    /// We are at or near the top level. No relevant information has been accumulated.
    TopLevel,

    /// We are inside a game instance, but the game could not be resolved.
    UnresolvedGameInstance(Ref<diag::Diagnostic>),

    /// We are inside a game instance.
    GameInstance(GameInstanceInfo),

    /// We are inside an equivalence oracle block, with a reference to the left and right game instances.
    EquivalenceOracleBlock {
        left_inst: Ref<theorem::InstanceBlock>,
        right_inst: Ref<theorem::InstanceBlock>,
    },
}

impl Position {
    fn replace_with(&mut self, mut new_position: Self) -> Self {
        core::mem::swap(self, &mut new_position);
        new_position
    }

    fn reset(&mut self) -> Self {
        self.replace_with(Self::TopLevel)
    }
}

pub struct TheoremVisitor<'arena, 'res> {
    // inputs: read only
    games: &'res HashMap<&'arena str, GameInfo>,
    packages: &'res HashMap<&'arena str, PackageInfo>,
    locations: &'arena LocationTable,

    // outputs: this is what is being populated
    diagnostics: &'arena mut diag::Diagnostics,
    tables: TheoremVisitorPartialTables<'res>,
    info: &'res mut Option<TheoremInfo>,

    // internal: state we keep while visiting, will be discarded
    scope: Scope<TheoremDeclaration<'res>>,
    position: Position,
}

impl<'arena, 'res> TheoremVisitor<'arena, 'res> {
    pub fn new(
        locations: &'arena GlobalTable<SourceLocation>,
        diagnostics: &'arena mut diag::Diagnostics,
        tables: TheoremVisitorPartialTables<'arena>,
        info: &'arena mut Option<TheoremInfo>,
        games: &'res HashMap<&'arena str, GameInfo>,
        packages: &'res HashMap<&'arena str, PackageInfo>,
    ) -> Self {
        let scope = Scope::new();
        let position = Position::TopLevel;

        Self {
            games,
            packages,
            locations,
            diagnostics,
            tables,
            info,
            scope,
            position,
        }
    }
}

impl<'a, 'res: 'a> domino_ast::Visitor for TheoremVisitor<'a, 'res> {
    fn thm(&mut self, arenas: &Arenas, node: Ref<theorem::Theorem>) {
        let thm = arenas.thm.get(node);

        self.declare_theorem(arenas, node);

        self.thm_ident(arenas, thm.name);
        self.thm_item_list(arenas, thm.items);
    }

    fn thm_item_list(&mut self, arenas: &Arenas, node: Ref<theorem::TheoremItemList>) {
        let thm_item_list = arenas.thm_item_list.get(node);

        let mut nodes: Vec<_> = thm_item_list.items.refs().collect();
        nodes.sort_by_key(|node| match arenas.thm_item.get(*node) {
            theorem::TheoremItem::ConstParams(_) => 0,
            theorem::TheoremItem::GameInstance(_) => 1,
            theorem::TheoremItem::Assumptions(_) => 2,
            theorem::TheoremItem::GameHops(_) => 3,
        });
        nodes
            .into_iter()
            .for_each(|node| self.thm_item(arenas, node));
    }

    fn thm_const_decl(&mut self, arenas: &Arenas, node: Ref<theorem::TheoremConstDecl>) {
        let decl = arenas.thm_const_decl.get(node);
        self.theorem_type(arenas, decl.ty);

        // DON'T recurse into the ident child node here, as that would try resolving
        // instead of declaring.

        self.declare_const_param(arenas, node);
    }

    fn thm_type_ident(&mut self, arenas: &Arenas, node: Ref<identifier::TheoremTypeIdentifier>) {
        self.resolve_type(arenas, node);
    }

    fn thm_type_arg_ident(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::TheoremTypeArgumentIdentifier>,
    ) {
        self.resolve_type_arg(arenas, node);
    }

    fn thm_const_value_ident(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::TheoremConstValueIdentifier>,
    ) {
        self.resolve_value_ident(arenas, node);
    }

    fn thm_inst_block(&mut self, arenas: &Arenas, node: Ref<theorem::InstanceBlock>) {
        let inst = arenas.thm_inst_block.get(node);

        self.resolve_game(arenas, inst.instantiated_name);

        self.position = match self.prepare_game_inst_info(arenas, node) {
            Ok(game_inst_info) => Position::GameInstance(game_inst_info),
            Err(diag) => Position::UnresolvedGameInstance(diag),
        };

        // this needs to be after setting the position
        self.thm_inst_item_list(arenas, inst.items);

        // Consume the resolved game instance and store it
        match self.position.reset() {
            Position::GameInstance(game_inst_info) => {
                self.declare_game_inst(arenas, node, game_inst_info)
            }
            Position::UnresolvedGameInstance(diag) => self
                .tables
                .game_inst_names
                .set(inst.instance_name, GameInstanceResolution::Error(diag)),
            _ => unreachable!(),
        }
    }

    fn thm_inst_const_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<theorem::InstanceConstAssignmentItem>,
    ) {
        let item = arenas.thm_inst_const_item.get(node);

        // `item.ident` names a const param of the instantiated game, so it resolves against that
        // game's params rather than the theorem scope.
        self.resolve_game_const_param(arenas, item.ident);
        self.thm_expr(arenas, item.expr);
    }

    fn thm_inst_type_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<theorem::InstanceTypeAssignmentItem>,
    ) {
        let item = arenas.thm_inst_type_item.get(node);
        self.resolve_game_type_param(arenas, item.ident);
        self.theorem_type(arenas, item.ty);
    }

    fn game_inst_ident(&mut self, arenas: &Arenas, node: Ref<identifier::GameInstanceIdentifier>) {
        self.resolve_game_inst(arenas, node);
    }

    fn assumption_ident(&mut self, arenas: &Arenas, node: Ref<identifier::AssumptionIdentifier>) {
        self.resolve_assumption(arenas, node);
    }

    fn lemma_ident(&mut self, arenas: &Arenas, node: Ref<identifier::LemmaIdentifier>) {
        self.resolve_lemma(arenas, node);
    }

    fn eqv(&mut self, arenas: &Arenas, node: Ref<theorem::Equivalence>) {
        let eqv = arenas.eqv.get(node);

        // Resolve left and right game instance names
        let left_resolution = self.resolve_game_inst(arenas, eqv.left_name);
        let right_resolution = self.resolve_game_inst(arenas, eqv.right_name);

        // Set up position for oracle block resolution
        match (left_resolution, right_resolution) {
            (
                GameInstanceResolution::GameInstance(left_inst),
                GameInstanceResolution::GameInstance(right_inst),
            ) => {
                self.position = Position::EquivalenceOracleBlock {
                    left_inst,
                    right_inst,
                };
            }
            _ => {
                self.position = Position::TopLevel;
            }
        }

        self.eqv_oracle_block_list(arenas, eqv.blocks);
        self.position = Position::TopLevel;
    }

    fn eqv_oracle_block(&mut self, arenas: &Arenas, node: Ref<theorem::EquivalenceOracleBlock>) {
        let block = arenas.eqv_oracle_block.get(node);

        // Resolve the oracle name against the packages of both game instances
        match &self.position {
            Position::EquivalenceOracleBlock {
                left_inst,
                right_inst,
            } => {
                let left_inst = *left_inst;
                let right_inst = *right_inst;
                self.resolve_equivalence_oracle_import(arenas, block.name, left_inst);
                self.resolve_equivalence_oracle_definition(arenas, block.name, right_inst);
            }
            _ => {
                // If game instances couldn't be resolved, mark the oracle names as errors
                let dx = domino_diagnostic::Resolver {
                    arenas,
                    locations: self.locations,
                };
                crate::fail_resolution!(
                    self,
                    block.name,
                    UndefinedIdentifier::new(dx, block.name),
                    oracle_composition_import_names,
                    then {}
                );
                crate::fail_resolution!(
                    self,
                    block.name,
                    UndefinedIdentifier::new(dx, block.name),
                    oracle_composition_def_names,
                    then {}
                );
            }
        }

        // Enter a new scope for lemmas within this oracle block
        self.scope.enter();
        self.eqv_oracle_item_list(arenas, block.items);
        self.scope.leave();
    }

    fn lemma_block(&mut self, arenas: &Arenas, node: Ref<theorem::LemmaBlock>) {
        let block = arenas.lemma_block.get(node);
        self.lemma_item_list(arenas, block.items);
    }

    fn lemma_item(&mut self, arenas: &Arenas, node: Ref<theorem::LemmaItem>) {
        let item = arenas.lemma_item.get(node);
        self.declare_lemma(arenas, node, item);
    }

    fn red(&mut self, arenas: &Arenas, node: Ref<theorem::Reduction>) {
        let red = arenas.red.get(node);

        // Resolve left and right game instance names
        self.resolve_game_inst(arenas, red.left_name);
        self.resolve_game_inst(arenas, red.right_name);

        // Process reduction items
        self.red_item_list(arenas, red.items);
    }

    fn red_map(&mut self, arenas: &Arenas, node: Ref<theorem::ReductionMap>) {
        let map = arenas.red_map.get(node);

        // assumption_name and construction_name are GameInstanceIdentifier refs
        let assumption_resolution = self.resolve_game_inst(arenas, map.assumption_name);
        let construction_resolution = self.resolve_game_inst(arenas, map.construction_name);

        // Set up position for resolving package instance mappings
        // We need the assumption and construction to be resolved game instances
        // to resolve their package instance names in the map items
        self.position = Position::EquivalenceOracleBlock {
            left_inst: match assumption_resolution {
                GameInstanceResolution::GameInstance(inst) => inst,
                _ => {
                    // Can't resolve map items without a valid assumption instance
                    self.position = Position::TopLevel;
                    self.red_map_item_list(arenas, map.items);
                    self.position = Position::TopLevel;
                    return;
                }
            },
            right_inst: match construction_resolution {
                GameInstanceResolution::GameInstance(inst) => inst,
                _ => {
                    self.position = Position::TopLevel;
                    self.red_map_item_list(arenas, map.items);
                    self.position = Position::TopLevel;
                    return;
                }
            },
        };

        self.red_map_item_list(arenas, map.items);
        self.position = Position::TopLevel;
    }

    fn red_map_item(&mut self, arenas: &Arenas, node: Ref<theorem::ReductionMapItem>) {
        let item = arenas.red_map_item.get(node);

        // left_name and right_name are PackageInstanceIdentifier refs
        // They need to be resolved against the assumption and construction game instances'
        // package instances respectively
        match &self.position {
            Position::EquivalenceOracleBlock {
                left_inst,
                right_inst,
            } => {
                let left_inst = *left_inst;
                let right_inst = *right_inst;
                self.resolve_pkg_inst_in_game_inst(arenas, item.left_name, left_inst);
                self.resolve_pkg_inst_in_game_inst(arenas, item.right_name, right_inst);
            }
            _ => {
                let dx = domino_diagnostic::Resolver {
                    arenas,
                    locations: self.locations,
                };
                crate::fail_resolution!(
                    self,
                    item.left_name,
                    UndefinedIdentifier::new(dx, item.left_name),
                    pkg_inst_names,
                    then {}
                );
                crate::fail_resolution!(
                    self,
                    item.right_name,
                    UndefinedIdentifier::new(dx, item.right_name),
                    pkg_inst_names,
                    then {}
                );
            }
        }
    }

    fn red_assumption_line(
        &mut self,
        arenas: &Arenas,
        node: Ref<theorem::ReductionAssumptionLine>,
    ) {
        let line = arenas.red_assumption_line.get(node);
        self.resolve_assumption(arenas, line.name);
    }

    fn conjecture(&mut self, arenas: &Arenas, node: Ref<theorem::Conjecture>) {
        let conj = arenas.conjecture.get(node);

        // Resolve left and right game instance names
        self.resolve_game_inst(arenas, conj.left_name);
        self.resolve_game_inst(arenas, conj.right_name);
    }

    fn assumption_block(&mut self, arenas: &Arenas, node: Ref<theorem::AssumptionsBlock>) {
        let block = arenas.assumption_block.get(node);
        self.assumption_item_list(arenas, block.items);
    }

    fn assumption_item(&mut self, arenas: &Arenas, node: Ref<theorem::AssumptionsItem>) {
        let item = arenas.assumption_item.get(node);

        // Declare the assumption in scope (don't recurse into name, that would try to resolve it)
        self.declare_assumption(arenas, node);

        // Resolve the bound's game instance references
        self.bound(arenas, item.bound);
    }

    fn bound(&mut self, arenas: &Arenas, node: Ref<theorem::Bound>) {
        let bound = arenas.bound.get(node);
        self.resolve_game_inst(arenas, bound.lhs);
        self.resolve_game_inst(arenas, bound.rhs);
    }

    // ignore trivia
    #[inline]
    fn trivia(&mut self, _arenas: &Arenas, _node: Ref<domino_ast::ast_nodes::Trivia>) {}
}

impl<'a: 'res, 'res> TheoremVisitor<'a, 'res> {
    fn declare_theorem(&mut self, arenas: &Arenas, decl_ref: Ref<theorem::Theorem>) {
        let thm = arenas.thm.get(decl_ref);

        *self.info = Some(TheoremInfo {
            theorem: decl_ref,
            name: thm.name,
            const_params: Default::default(),
            instances: Default::default(),
            assumptions: Default::default(),
        });

        self.tables
            .theorem_names
            .set(thm.name, TheoremResolution::Theorem(decl_ref));
    }

    fn declare_const_param(&mut self, arenas: &Arenas, node: Ref<theorem::TheoremConstDecl>) {
        let decl = arenas.thm_const_decl.get(node);
        let name = get_text(decl.name, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self
            .scope
            .declare(name, TheoremDeclaration::TheoremConst(node))
        {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                TheoremDeclarationPlace::BuiltIn => {
                    diag::CantRedefineBuiltin::new(dx, decl.name).into()
                }
                TheoremDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, decl.name, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, decl.name, err, theorem_const_value_names);
        };

        self.info
            .as_mut()
            .expect("theorem info not set")
            .const_params
            .insert(name.to_string(), node);

        self.tables
            .theorem_const_value_names
            .set(decl.name, TheoremConstValueResolution::ConstParam(node));
    }

    fn declare_game_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<theorem::InstanceBlock>,
        info: GameInstanceInfo,
    ) {
        let block = arenas.thm_inst_block.get(node);
        let name = get_text(info.name, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self
            .scope
            .declare(name, TheoremDeclaration::GameInstance(info.clone()))
        {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                TheoremDeclarationPlace::BuiltIn => {
                    diag::CantRedefineBuiltin::new(dx, block.instance_name).into()
                }
                TheoremDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, block.instance_name, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, block.instance_name, err, game_inst_names);
        };

        let declare_info_ok = self
            .info
            .as_mut()
            .expect("theorem info not set")
            .instances
            .insert(name.to_string(), info)
            .is_none();

        // ensure that the scope and the info table agree
        debug_assert!(declare_info_ok);

        self.tables.game_inst_names.set(
            block.instance_name,
            GameInstanceResolution::GameInstance(node),
        );
    }

    fn declare_assumption(&mut self, arenas: &Arenas, node: Ref<theorem::AssumptionsItem>) {
        let item = arenas.assumption_item.get(node);
        let name = get_text(item.name, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self
            .scope
            .declare(name, TheoremDeclaration::Assumption(node))
        {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                TheoremDeclarationPlace::BuiltIn => {
                    diag::CantRedefineBuiltin::new(dx, item.name).into()
                }
                TheoremDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, item.name, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, item.name, err, assumption_names);
        };

        self.info
            .as_mut()
            .expect("theorem info not set")
            .assumptions
            .insert(name.to_string(), node);

        self.tables
            .assumption_names
            .set(item.name, AssumptionResolution::Assumption(node));
    }

    fn declare_lemma(
        &mut self,
        arenas: &Arenas,
        node: Ref<theorem::LemmaItem>,
        item: &theorem::LemmaItem,
    ) {
        let name = get_text(item.name, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self.scope.declare(name, TheoremDeclaration::Lemma(node)) {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                TheoremDeclarationPlace::BuiltIn => {
                    diag::CantRedefineBuiltin::new(dx, item.name).into()
                }
                TheoremDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, item.name, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, item.name, err, lemma_names);
        };

        self.tables
            .lemma_names
            .set(item.name, LemmaResolution::Lemma(node));
    }

    fn prepare_game_inst_info(
        &mut self,
        arenas: &Arenas,
        game_inst: Ref<theorem::InstanceBlock>,
    ) -> Result<GameInstanceInfo, Ref<diag::Diagnostic>> {
        let inst = arenas.thm_inst_block.get(game_inst);
        let name = inst.instance_name;
        let game_name_ref = inst.instantiated_name;

        let resolved_game = match self
            .tables
            .game_names
            .get(game_name_ref)
            .expect("the caller must set this first")
        {
            GameResolution::Game(_) => {
                let game_name = get_text(game_name_ref, self.locations, &arenas.source);

                self.games
                    .get(&game_name)
                    .expect("looking up a resolved game should have succeeded")
            }
            GameResolution::Error(diag) => return Err(diag),
        };

        Ok(GameInstanceInfo {
            game_inst,
            name,
            game_name: resolved_game.name,
            const_assignments: Default::default(),
            ty_assignments: Default::default(),
        })
    }

    fn resolve_type(&mut self, arenas: &Arenas, node: Ref<identifier::TheoremTypeIdentifier>) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let resolution = match self.scope.lookup(name).cloned() {
            Some(TheoremDeclaration::BuiltinType(ty)) => TheoremTypeResolution::Builtin(ty),
            None => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    theorem_type_names
                );
            }
            Some(other) => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::ExpectedTypeIdentifier::new(dx, node, other),
                    theorem_type_names
                );
            }
        };

        self.tables.theorem_type_names.set(node, resolution);
    }

    fn resolve_type_arg(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::TheoremTypeArgumentIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let resolution = match self.scope.lookup(name).cloned() {
            Some(TheoremDeclaration::BuiltinType(ty)) => TheoremTypeArgResolution::Builtin(ty),
            None => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    theorem_type_arg_names
                );
            }
            Some(other) => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::ExpectedTypeArgIdentifier::new(dx, node, other),
                    theorem_type_arg_names
                );
            }
        };

        self.tables.theorem_type_arg_names.set(node, resolution);
    }

    fn resolve_game(&mut self, arenas: &Arenas, node: Ref<identifier::GameIdentifier>) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);
        let Some(game_info) = self.games.get(name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                game_names
            );
        };

        self.tables
            .game_names
            .set(node, GameResolution::Game(game_info.game));
    }

    fn resolve_game_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::GameInstanceIdentifier>,
    ) -> GameInstanceResolution {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let Some(decl) = self.scope.lookup(name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                game_inst_names,
                then err => { return GameInstanceResolution::Error(err) }
            );
        };

        // check that the identifier actually refers to a game instance
        let TheoremDeclaration::GameInstance(game_inst) = decl else {
            crate::fail_resolution!(
                self,
                node,
                diag::ExpectedGameInstanceIdentifier::new(dx, node, decl.clone()),
                game_inst_names,
                then err => { return GameInstanceResolution::Error(err) }
            );
        };

        let resolution = GameInstanceResolution::GameInstance(game_inst.game_inst);

        self.tables.game_inst_names.set(node, resolution);

        resolution
    }

    fn resolve_assumption(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::AssumptionIdentifier>,
    ) -> AssumptionResolution {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let Some(decl) = self.scope.lookup(name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                assumption_names,
                then err => { return AssumptionResolution::Error(err) }
            );
        };

        let TheoremDeclaration::Assumption(assumption) = decl else {
            crate::fail_resolution!(
                self,
                node,
                diag::ExpectedAssumptionIdentifier::new(dx, node, decl.clone()),
                assumption_names,
                then err => { return AssumptionResolution::Error(err) }
            );
        };

        let resolution = AssumptionResolution::Assumption(*assumption);

        self.tables.assumption_names.set(node, resolution);

        resolution
    }

    fn resolve_lemma(&mut self, arenas: &Arenas, node: Ref<identifier::LemmaIdentifier>) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let resolution = match self.scope.lookup(name) {
            None => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    lemma_names
                );
            }
            Some(TheoremDeclaration::Lemma(lemma)) => LemmaResolution::Lemma(*lemma),
            Some(_other) => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    lemma_names
                );
            }
        };

        self.tables.lemma_names.set(node, resolution);
    }

    /// Resolve a value identifier in an expression.
    fn resolve_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::TheoremConstValueIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);
        let resolution = match self.scope.lookup(ident_name) {
            None => {
                crate::fail_resolution!(
                    self,
                    ident,
                    diag::UndefinedIdentifier::new(dx, ident),
                    theorem_const_value_names
                );
            }

            Some(TheoremDeclaration::TheoremConst(decl)) => {
                TheoremConstValueResolution::ConstParam(*decl)
            }
            Some(TheoremDeclaration::BuiltinValue(builtin)) => {
                TheoremConstValueResolution::Builtin(*builtin)
            }

            Some(decl) => {
                crate::fail_resolution!(
                    self,
                    ident,
                    diag::ExpectedValueIdentifier::new(dx, ident, decl.clone()),
                    theorem_const_value_names
                );
            }
        };

        self.tables.theorem_const_value_names.set(ident, resolution);
    }

    fn resolve_game_type_param(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::GameTypeIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let game_inst_info = match &mut self.position {
            Position::GameInstance(game_inst_info) => game_inst_info,
            Position::UnresolvedGameInstance(diag) => {
                crate::fail_resolution_ref!(self, node, *diag, game_type_names)
            }
            other => {
                unreachable!("expected to be in Position::GameInstance, but am in {other:?}")
            }
        };

        let in_game_instance = *arenas.thm_inst_block.get(game_inst_info.game_inst);
        let ty_name = get_text(node, self.locations, &arenas.source);
        let game_name = get_text(
            in_game_instance.instantiated_name,
            self.locations,
            &arenas.source,
        );

        let Some(game) = self.games.get(game_name) else {
            unreachable!();
        };

        let Some(decl) = game.type_params.get(ty_name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                game_type_names
            );
        };

        self.tables
            .game_type_names
            .set(node, GameTypeResolution::TypeParam(*decl));
    }

    fn resolve_game_const_param(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::GameConstValueIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let game_inst_info = match &mut self.position {
            Position::GameInstance(game_inst_info) => game_inst_info,
            Position::UnresolvedGameInstance(diag) => {
                crate::fail_resolution_ref!(self, node, *diag, game_const_value_names)
            }
            other => {
                unreachable!("expected to be in Position::GameInstance, but am in {other:?}")
            }
        };

        let in_game_instance = *arenas.thm_inst_block.get(game_inst_info.game_inst);
        let const_name = get_text(node, self.locations, &arenas.source);
        let game_name = get_text(
            in_game_instance.instantiated_name,
            self.locations,
            &arenas.source,
        );

        let Some(game) = self.games.get(game_name) else {
            unreachable!();
        };

        let Some(decl) = game.const_params.get(const_name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                game_const_value_names
            );
        };

        self.tables
            .game_const_value_names
            .set(node, GameConstValueResolution::ConstParam(*decl));
    }

    /// Resolve a package instance identifier against a game instance's package instances
    fn resolve_pkg_inst_in_game_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::PackageInstanceIdentifier>,
        game_inst_ref: Ref<theorem::InstanceBlock>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let inst = arenas.thm_inst_block.get(game_inst_ref);
        let game_name = get_text(inst.instantiated_name, self.locations, &arenas.source);

        let Some(game_info) = self.games.get(game_name) else {
            crate::fail_resolution!(
                self,
                node,
                UndefinedIdentifier::new(dx, node),
                pkg_inst_names
            );
        };

        let pkg_inst_name = get_text(node, self.locations, &arenas.source);

        if pkg_inst_name == "adversary" {
            self.tables
                .pkg_inst_names
                .set(node, PackageInstanceResolution::Adversary);
            return;
        }

        let Some(pkg_inst_info) = game_info.instances.get(pkg_inst_name) else {
            crate::fail_resolution!(
                self,
                node,
                UndefinedIdentifier::new(dx, node),
                pkg_inst_names
            );
        };

        self.tables.pkg_inst_names.set(
            node,
            PackageInstanceResolution::PackageInstance(pkg_inst_info.pkg_inst),
        );
    }

    /// Resolve oracle import in a game instance's package for equivalence blocks
    fn resolve_equivalence_oracle_import(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::OracleCompositionIdentifier>,
        game_inst_ref: Ref<theorem::InstanceBlock>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let inst = arenas.thm_inst_block.get(game_inst_ref);
        let game_name = get_text(inst.instantiated_name, self.locations, &arenas.source);
        let oracle_name = self.get_text(arenas, node);

        let Some(game_info) = self.games.get(game_name) else {
            crate::fail_resolution!(
                self,
                node,
                UndefinedIdentifier::new(dx, node),
                oracle_composition_import_names
            );
        };

        // In an equivalence, we need to find the oracle in the game's packages.
        // Look through all package instances of the game to find the oracle import.
        for pkg_inst_info in game_info.instances.values() {
            let pkg_name = get_text(pkg_inst_info.pkg_name, self.locations, &arenas.source);
            if let Some(pkg_info) = self.packages.get(pkg_name) {
                if let Some(oracle) = pkg_info.oracle_imports.get(oracle_name).copied() {
                    self.tables.oracle_composition_import_names.set(
                        node,
                        OracleCompositionImportResolution::EquivalenceOracle {
                            sig: oracle,
                            pkg_inst: pkg_inst_info.pkg_inst,
                            game_inst: game_inst_ref,
                        },
                    );
                    return;
                }
            }
        }

        crate::fail_resolution!(
            self,
            node,
            UndefinedIdentifier::new(dx, node),
            oracle_composition_import_names
        );
    }

    /// Resolve oracle definition in a game instance's package for equivalence blocks
    fn resolve_equivalence_oracle_definition(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::OracleCompositionIdentifier>,
        game_inst_ref: Ref<theorem::InstanceBlock>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let inst = arenas.thm_inst_block.get(game_inst_ref);
        let game_name = get_text(inst.instantiated_name, self.locations, &arenas.source);
        let oracle_name = self.get_text(arenas, node);

        let Some(game_info) = self.games.get(game_name) else {
            crate::fail_resolution!(
                self,
                node,
                UndefinedIdentifier::new(dx, node),
                oracle_composition_def_names
            );
        };

        // Look through all package instances of the game to find the oracle definition.
        for pkg_inst_info in game_info.instances.values() {
            let pkg_name = get_text(pkg_inst_info.pkg_name, self.locations, &arenas.source);
            if let Some(pkg_info) = self.packages.get(pkg_name) {
                if let Some(oracle) = pkg_info.oracle_definitions.get(oracle_name).copied() {
                    self.tables.oracle_composition_def_names.set(
                        node,
                        OracleCompositionDefinitionResolution::EquivalenceOracle {
                            def: oracle,
                            pkg_inst: pkg_inst_info.pkg_inst,
                            game_inst: game_inst_ref,
                        },
                    );
                    return;
                }
            }
        }

        crate::fail_resolution!(
            self,
            node,
            UndefinedIdentifier::new(dx, node),
            oracle_composition_def_names
        );
    }

    fn get_text<'b, T: NodeType>(&self, arenas: &'b Arenas, node: Ref<T>) -> &'b str {
        let id = node.global_ref_id();
        let loc = *self.locations.get(&id).unwrap();
        arenas.source.text(loc)
    }
}

#[derive(Debug, Clone)]
enum TheoremDeclaration<'res> {
    Game(&'res GameInfo),
    GameInstance(GameInstanceInfo),
    Assumption(Ref<theorem::AssumptionsItem>),
    Lemma(Ref<theorem::LemmaItem>),

    BuiltinType(BuiltinType),

    TheoremConst(Ref<theorem::TheoremConstDecl>),

    BuiltinValue(BuiltinValue),
}

impl<'res> TheoremDeclaration<'res> {
    fn place(&self) -> TheoremDeclarationPlace {
        let ref_id = match self {
            TheoremDeclaration::BuiltinType(_) | TheoremDeclaration::BuiltinValue(_) => {
                return TheoremDeclarationPlace::BuiltIn
            }

            TheoremDeclaration::Game(info) => info.game.global_ref_id(),
            TheoremDeclaration::GameInstance(info) => info.game_inst.global_ref_id(),
            TheoremDeclaration::Assumption(r) => r.global_ref_id(),
            TheoremDeclaration::Lemma(r) => r.global_ref_id(),

            TheoremDeclaration::TheoremConst(r) => r.global_ref_id(),
        };

        TheoremDeclarationPlace::UserDeclaration(ref_id)
    }
}

enum TheoremDeclarationPlace {
    BuiltIn,
    UserDeclaration(GlobalRefId),
}

impl From<BuiltinType> for TheoremDeclaration<'_> {
    fn from(value: BuiltinType) -> Self {
        Self::BuiltinType(value)
    }
}

impl From<BuiltinValue> for TheoremDeclaration<'_> {
    fn from(value: BuiltinValue) -> Self {
        Self::BuiltinValue(value)
    }
}

impl crate::Declaration for TheoremDeclaration<'_> {
    fn decl_type(&self) -> DeclarationType {
        match self {
            TheoremDeclaration::BuiltinType(_) => DeclarationType::Type,

            TheoremDeclaration::Game(_) => DeclarationType::Game,
            TheoremDeclaration::GameInstance(_) => DeclarationType::GameInstance,
            TheoremDeclaration::Assumption(_) => DeclarationType::Assumption,
            TheoremDeclaration::Lemma(_) => DeclarationType::PureValue,

            TheoremDeclaration::BuiltinValue(BuiltinValue::True) => DeclarationType::PureValue,
            TheoremDeclaration::BuiltinValue(BuiltinValue::False) => DeclarationType::PureValue,
            TheoremDeclaration::BuiltinValue(BuiltinValue::None) => DeclarationType::PureValue,
            TheoremDeclaration::BuiltinValue(BuiltinValue::EmptyTable) => DeclarationType::PureValue,
            TheoremDeclaration::TheoremConst(_) => DeclarationType::PureValue,

            TheoremDeclaration::BuiltinValue(BuiltinValue::Some) => DeclarationType::Value,
        }
    }
}
