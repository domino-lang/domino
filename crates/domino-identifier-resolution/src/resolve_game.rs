use std::collections::HashMap;

use domino_ast::{
    arena::Ref,
    ast_nodes::{game, identifier, NodeType},
    source::SourceLocation,
    Arenas, GlobalRefId, GlobalTable, LocationTable, PartialDenseTable,
};

use crate::{
    diag::{self, UndefinedIdentifier},
    resolutions::*,
    scope::*,
    util::get_text,
    BuiltinType, BuiltinValue, DeclarationType, PackageInfo,
};

#[derive(Debug, Clone)]
pub struct GameInfo {
    pub game: Ref<game::Game>,
    pub name: Ref<identifier::GameIdentifier>,
    pub const_params: HashMap<String, Ref<game::GameConstDecl>>,
    pub type_params: HashMap<String, Ref<identifier::GameTypeIdentifier>>,
    pub instances: HashMap<String, PackageInstanceInfo>,
}

#[derive(Debug, Clone)]
pub struct PackageInstanceInfo {
    pub pkg_inst: Ref<game::InstanceBlock>,
    pub name: Ref<identifier::PackageInstanceIdentifier>,
    pub pkg_name: Ref<identifier::PackageIdentifier>,

    pub const_assignments: HashMap<String, Ref<game::InstanceConstAssignmentItem>>,
    pub ty_assignments: HashMap<String, Ref<game::InstanceTypeAssignmentItem>>,
}

#[derive(Debug)]
pub struct GameVisitorPartialTables<'a> {
    pub game_names: &'a mut PartialDenseTable<identifier::GameIdentifier, GameResolution>,
    pub game_type_names:
        &'a mut PartialDenseTable<identifier::GameTypeIdentifier, GameTypeResolution>,
    pub game_type_arg_names:
        &'a mut PartialDenseTable<identifier::GameTypeArgumentIdentifier, GameTypeArgResolution>,
    pub game_const_value_names:
        &'a mut PartialDenseTable<identifier::GameConstValueIdentifier, GameConstValueResolution>,
    pub pkg_inst_names:
        &'a mut PartialDenseTable<identifier::PackageInstanceIdentifier, PackageInstanceResolution>,
    pub pkg_const_value_names: &'a mut PartialDenseTable<
        identifier::PackageConstValueIdentifier,
        PackageConstValueResolution,
    >,
    pub pkg_names: &'a mut PartialDenseTable<identifier::PackageIdentifier, PackageResolution>,
    pub oracle_composition_import_names: &'a mut PartialDenseTable<
        identifier::OracleCompositionIdentifier,
        OracleCompositionImportResolution,
    >,
    pub oracle_composition_def_names: &'a mut PartialDenseTable<
        identifier::OracleCompositionIdentifier,
        OracleCompositionDefinitionResolution,
    >,
    pub pkg_type_names:
        &'a mut PartialDenseTable<identifier::PackageTypeIdentifier, PackageTypeResolution>,
}

#[derive(Debug, Clone)]
enum Position {
    /// We are at or near the top level. No relevant information has been accumulated.
    TopLevel,

    /// We are inside a package instance, but the package could not be resolved.
    UnresolvedPackageInstance(Ref<diag::Diagnostic>),

    /// We are inside a package instance.
    /// This variant contains a partial PackageInstanceInfo, which is extracted when it is complete.
    PackageInstance(PackageInstanceInfo),

    /// We are in the inner part of a transition, i.e. the one that maps a package instances oracles
    /// to the callee package instances.
    Composition(PackageInstanceResolution),
}

impl Position {
    fn pkg_inst_mut(&mut self) -> Option<&mut PackageInstanceInfo> {
        if let Position::PackageInstance(ref mut pkg_inst_info) = self {
            Some(pkg_inst_info)
        } else {
            None
        }
    }

    fn replace_with(&mut self, mut new_position: Self) -> Self {
        core::mem::swap(self, &mut new_position);
        new_position
    }

    fn reset(&mut self) -> Self {
        self.replace_with(Self::TopLevel)
    }
}

pub struct GameVisitor<'arena, 'res> {
    // inputs: read only
    packages: &'res HashMap<&'arena str, PackageInfo>,
    locations: &'arena LocationTable,

    // outputs: this is what is being populated
    diagnostics: &'arena mut diag::Diagnostics,
    tables: GameVisitorPartialTables<'res>,
    info: &'res mut Option<GameInfo>,

    // internal: state we keep while visiting, will be discarded
    scope: Scope<GameDeclaration<'res>>,
    position: Position,
}

impl<'arena, 'res> GameVisitor<'arena, 'res> {
    pub fn new(
        locations: &'arena GlobalTable<SourceLocation>,
        diagnostics: &'arena mut diag::Diagnostics,
        tables: GameVisitorPartialTables<'arena>,
        info: &'arena mut Option<GameInfo>,
        packages: &'res HashMap<&'arena str, PackageInfo>,
    ) -> Self {
        let scope = Scope::new();
        let position = Position::TopLevel;

        Self {
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

impl<'a, 'res: 'a> domino_ast::Visitor for GameVisitor<'a, 'res> {
    fn game(&mut self, arenas: &domino_ast::Arenas, node: domino_ast::arena::Ref<game::Game>) {
        let game = arenas.game.get(node);

        self.declare_game(arenas, node);

        self.game_ident(arenas, game.name);
        self.game_item_list(arenas, game.items);
    }

    fn game_item_list(&mut self, arenas: &Arenas, node: Ref<game::GameItemList>) {
        let game_item_list = arenas.game_item_list.get(node);

        let mut nodes: Vec<_> = game_item_list.items.refs().collect();
        nodes.sort_by_key(|node| match arenas.game_item.get(*node) {
            game::GameItem::TypeParams(_) => 0,
            game::GameItem::ConstParams(_) => 1,
            game::GameItem::Instance(_) => 2,
            game::GameItem::Compose(_) => 3,
        });
        nodes
            .into_iter()
            .for_each(|node| self.game_item(arenas, node));
    }

    fn game_type_decl_list(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<game::GameTypeDeclList>,
    ) {
        arenas
            .game_type_decl_list
            .get(node)
            .items
            .refs()
            .for_each(|ty_decl| self.declare_type_param(arenas, ty_decl));
    }

    fn game_const_decl(&mut self, arenas: &Arenas, node: Ref<game::GameConstDecl>) {
        let decl = arenas.game_const_decl.get(node);
        self.game_type(arenas, decl.ty);

        // DON'T recurse into the ident child node here, as that would try resolving
        // instead of declaring.

        self.declare_const_param(arenas, node);
    }

    fn game_type_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::GameTypeIdentifier>,
    ) {
        self.resolve_type(arenas, node);
    }

    fn game_type_arg_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::GameTypeArgumentIdentifier>,
    ) {
        self.resolve_type_arg(arenas, node);
    }

    fn game_inst_block(&mut self, arenas: &Arenas, node: Ref<game::InstanceBlock>) {
        let inst = arenas.game_inst_block.get(node);

        self.resolve_pkg(arenas, inst.instantiated_name);

        self.position = match self.prepare_pkg_inst_info(arenas, node) {
            Ok(pkg_inst_info) => Position::PackageInstance(pkg_inst_info),
            Err(diag) => Position::UnresolvedPackageInstance(diag),
        };

        // this needs to be after setting the position
        self.game_inst_item_list(arenas, inst.items);

        // Consume the resolved package instance and store it - if we are
        match self.position.reset() {
            Position::PackageInstance(pkg_inst_info) => {
                self.declare_game_inst(arenas, node, pkg_inst_info)
            }
            Position::UnresolvedPackageInstance(diag) => self
                .tables
                .pkg_inst_names
                .set(inst.instance_name, PackageInstanceResolution::Error(diag)),
            _ => unreachable!(),
        }
    }

    fn game_inst_const_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::InstanceConstAssignmentItem>,
    ) {
        let item = arenas.game_inst_const_item.get(node);

        // `item.ident` names a const param of the instantiated package, so it resolves against that
        // package's params rather than the game scope.
        // Recursing would reach `pkg_const_value_ident`, which this visitor doesn't handle.
        self.resolve_pkg_const_param(arenas, item.ident);
        self.game_expr(arenas, item.expr);
    }

    fn game_inst_type_item(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<game::InstanceTypeAssignmentItem>,
    ) {
        let item = arenas.game_inst_type_item.get(node);
        self.resolve_pkg_type_param(arenas, item.ident);
        self.game_type(arenas, item.ty);
    }

    fn game_const_value_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::GameConstValueIdentifier>,
    ) {
        self.resolve_value_ident(arenas, node);
    }

    fn compose_pkg_inst_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::ComposePackageInstanceItem>,
    ) {
        let item = arenas.compose_pkg_inst_item.get(node);
        let resolution = self.resolve_pkg_inst(arenas, item.pkg_inst_name);

        self.position = Position::Composition(resolution);
        self.compose_oracle_item_list(arenas, item.items);
        self.position = Position::TopLevel;
    }

    fn compose_oracle_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::ComposeOracleAssignmentItem>,
    ) {
        // We have to resolve the oracle twice:
        // 1. in the import signatures of the import in the calling/left package instance
        //    (if outer instance is not the adversary)
        // 2. in the definitions of the callee package instance on the right

        let item = arenas.compose_oracle_item.get(node);

        let Position::Composition(left_resolution) = self.position else {
            unreachable!()
        };

        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        // resolve caller
        match left_resolution {
            PackageInstanceResolution::Adversary => {
                self.tables.oracle_composition_import_names.set(
                    item.oracle_name,
                    OracleCompositionImportResolution::Adversary,
                );
            }

            // Resolve in the oracle name in the caller's imports
            PackageInstanceResolution::PackageInstance(left_inst_ref) => {
                self.resolve_oracle_import_in_pkg_inst(arenas, item.oracle_name, left_inst_ref);
            }

            PackageInstanceResolution::Error(err) => {
                self.tables.oracle_composition_import_names.set(
                    item.oracle_name,
                    OracleCompositionImportResolution::Error(err),
                );
            }
        }

        // resolve callee
        match self.resolve_pkg_inst(arenas, item.pkg_inst_name) {
            PackageInstanceResolution::PackageInstance(right_inst_ref) => {
                self.resolve_oracle_definition_in_pkg_inst(
                    arenas,
                    item.oracle_name,
                    right_inst_ref,
                );
            }

            PackageInstanceResolution::Adversary => {
                crate::fail_resolution!(
                    self,
                    item.oracle_name,
                    diag::AdversaryAsCallee::new(dx, item.oracle_name,),
                    oracle_composition_def_names,
                    then {}
                );
            }
            PackageInstanceResolution::Error(err) => {
                self.tables.oracle_composition_def_names.set(
                    item.oracle_name,
                    OracleCompositionDefinitionResolution::Error(err),
                );
            }
        }
    }

    // ignore trivia
    #[inline]
    fn trivia(
        &mut self,
        _arenas: &domino_ast::Arenas,
        _node: domino_ast::arena::Ref<domino_ast::ast_nodes::Trivia>,
    ) {
    }
}

impl<'a: 'res, 'res> GameVisitor<'a, 'res> {
    fn declare_game(&mut self, arenas: &Arenas, decl_ref: Ref<game::Game>) {
        let game = arenas.game.get(decl_ref);

        *self.info = Some(GameInfo {
            game: decl_ref,
            name: game.name,
            const_params: Default::default(),
            type_params: Default::default(),
            instances: Default::default(),
        });

        self.tables
            .game_names
            .set(game.name, GameResolution::Game(decl_ref));
    }

    fn declare_type_param(&mut self, arenas: &Arenas, ty: Ref<identifier::GameTypeIdentifier>) {
        let ident_name = get_text(ty, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self
            .scope
            .declare(ident_name, GameDeclaration::TypeParam(ty))
        {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                GameDeclarationPlace::BuiltIn => diag::CantRedefineBuiltin::new(dx, ty).into(),
                GameDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, ty, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, ty, err, game_type_names);
        };

        self.info
            .as_mut()
            .expect("game info not set")
            .type_params
            .insert(ident_name.to_string(), ty);

        self.tables
            .game_type_names
            .set(ty, GameTypeResolution::TypeParam(ty));
    }

    fn declare_const_param(&mut self, arenas: &Arenas, node: Ref<game::GameConstDecl>) {
        let decl = arenas.game_const_decl.get(node);
        let name = get_text(decl.name, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self.scope.declare(name, GameDeclaration::GameConst(node)) {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                GameDeclarationPlace::BuiltIn => {
                    diag::CantRedefineBuiltin::new(dx, decl.name).into()
                }
                GameDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, decl.name, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, decl.name, err, game_const_value_names);
        };

        self.info
            .as_mut()
            .expect("game info not set")
            .const_params
            .insert(name.to_string(), node);

        self.tables
            .game_const_value_names
            .set(decl.name, GameConstValueResolution::ConstParam(node));
    }

    fn declare_game_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::InstanceBlock>,
        info: PackageInstanceInfo,
    ) {
        let block = arenas.game_inst_block.get(node);
        let name = get_text(info.name, self.locations, &arenas.source);

        // fail if duplicate declaration
        if let Some(existing_decl) = self
            .scope
            .declare(name, GameDeclaration::PackageInstance(info.clone()))
        {
            let dx = domino_diagnostic::Resolver {
                arenas,
                locations: self.locations,
            };

            let err: diag::Diagnostic = match existing_decl.place() {
                GameDeclarationPlace::BuiltIn => {
                    diag::CantRedefineBuiltin::new(dx, block.instance_name).into()
                }
                GameDeclarationPlace::UserDeclaration(global_ref_id) => {
                    domino_ast::with_global_ref_id!(global_ref_id, |r| {
                        diag::AlreadyDefined::new(dx, block.instance_name, r).into()
                    })
                }
            };

            crate::fail_resolution!(self, block.instance_name, err, pkg_inst_names);
        };

        let declare_info_ok = self
            .info
            .as_mut()
            .expect("game info not set")
            .instances
            .insert(name.to_string(), info)
            .is_none();

        // ensure that the scope and the info table agree
        debug_assert!(declare_info_ok);

        self.tables.pkg_inst_names.set(
            block.instance_name,
            PackageInstanceResolution::PackageInstance(node),
        );
    }

    fn prepare_pkg_inst_info(
        &mut self,
        arenas: &Arenas,
        pkg_inst: Ref<game::InstanceBlock>,
    ) -> Result<PackageInstanceInfo, Ref<diag::Diagnostic>> {
        let inst = arenas.game_inst_block.get(pkg_inst);
        let name = inst.instance_name;
        let pkg_name = inst.instantiated_name;

        let resolved_pkg = match self
            .tables
            .pkg_names
            .get(pkg_name)
            .expect("the caller must set this first")
        {
            PackageResolution::Package(_) => {
                // we know the package can be resolved, but we need the PackageInfo instead. So we
                // just look it up - we know it'll succeed.

                let pkg_name = get_text(pkg_name, self.locations, &arenas.source);

                self.packages
                    .get(&pkg_name)
                    .expect("looking up a resolved package should have succeeded")
            }
            PackageResolution::Error(diag) => return Err(diag),
        };

        Ok(PackageInstanceInfo {
            pkg_inst,
            name,
            pkg_name: resolved_pkg.name,
            const_assignments: Default::default(),
            ty_assignments: Default::default(),
        })
    }

    fn resolve_type(&mut self, arenas: &Arenas, node: Ref<identifier::GameTypeIdentifier>) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let resolution = match self.scope.lookup(name).cloned() {
            Some(GameDeclaration::BuiltinType(ty)) => GameTypeResolution::Builtin(ty),
            Some(GameDeclaration::TypeParam(ty)) => GameTypeResolution::TypeParam(ty),
            None => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    game_type_names
                );
            }
            Some(other) => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::ExpectedTypeIdentifier::new(dx, node, other),
                    game_type_names
                );
            }
        };

        self.tables.game_type_names.set(node, resolution);
    }

    fn resolve_type_arg(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::GameTypeArgumentIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);

        let resolution = match self.scope.lookup(name).cloned() {
            Some(GameDeclaration::BuiltinType(ty)) => GameTypeArgResolution::Builtin(ty),
            Some(GameDeclaration::TypeParam(_)) => GameTypeArgResolution::TypeParam(node),
            Some(GameDeclaration::GameConst(decl)) => GameTypeArgResolution::Consts(decl),
            None => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    game_type_arg_names
                );
            }
            Some(other) => {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::ExpectedTypeArgIdentifier::new(dx, node, other),
                    game_type_arg_names
                );
            }
        };

        self.tables.game_type_arg_names.set(node, resolution);
    }

    fn resolve_pkg(&mut self, arenas: &Arenas, node: Ref<identifier::PackageIdentifier>) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        let name = get_text(node, self.locations, &arenas.source);
        let Some(pkg_info) = self.packages.get(name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                pkg_names
            );
        };

        self.tables
            .pkg_names
            .set(node, PackageResolution::Package(pkg_info.pkg));
    }

    fn resolve_pkg_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::PackageInstanceIdentifier>,
    ) -> PackageInstanceResolution {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        // look up the package instance from the scope
        let name = get_text(node, self.locations, &arenas.source);

        //
        let resolution = if name == "adversary" {
            PackageInstanceResolution::Adversary
        } else {
            let Some(decl) = self.scope.lookup(name) else {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::UndefinedIdentifier::new(dx, node),
                    pkg_inst_names,
                    then err => { return PackageInstanceResolution::Error(err) }
                );
            };

            // check that the the identifier actually refers to a package instance
            let GameDeclaration::PackageInstance(pkg_inst) = decl else {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::ExpectedPackageInstanceIdentifier::new(dx, node, decl.clone()),
                    pkg_inst_names,
                    then err => { return PackageInstanceResolution::Error(err) }
                );
            };

            PackageInstanceResolution::PackageInstance(pkg_inst.pkg_inst)
        };

        // set the resolved value in the table
        self.tables.pkg_inst_names.set(node, resolution);

        resolution
    }

    fn resolve_pkg_type_param(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::PackageTypeIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        // SAFETY: this function is only called when we are inside a package instance block, so this is set
        let pkg_inst_info = match &mut self.position {
            Position::PackageInstance(pkg_inst_info) => pkg_inst_info,
            Position::UnresolvedPackageInstance(diag) => {
                crate::fail_resolution_ref!(self, node, *diag, pkg_type_names)
            }
            other => {
                unreachable!("expected to be in Position::PackageInstance, but am in {other:?}",)
            }
        };

        let in_package_instance = *arenas.game_inst_block.get(pkg_inst_info.pkg_inst);

        let ty_name = get_text(node, self.locations, &arenas.source);
        let pkg_name = get_text(
            in_package_instance.instantiated_name,
            self.locations,
            &arenas.source,
        );

        let Some(pkg) = self.packages.get(pkg_name) else {
            // We do not traverse instantiation code if the pacAge can not be resolved, so we only
            // should end up here if that failed.
            unreachable!();
        };

        let Some(decl) = pkg.type_params.get(ty_name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                pkg_type_names
            );
        };

        self.tables
            .pkg_type_names
            .set(node, PackageTypeResolution::TypeParam(*decl));
    }

    fn resolve_pkg_const_param(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::PackageConstValueIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };

        // SAFETY: this function is only called when we are inside a package instance block, so this is set
        let pkg_inst_info = match &mut self.position {
            Position::PackageInstance(pkg_inst_info) => pkg_inst_info,
            Position::UnresolvedPackageInstance(diag) => {
                crate::fail_resolution_ref!(self, node, *diag, pkg_const_value_names)
            }
            other => {
                unreachable!("expected to be in Position::PackageInstance, but am in {other:?}",)
            }
        };

        let in_package_instance = *arenas.game_inst_block.get(pkg_inst_info.pkg_inst);

        let const_name = get_text(node, self.locations, &arenas.source);
        let pkg_name = get_text(
            in_package_instance.instantiated_name,
            self.locations,
            &arenas.source,
        );

        let Some(pkg) = self.packages.get(pkg_name) else {
            // We do not traverse instantiation code if the pacAge can not be resolved, so we only
            // should end up here if that failed.
            unreachable!();
        };

        let Some(decl) = pkg.const_params.get(const_name) else {
            crate::fail_resolution!(
                self,
                node,
                diag::UndefinedIdentifier::new(dx, node),
                pkg_const_value_names
            );
        };

        self.tables
            .pkg_const_value_names
            .set(node, PackageConstValueResolution::ConstParam(*decl));
    }

    fn resolve_oracle_definition_in_pkg_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::OracleCompositionIdentifier>,
        pkg_inst_ref: Ref<game::InstanceBlock>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };
        let oracle_name = self.get_text(arenas, node);

        let pkg_inst = arenas.game_inst_block.get(pkg_inst_ref);

        let pkg_name = get_text(pkg_inst.instantiated_name, self.locations, &arenas.source);
        // SAFETY: The indexing is fine, because we only put a package name into a
        //         PackageInstanceInfo if it exists, so we can assume it is set.
        let Some(oracle) = self.packages[pkg_name]
            .oracle_definitions
            .get(oracle_name)
            .copied()
        else {
            // TODO: maybe use a more specific diagnostic here
            crate::fail_resolution!(
                self,
                node,
                UndefinedIdentifier::new(dx, node),
                oracle_composition_def_names
            );
        };

        self.tables.oracle_composition_def_names.set(
            node,
            OracleCompositionDefinitionResolution::Definition {
                def: oracle,
                pkg_inst: pkg_inst_ref,
            },
        );
    }

    fn resolve_oracle_import_in_pkg_inst(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::OracleCompositionIdentifier>,
        pkg_inst_ref: Ref<game::InstanceBlock>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: self.locations,
        };
        let oracle_name = self.get_text(arenas, node);

        let pkg_inst = arenas.game_inst_block.get(pkg_inst_ref);

        let pkg_name = get_text(pkg_inst.instantiated_name, self.locations, &arenas.source);
        // SAFETY: The indexing is fine, because we only put a package name into a
        //         PackageInstanceInfo if it exists, so we can assume it is set.
        let Some(oracle) = self.packages[pkg_name]
            .oracle_imports
            .get(oracle_name)
            .copied()
        else {
            // TODO: maybe use a more specific diagnostic here
            crate::fail_resolution!(
                self,
                node,
                UndefinedIdentifier::new(dx, node),
                oracle_composition_import_names
            );
        };

        let resolution = OracleCompositionImportResolution::Import {
            sig: oracle,
            pkg_inst: pkg_inst_ref,
        };

        self.tables
            .oracle_composition_import_names
            .set(node, resolution);
    }

    /// indexes a value identifier in an expression (i.e. "right of an assignment arrow").
    /// If the Identifier is not declared yet, that is an error.
    fn resolve_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::GameConstValueIdentifier>,
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
                    game_const_value_names
                );
            }

            Some(GameDeclaration::GameConst(decl)) => GameConstValueResolution::ConstParam(*decl),
            Some(GameDeclaration::BuiltinValue(builtin)) => {
                GameConstValueResolution::Builtin(*builtin)
            }

            Some(decl) => {
                crate::fail_resolution!(
                    self,
                    ident,
                    diag::ExpectedValueIdentifier::new(dx, ident, decl.clone()),
                    game_const_value_names
                );
            }
        };

        self.tables.game_const_value_names.set(ident, resolution);
    }

    fn get_text<'b, T: NodeType>(&self, arenas: &'b Arenas, node: Ref<T>) -> &'b str {
        let id = node.global_ref_id();
        let loc = *self.locations.get(&id).unwrap();
        arenas.source.text(loc)
    }
}

#[derive(Debug, Clone)]
enum GameDeclaration<'res> {
    Package(&'res PackageInfo),
    PackageInstance(PackageInstanceInfo),

    BuiltinType(BuiltinType),
    TypeParam(Ref<identifier::GameTypeIdentifier>),

    GameConst(Ref<game::GameConstDecl>),

    BuiltinValue(BuiltinValue),
}

impl<'res> GameDeclaration<'res> {
    fn place(&self) -> GameDeclarationPlace {
        let ref_id = match self {
            GameDeclaration::BuiltinType(_) | GameDeclaration::BuiltinValue(_) => {
                return GameDeclarationPlace::BuiltIn
            }

            GameDeclaration::Package(info) => info.pkg.global_ref_id(),
            GameDeclaration::PackageInstance(info) => info.pkg_inst.global_ref_id(),

            GameDeclaration::TypeParam(r) => r.global_ref_id(),
            GameDeclaration::GameConst(r) => r.global_ref_id(),
        };

        GameDeclarationPlace::UserDeclaration(ref_id)
    }
}

enum GameDeclarationPlace {
    BuiltIn,
    UserDeclaration(GlobalRefId),
}

impl From<BuiltinType> for GameDeclaration<'_> {
    fn from(value: BuiltinType) -> Self {
        Self::BuiltinType(value)
    }
}

impl From<BuiltinValue> for GameDeclaration<'_> {
    fn from(value: BuiltinValue) -> Self {
        Self::BuiltinValue(value)
    }
}

impl crate::Declaration for GameDeclaration<'_> {
    fn decl_type(&self) -> DeclarationType {
        match self {
            GameDeclaration::BuiltinType(_) => DeclarationType::Type,
            GameDeclaration::TypeParam(_) => DeclarationType::Type,

            GameDeclaration::Package(_) => DeclarationType::Package,
            GameDeclaration::PackageInstance(_) => DeclarationType::PackageInstance,

            GameDeclaration::BuiltinValue(BuiltinValue::True) => DeclarationType::PureValue,
            GameDeclaration::BuiltinValue(BuiltinValue::False) => DeclarationType::PureValue,
            GameDeclaration::BuiltinValue(BuiltinValue::None) => DeclarationType::PureValue,
            GameDeclaration::BuiltinValue(BuiltinValue::EmptyTable) => DeclarationType::PureValue,
            GameDeclaration::GameConst(_) => DeclarationType::PureValue,

            // TODO: Actually, whether this is pure or not depends on whether the inner expression
            //       is pure, but we can't tell that at this point, so we are conservative.
            GameDeclaration::BuiltinValue(BuiltinValue::Some) => DeclarationType::Value,
        }
    }
}
