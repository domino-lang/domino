use std::collections::HashMap;

use domino_ast::{
    arena::Ref,
    ast_nodes::{
        game,
        identifier::{self, GameTypeIdentifier},
        instances, package, types, NodeType,
    },
    source::SourceLocation,
    Arenas, GlobalTable, LocationTable, PartialDenseTable,
};

use crate::{
    diag::{self, ExpectedValueIdentifier, UndefinedIdentifier},
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
    pub game_const_value_names:
        &'a mut PartialDenseTable<identifier::GameConstValueIdentifier, GameConstValueResolution>,
    pub pkg_inst_names:
        &'a mut PartialDenseTable<identifier::PackageInstanceIdentifier, PackageInstanceResolution>,
    pub pkg_const_value_names: &'a mut PartialDenseTable<
        identifier::PackageConstValueIdentifier,
        PackageConstValueResolution,
    >,
    pub pkg_names: &'a mut PartialDenseTable<identifier::PackageIdentifier, PackageResolution>,
    pub oracle_import_names:
        &'a mut PartialDenseTable<identifier::OracleImportIdentifier, OracleImportResolution>,
    pub oracle_def_names: &'a mut PartialDenseTable<
        identifier::OracleDefinitionIdentifier,
        OracleDefinitionResolution,
    >,
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

    /// We are inside a package instance.
    /// This variant contains a partial PackageInstanceInfo, which is extracted when it is complete.
    PackageInstance(PackageInstanceInfo),

    /// We are in the inner part of a transition, i.e. the one that maps a package instances oracles
    /// to the callee package instances.
    Composition(Ref<identifier::PackageInstanceIdentifier>),
}

impl Position {
    fn leave_pkg_instance(&mut self) -> Option<PackageInstanceInfo> {
        if !matches!(self, Self::PackageInstance(_)) {
            return None;
        }

        let mut out = Self::TopLevel;
        core::mem::swap(self, &mut out);

        // SAFETY: We checked above that the value has the right variant.
        let Self::PackageInstance(pkg_inst_info) = out else {
            unreachable!()
        };

        Some(pkg_inst_info)
    }

    fn pkg_inst_mut(&mut self) -> Option<&mut PackageInstanceInfo> {
        if let Position::PackageInstance(ref mut pkg_inst_info) = self {
            Some(pkg_inst_info)
        } else {
            None
        }
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

    fn game_item(&mut self, arenas: &Arenas, node: Ref<game::GameItem>) {
        match *arenas.game_item.get(node) {
            game::GameItem::TypeParams(node) => self.game_type_param_block(arenas, node),
            game::GameItem::ConstParams(node) => self.game_const_param_block(arenas, node),
            game::GameItem::Instance(node) => self.game_inst_block(arenas, node),
            game::GameItem::Compose(node) => self.compose_block(arenas, node),
        }
    }

    fn game_type_param_block(&mut self, arenas: &Arenas, node: Ref<game::GameTypeParamBlock>) {
        let type_params_block = arenas.game_type_param_block.get(node);
        self.game_type_decl_list(arenas, type_params_block.decls)
    }

    fn game_type_decl_list(&mut self, arenas: &Arenas, node: Ref<game::GameTypeDeclList>) {
        arenas
            .game_type_decl_list
            .get(node)
            .items
            .refs()
            .for_each(|ty_decl| self.declare_type_param(arenas, ty_decl));
    }

    fn game_const_param_block(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<game::GameConstParamBlock>,
    ) {
        let const_param_block = arenas.game_const_param_block.get(node);
        self.game_const_decl_list(arenas, const_param_block.decls);
    }

    fn game_const_decl_list(&mut self, arenas: &Arenas, node: Ref<game::GameConstDeclList>) {
        arenas
            .game_const_decl_list
            .get(node)
            .items
            .refs()
            .for_each(|node| self.game_const_decl(arenas, node));
    }

    fn game_const_decl(&mut self, arenas: &Arenas, node: Ref<game::GameConstDecl>) {
        let decl = arenas.game_const_decl.get(node);
        self.game_type(arenas, decl.ty);

        self.declare_const_param(arenas, node);
    }

    fn game_type(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<
            domino_ast::ast_nodes::types::Type<domino_ast::ast_nodes::types::GameTypeKind>,
        >,
    ) {
        let ty = arenas.game_type.get(node);
        match *ty {
            domino_ast::ast_nodes::types::Type::Identifier(node) => {
                self.game_type_ident(arenas, node)
            }
            domino_ast::ast_nodes::types::Type::Tuple(node) => self.game_type_tuple(arenas, node),
            domino_ast::ast_nodes::types::Type::Argumented(node) => {
                self.game_type_app(arenas, node)
            }
            domino_ast::ast_nodes::types::Type::Fn(node) => self.game_type_fn(arenas, node),
        }
    }

    fn game_type_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::GameTypeIdentifier>,
    ) {
        self.resolve_type(arenas, node);
    }

    fn game_type_fn(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<types::FnType<types::GameTypeKind>>,
    ) {
        let fn_ty = arenas.game_type_fn.get(node);
        self.game_type_list(arenas, fn_ty.args);
        self.game_type(arenas, fn_ty.ret_ty);
    }

    fn game_type_tuple(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<
            domino_ast::ast_nodes::types::TupleType<domino_ast::ast_nodes::types::GameTypeKind>,
        >,
    ) {
        let tuple = arenas.game_type_tuple.get(node);
        self.game_type_list(arenas, tuple.0)
    }

    fn game_type_list(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<
            domino_ast::ast_nodes::types::TypeList<domino_ast::ast_nodes::types::GameTypeKind>,
        >,
    ) {
        let list = arenas.game_type_list.get(node);
        for item in list.items.refs() {
            self.game_type(arenas, item)
        }
    }

    fn game_type_app(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<
            domino_ast::ast_nodes::types::ArgumentedType<
                domino_ast::ast_nodes::types::GameTypeKind,
            >,
        >,
    ) {
        let app = arenas.game_type_app.get(node);
        self.resolve_type(arenas, app.name);
        self.game_type_applist(arenas, app.args);
    }

    fn game_type_applist(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<
            domino_ast::ast_nodes::types::TypeArgList<domino_ast::ast_nodes::types::GameTypeKind>,
        >,
    ) {
        let list = arenas.game_type_applist.get(node);

        for item in list.items.refs() {
            self.game_type_arg(arenas, item)
        }
    }

    fn game_type_arg(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<types::TypeArgument<types::GameTypeKind>>,
    ) {
        let arg = arenas.game_type_arg.get(node);
        match *arg {
            types::TypeArgument::Identifier(node) => self.game_type_arg_ident(arenas, node),
            types::TypeArgument::Tuple(node) => self.game_type_applist(arenas, node),
            types::TypeArgument::Application(node) => self.game_type_app(arenas, node),
            types::TypeArgument::Type(node) => self.game_type(arenas, node),
            types::TypeArgument::Expr(node) => self.game_expr(arenas, node),
        }
    }

    fn game_inst_block(&mut self, arenas: &Arenas, node: Ref<game::InstanceBlock>) {
        let inst = arenas.game_inst_block.get(node);

        // Only proceed if the package instance info could be prepared, and the package resolved. If
        // this returns None, a diagnostic that the identifier is None will be emitted.
        if let Some(pkg_inst_info) = self.prepare_pkg_inst_info(arenas, node) {
            self.position = Position::PackageInstance(pkg_inst_info);

            self.resolve_pkg(arenas, inst.instantiated_name);
            self.game_inst_item_list(arenas, inst.items);

            // Consume the resolved package instance and store it
            let pkg_inst_info = self
                .position
                .leave_pkg_instance()
                .expect("in_package_instance was None at the end of resolution process");
            self.declare_game_inst(arenas, node, pkg_inst_info);
        }
    }

    fn game_inst_item_list(&mut self, arenas: &Arenas, node: Ref<game::InstanceItemList>) {
        let list = arenas.game_inst_item_list.get(node);

        list.items
            .refs()
            .for_each(|node| self.game_inst_item(arenas, node));
    }

    fn game_inst_item(&mut self, arenas: &Arenas, node: Ref<game::InstanceItem>) {
        let item = arenas.game_inst_item.get(node);

        match *item {
            instances::InstanceItem::InstanceConst(node) => {
                self.game_inst_const_block(arenas, node)
            }
            instances::InstanceItem::InstanceType(node) => self.game_inst_type_block(arenas, node),
        }
    }

    fn game_inst_const_block(&mut self, arenas: &Arenas, node: Ref<game::InstanceConstBlock>) {
        let block = arenas.game_inst_const_block.get(node);

        self.game_inst_const_item_list(arenas, block.list);
    }

    fn game_inst_const_item_list(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::InstanceConstAssignmentList>,
    ) {
        let list = arenas.game_inst_const_item_list.get(node);

        list.items
            .refs()
            .for_each(|node| self.game_inst_const_item(arenas, node));
    }

    fn game_inst_const_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::InstanceConstAssignmentItem>,
    ) {
        let item = arenas.game_inst_const_item.get(node);

        self.resolve_pkg_const_param(arenas, item.ident);
        self.game_expr(arenas, item.expr);

        let const_name = get_text(item.ident, self.locations, &arenas.source);

        let pkg_inst_info = self.position.pkg_inst_mut().unwrap();

        pkg_inst_info
            .const_assignments
            .insert(const_name.to_string(), node);
    }

    fn game_expr(&mut self, arenas: &Arenas, node: Ref<game::Expression>) {
        let expr = arenas.game_expr.get(node);
        match *expr {
            game::Expression::TableIndex(node) => self.game_expr_tableidx(arenas, node),
            game::Expression::Paren(node) => self.game_expr_paren(arenas, node),
            game::Expression::Tuple(node) => self.game_expr_tuple(arenas, node),
            game::Expression::Call(node) => self.game_expr_call(arenas, node),
            game::Expression::Identifier(node) => {
                self.game_const_value_ident(arenas, node);
                self.resolve_value_ident(arenas, node);
            }
            game::Expression::BinOp(node) => self.game_expr_binop(arenas, node),
            game::Expression::UnOp(node) => self.game_expr_unop(arenas, node),
            game::Expression::Invoke(node) => self.game_expr_invoc(arenas, node),
            game::Expression::Sample(node) => self.game_expr_sample(arenas, node),
            game::Expression::String | game::Expression::Int => {}
        }
    }

    fn compose_block(&mut self, arenas: &Arenas, node: Ref<game::ComposeBlock>) {
        let block = arenas.compose_block.get(node);

        self.compose_pkg_inst_item_list(arenas, block.items);
    }

    fn compose_pkg_inst_item_list(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::ComposePackageInstanceList>,
    ) {
        let list = arenas.compose_pkg_inst_item_list.get(node);

        list.items
            .refs()
            .for_each(|item| self.compose_pkg_inst_item(arenas, item));
    }

    fn compose_pkg_inst_item(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::ComposePackageInstanceItem>,
    ) {
        let item = arenas.compose_pkg_inst_item.get(node);

        if self.resolve_pkg_inst(arenas, item.pkg_inst_name).is_some() {
            self.position = Position::Composition(item.pkg_inst_name);
            self.compose_oracle_item_list(arenas, item.items);
        }
    }

    fn compose_oracle_item_list(
        &mut self,
        arenas: &Arenas,
        node: Ref<game::ComposeOracleAssignmentList>,
    ) {
        let list = arenas.compose_oracle_item_list.get(node);

        list.items
            .refs()
            .for_each(|item| self.compose_oracle_item(arenas, item));
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

        let Position::Composition(left_pkg_inst_name_node) = self.position else {
            unreachable!()
        };

        // XXX: currently both resolve_oracle_in_x functions write into the same side table. These
        //      should either be different ones or append instead of overwrite

        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: &self.locations,
        };

        // resolve caller
        match self.resolve_pkg_inst(arenas, left_pkg_inst_name_node) {
            Some(PackageInstanceResolution::Adversary) => {
                self.tables.oracle_composition_import_names.set(
                    item.oracle_name,
                    OracleCompositionImportResolution::Adversary,
                );
            }

            // Resolve in the oracle name in the caller's imports
            Some(PackageInstanceResolution::PackageInstance(left_inst_ref)) => {
                self.resolve_oracle_import_in_pkg_inst(arenas, item.oracle_name, left_inst_ref);
            }

            Some(PackageInstanceResolution::Error(err)) => todo!("propagate error"),
            None => {
                crate::fail_resolution!(
                    self,
                    item.oracle_name,
                    diag::PackageDoesNotImportOracle::new(
                        dx,
                        item.oracle_name,
                        item.pkg_inst_name,
                        None,
                    ),
                    oracle_composition_import_names,
                    then {}
                );
            }
        }

        // resolve callee
        match self.resolve_pkg_inst(arenas, item.pkg_inst_name) {
            Some(PackageInstanceResolution::PackageInstance(right_inst_ref)) => {
                self.resolve_oracle_definition_in_pkg_inst(
                    arenas,
                    item.oracle_name,
                    right_inst_ref,
                );
            }

            Some(PackageInstanceResolution::Adversary) => {
                crate::fail_resolution!(
                    self,
                    item.oracle_name,
                    diag::AdversaryAsCallee::new(dx, item.oracle_name,),
                    oracle_composition_import_names,
                    then {}
                );
            }
            Some(PackageInstanceResolution::Error(err)) => todo!("propagate error"),
            None => {
                crate::fail_resolution!(
                    self,
                    item.oracle_name,
                    diag::PackageDoesNotDefineOracle::new(
                        dx,
                        item.oracle_name,
                        item.pkg_inst_name,
                        None,
                    ),
                    oracle_composition_def_names,
                    then {}
                );
            }
        }
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
        let ident_name = get_text(ty, &self.locations, &arenas.source);
        self.tables
            .game_type_names
            .set(ty, GameTypeResolution::TypeParam(ty));
        self.scope
            .declare(ident_name, GameDeclaration::TypeParam(ty));
    }

    fn declare_const_param(&mut self, arenas: &Arenas, node: Ref<game::GameConstDecl>) {
        let decl = arenas.game_const_decl.get(node);
        let name = get_text(decl.name, self.locations, &arenas.source);
        self.scope.declare(name, GameDeclaration::GameConst(node));
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
        let decl = arenas.game_inst_block.get(node);
        let name = get_text(info.name, self.locations, &arenas.source);

        let declare_scope_ok = self
            .scope
            .declare(name, GameDeclaration::PackageInstance(info.clone()))
            .is_none();

        let declare_info_ok = self
            .info
            .as_mut()
            .expect("game info not set")
            .instances
            .insert(name.to_string(), info)
            .is_none();

        // ensure that the scope and the info table agree
        debug_assert_eq!(declare_scope_ok, declare_info_ok);

        self.tables.pkg_inst_names.set(
            decl.instance_name,
            PackageInstanceResolution::PackageInstance(node),
        );
    }

    fn prepare_pkg_inst_info(
        &mut self,
        arenas: &Arenas,
        pkg_inst: Ref<game::InstanceBlock>,
    ) -> Option<PackageInstanceInfo> {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: &self.locations,
        };

        let inst = arenas.game_inst_block.get(pkg_inst);
        let name = inst.instance_name;
        let pkg_name = inst.instantiated_name;

        let pkg_name_str = get_text(pkg_name, self.locations, &arenas.source);
        let Some(resolved_pkg) = self.packages.get(pkg_name_str) else {
            // TODO: Also report that we are ignoring the instance because the package is not found?
            //       Maybe not needed.
            crate::fail_resolution!(
                self,
                pkg_name,
                diag::UndefinedIdentifier::new(dx, pkg_name),
                pkg_names,
                then { return None }
            );
        };

        Some(PackageInstanceInfo {
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
            locations: &self.locations,
        };

        let name = get_text(node, &self.locations, &arenas.source);

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
            _ => {
                todo!()
            }
        };

        self.tables.game_type_names.set(node, resolution);
    }

    fn resolve_pkg(&mut self, arenas: &Arenas, node: Ref<identifier::PackageIdentifier>) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: &self.locations,
        };

        let name = get_text(node, &self.locations, &arenas.source);
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
    ) -> Option<PackageInstanceResolution> {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: &self.locations,
        };

        // look up the package instance from the scope
        let name = get_text(node, &self.locations, &arenas.source);

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
                    then { return None }
                );
            };

            // check that the the identifier actually refers to a package instance
            let GameDeclaration::PackageInstance(pkg_inst) = decl else {
                crate::fail_resolution!(
                    self,
                    node,
                    diag::ExpectedPackageInstanceIdentifier::new(dx, node, decl.clone()),
                    pkg_inst_names,
                    then { return None }
                );
            };

            PackageInstanceResolution::PackageInstance(pkg_inst.pkg_inst)
        };

        // set the resolved value in the table
        self.tables.pkg_inst_names.set(node, resolution);

        Some(resolution)
    }

    fn resolve_pkg_const_param(
        &mut self,
        arenas: &Arenas,
        node: Ref<identifier::PackageConstValueIdentifier>,
    ) {
        let dx = domino_diagnostic::Resolver {
            arenas,
            locations: &self.locations,
        };

        // SAFETY: this function is only called when we are inside a package instance block, so this is set
        let pkg_inst_info = self.position.pkg_inst_mut().unwrap();
        let in_package_instance = *arenas.game_inst_block.get(pkg_inst_info.pkg_inst);

        let const_name = get_text(node, &self.locations, &arenas.source);
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
            locations: &self.locations,
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
            locations: &self.locations,
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
            Some(GameDeclaration::PackageConst(_decl)) => todo!("should this even be here?"),

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
    PackageConst(Ref<package::PackageConstDecl>),

    BuiltinValue(BuiltinValue),
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
            GameDeclaration::GameConst(_) => DeclarationType::PureValue,
            GameDeclaration::PackageConst(_) => DeclarationType::PureValue,

            // TODO: Actually, whether this is pure or not depends on whether the inner expression
            //       is pure, but we can't tell that at this point, so we are conservative.
            GameDeclaration::BuiltinValue(BuiltinValue::Some) => DeclarationType::Value,
        }
    }
}
