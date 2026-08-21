use std::collections::HashMap;

use domino_ast::{
    arena::Ref,
    ast_nodes::{identifier, oracles, package, statements, types, Visitor},
    source::SourceLocation,
    Arenas, GlobalTable, PartialDenseTable,
};
use domino_diagnostic::Resolver;

use crate::{
    diag,
    resolutions::{
        self, OracleDefinitionResolution, OracleImportResolution, OracleValueResolution,
        PackageConstValueResolution, PackageTypeArgResolution, PackageTypeResolution,
    },
    scope::*,
    util::*,
    BuiltinType, BuiltinValue, DeclarationType,
};

/// The declaration type used in the [`Scope`]. Has variants for every place that can create a binding.
#[derive(Debug, Clone, Copy)]
enum PackageDeclaration {
    OracleImport(Ref<oracles::OracleSignature<identifier::OracleImportIdentifierKind>>),

    BuiltinType(BuiltinType),
    TypeParam(Ref<identifier::PackageTypeIdentifier>),

    Const(Ref<package::PackageConstDecl>),
    State(Ref<package::PackageConstDecl>),

    OracleArg(Ref<oracles::OracleValueArgDecl>),
    OracleLocal(Ref<statements::AssignStatement>),
    BuiltinValue(BuiltinValue),
}

impl From<BuiltinType> for PackageDeclaration {
    fn from(value: BuiltinType) -> Self {
        Self::BuiltinType(value)
    }
}

impl From<BuiltinValue> for PackageDeclaration {
    fn from(value: BuiltinValue) -> Self {
        Self::BuiltinValue(value)
    }
}

impl crate::Declaration for PackageDeclaration {
    fn decl_type(&self) -> DeclarationType {
        match self {
            PackageDeclaration::OracleImport(_) => DeclarationType::Oracle,

            PackageDeclaration::TypeParam(_) => DeclarationType::Type,
            PackageDeclaration::BuiltinType(_) => DeclarationType::Type,

            PackageDeclaration::BuiltinValue(BuiltinValue::True) => DeclarationType::PureValue,
            PackageDeclaration::BuiltinValue(BuiltinValue::False) => DeclarationType::PureValue,
            PackageDeclaration::BuiltinValue(BuiltinValue::None) => DeclarationType::PureValue,
            PackageDeclaration::Const(_) => DeclarationType::PureValue,
            PackageDeclaration::State(_) => DeclarationType::Value,

            PackageDeclaration::OracleArg(_) => DeclarationType::Value,
            PackageDeclaration::OracleLocal(_) => DeclarationType::Value,

            // TODO: Actually, whether this is pure or not depends on whether the inner expression
            //       is pure, but we can't tell that at this point, so we are conservative.
            PackageDeclaration::BuiltinValue(BuiltinValue::Some) => DeclarationType::Value,
        }
    }
}

impl TryFrom<PackageDeclaration> for PackageConstValueResolution {
    type Error = ();

    fn try_from(decl: PackageDeclaration) -> Result<Self, ()> {
        let resolution = match decl {
            PackageDeclaration::Const(decl) => PackageConstValueResolution::ConstParam(decl),
            PackageDeclaration::BuiltinValue(builtin) => {
                PackageConstValueResolution::Builtin(builtin)
            }

            _ => return Err(()),
        };

        Ok(resolution)
    }
}
impl TryFrom<PackageDeclaration> for OracleValueResolution {
    type Error = ();

    fn try_from(decl: PackageDeclaration) -> Result<Self, ()> {
        let resolution = match decl {
            PackageDeclaration::Const(decl) => OracleValueResolution::Consts(decl),
            PackageDeclaration::State(decl) => OracleValueResolution::State(decl),
            PackageDeclaration::OracleArg(decl) => OracleValueResolution::Arg(decl),
            PackageDeclaration::OracleLocal(assign) => OracleValueResolution::Local(assign),
            PackageDeclaration::BuiltinValue(builtin) => OracleValueResolution::Builtin(builtin),

            _ => return Err(()),
        };

        Ok(resolution)
    }
}

impl TryFrom<PackageDeclaration> for PackageTypeResolution {
    type Error = ();

    fn try_from(decl: PackageDeclaration) -> Result<Self, ()> {
        let resolution = match decl {
            PackageDeclaration::TypeParam(decl) => PackageTypeResolution::TypeParam(decl),
            PackageDeclaration::BuiltinType(builtin) => PackageTypeResolution::Builtin(builtin),

            _ => return Err(()),
        };

        Ok(resolution)
    }
}

impl TryFrom<PackageDeclaration> for PackageTypeArgResolution {
    type Error = ();

    fn try_from(decl: PackageDeclaration) -> Result<Self, ()> {
        let resolution = match decl {
            PackageDeclaration::TypeParam(decl) => PackageTypeArgResolution::TypeParam(decl),
            PackageDeclaration::BuiltinType(builtin) => PackageTypeArgResolution::Builtin(builtin),
            PackageDeclaration::Const(decl) => PackageTypeArgResolution::Consts(decl),

            _ => return Err(()),
        };

        Ok(resolution)
    }
}

// XXX: These probably all need custom resolution types with error variants
//      and also make sure that everything that needs it has acess to builtins
#[derive(Debug)]
pub struct PartialPackagedIdentifierResolution<'a> {
    pub pkg_names:
        &'a mut PartialDenseTable<identifier::PackageIdentifier, resolutions::PackageResolution>,
    pub oracle_def_names: &'a mut PartialDenseTable<
        identifier::OracleDefinitionIdentifier,
        OracleDefinitionResolution,
    >,
    pub oracle_import_names:
        &'a mut PartialDenseTable<identifier::OracleImportIdentifier, OracleImportResolution>,
    pub const_value_names: &'a mut PartialDenseTable<
        identifier::PackageConstValueIdentifier,
        resolutions::PackageConstValueResolution,
    >,
    pub oracle_value_names:
        &'a mut PartialDenseTable<identifier::OracleValueIdentifier, OracleValueResolution>,
    pub type_names:
        &'a mut PartialDenseTable<identifier::PackageTypeIdentifier, PackageTypeResolution>,
    pub type_arg_names: &'a mut PartialDenseTable<
        identifier::PackageTypeArgumentIdentifier,
        PackageTypeArgResolution,
    >,
    pub is_state: &'a mut PartialDenseTable<package::PackageConstDecl, bool>,
}

#[derive(Debug, Clone)]
pub struct PackageInfo {
    pub pkg: Ref<package::Package>,
    pub name: Ref<identifier::PackageIdentifier>,
    pub const_params: HashMap<String, Ref<package::PackageConstDecl>>,
    pub type_params: HashMap<String, Ref<identifier::PackageTypeIdentifier>>,
    pub state: HashMap<String, Ref<package::PackageConstDecl>>,
    pub oracle_imports:
        HashMap<String, Ref<oracles::OracleSignature<identifier::OracleImportIdentifierKind>>>,
    pub oracle_definitions: HashMap<String, Ref<oracles::OracleDefinition>>,
}

impl PackageInfo {
    fn new(pkg: Ref<package::Package>, name: Ref<identifier::PackageIdentifier>) -> Self {
        Self {
            pkg,
            name,

            const_params: Default::default(),
            type_params: Default::default(),
            state: Default::default(),
            oracle_imports: Default::default(),
            oracle_definitions: Default::default(),
        }
    }
}

#[derive(Debug)]
pub struct PackageVisitor<'a> {
    locations: &'a GlobalTable<SourceLocation>,

    diagnostics: &'a mut diag::Diagnostics,
    info: &'a mut Option<PackageInfo>,
    tables: PartialPackagedIdentifierResolution<'a>,

    scope: Scope<PackageDeclaration>,

    /// This is a bit of a hack. When in a visitor function of a constant/state declaration block,
    /// we can't distinguish between the two. so we set a flag when entering state an immediate
    /// clear it. we then tag all state declaration with a flag, so we know they are mutable.
    ///
    /// actually maybe the other way around makes more sense? we'll see.
    inside_state: bool,
}

impl<'a> PackageVisitor<'a> {
    pub fn new(
        locations: &'a GlobalTable<SourceLocation>,
        diagnostics: &'a mut diag::Diagnostics,
        tables: PartialPackagedIdentifierResolution<'a>,
        info: &'a mut Option<PackageInfo>,
    ) -> Self {
        let scope = Scope::new();
        let inside_state = false;

        Self {
            locations,
            scope,
            inside_state,

            info,
            tables,
            diagnostics,
        }
    }
}

impl<'a> domino_ast::Visitor for PackageVisitor<'a> {
    fn package(&mut self, arenas: &Arenas, node: Ref<package::Package>) {
        let package = arenas.package.get(node);

        *self.info = Some(PackageInfo::new(node, package.name));
        self.tables
            .pkg_names
            .set(package.name, resolutions::PackageResolution::Package(node));

        self.scope.enter();
        self.pkg_item_list(arenas, package.items);
        self.scope.leave();
    }

    // here we process these ordered by type, so you can use a constant before it was declared
    fn pkg_item_list(&mut self, arenas: &Arenas, node: Ref<package::PackageItemList>) {
        let mut type_params = vec![];
        let mut const_params = vec![];
        let mut state = vec![];
        let mut imports = vec![];
        let mut oracles = vec![];

        for item in arenas.pkg_item_list.get(node).items.refs() {
            match arenas.pkg_item.get(item) {
                package::PackageItem::TypeParams(_) => type_params.push(item),
                package::PackageItem::ConstParams(_) => const_params.push(item),
                package::PackageItem::State(_) => state.push(item),
                package::PackageItem::ImportOracles(_) => imports.push(item),
                package::PackageItem::OracleDefinition(_) => oracles.push(item),
            }
        }

        type_params
            .into_iter()
            .chain(const_params)
            .chain(state)
            .chain(imports)
            .chain(oracles)
            .for_each(|node| self.pkg_item(arenas, node));
    }

    fn pkg_type_decl_list(&mut self, arenas: &Arenas, node: Ref<package::PackageTypeDeclList>) {
        arenas
            .pkg_type_decl_list
            .get(node)
            .items
            .refs()
            .for_each(|type_name| {
                let name = get_text(type_name, self.locations, &arenas.source);
                self.info
                    .as_mut()
                    .unwrap()
                    .type_params
                    .insert(name.to_string(), type_name);
                self.scope
                    .declare(name, PackageDeclaration::TypeParam(type_name));
                self.tables
                    .type_names
                    .set(type_name, PackageTypeResolution::TypeParam(type_name));
            })
    }

    fn pkg_const_param_block(
        &mut self,
        arenas: &Arenas,
        node: Ref<package::PackageConstParamBlock>,
    ) {
        let const_block = arenas.pkg_const_param_block.get(node);

        // This should really only be set inside state blocks. If it is set here, something is wrong!
        debug_assert!(!self.inside_state);

        self.pkg_const_decl_list(arenas, const_block.decls);
    }

    fn state_block(&mut self, arenas: &Arenas, node: Ref<package::StateBlock>) {
        let state_block = arenas.state_block.get(node);

        self.inside_state = true;
        self.pkg_const_decl_list(arenas, state_block.decls);
        self.inside_state = false;
    }

    fn pkg_type_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::PackageTypeIdentifier>,
    ) {
        self.resolve_type_ident(arenas, node)
    }

    fn pkg_type_arg_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::PackageTypeArgumentIdentifier>,
    ) {
        self.resolve_type_arg_ident(arenas, node);
    }

    fn package_type_list(
        &mut self,
        arenas: &Arenas,
        node: Ref<types::TypeList<types::PackageTypeKind>>,
    ) {
        let tys = arenas.package_type_list.get(node);
        tys.items
            .refs()
            .for_each(|node| self.package_type(arenas, node));
    }

    // TODO: change the AST types to have a separate declaration for State, even though it is the
    //       same structureally. This allows me to drop the flag and the is_state side table.
    //       It might also make resolution simpler, because we don't need to check the side table
    //       for whether we are allowed to write there
    fn pkg_const_decl(&mut self, arenas: &Arenas, node: Ref<package::PackageConstDecl>) {
        let decl = arenas.pkg_const_decl.get(node);
        let name = get_text(decl.name, self.locations, &arenas.source);
        self.package_type(arenas, decl.ty);

        if self.inside_state {
            self.info
                .as_mut()
                .unwrap()
                .state
                .insert(name.to_string(), node);
            self.scope.declare(name, PackageDeclaration::State(node));
        } else {
            self.info
                .as_mut()
                .unwrap()
                .const_params
                .insert(name.to_string(), node);
            self.scope.declare(name, PackageDeclaration::Const(node));
        }

        self.tables.const_value_names.set(
            decl.name,
            resolutions::PackageConstValueResolution::ConstParam(node),
        );
        self.tables.is_state.set(node, self.inside_state);
    }

    fn pkg_const_value_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::PackageConstValueIdentifier>,
    ) {
        self.resolve_pkg_const_value_ident(arenas, node);
    }

    fn import_oracle_block(&mut self, arenas: &Arenas, node: Ref<package::ImportOraclesBlock>) {
        let decls = arenas.import_oracle_block.get(node).decls;
        arenas
            .oracle_decl_list
            .get(decls)
            .items
            .refs()
            .for_each(|node| {
                self.oracle_import_sig(arenas, node);

                let sig = arenas.oracle_import_sig.get(node);
                let name = get_text(sig.name, self.locations, &arenas.source);

                self.info
                    .as_mut()
                    .unwrap()
                    .oracle_imports
                    .insert(name.to_string(), node);
                self.scope
                    .declare(name, PackageDeclaration::OracleImport(node));
                self.tables
                    .oracle_import_names
                    .set(sig.name, OracleImportResolution::Import(node));
            });
    }

    fn oracle_def(&mut self, arenas: &Arenas, node: Ref<oracles::OracleDefinition>) {
        let oracle_def = arenas.oracle_def.get(node);
        let oracle_sig = arenas.oracle_def_sig.get(oracle_def.oracle_sig);
        let args = arenas.oracle_value_decl_list.get(oracle_sig.args);

        let name = get_text(oracle_sig.name, self.locations, &arenas.source);
        self.info
            .as_mut()
            .unwrap()
            .oracle_definitions
            .insert(name.to_string(), node);
        self.oracle_def_sig(arenas, oracle_def.oracle_sig);
        self.tables.oracle_def_names.set(
            oracle_sig.name,
            OracleDefinitionResolution::Definition(node),
        );

        // enter before declaring oracle args
        self.scope.enter();
        args.items
            .refs()
            .for_each(|arg_decl_ref| self.declare_oracle_arg(arenas, arg_decl_ref));
        self.stmt_list(arenas, oracle_def.statements);
        self.scope.leave();
    }

    fn oracle_value_arg_decl(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<oracles::OracleValueArgDecl>,
    ) {
        let arg = arenas.oracle_value_arg_decl.get(node);
        // DON'T recurse into the name child node here, as that would try resolving
        // instead of declaring.
        self.package_type(arenas, arg.ty);
    }

    fn stmt_assign(&mut self, arenas: &Arenas, node: Ref<statements::AssignStatement>) {
        let stmt = arenas.stmt_assign.get(node);

        // DON'T recurse into the pat child node here, as that would try resolving
        // instead of declaring.
        self.oracle_expr(arenas, stmt.expr);

        self.pat_set_assign(arenas, stmt.pat, node);
    }

    fn stmt_ite(&mut self, arenas: &Arenas, node: Ref<statements::IfThenElseStatement>) {
        let stmt = arenas.stmt_ite.get(node);
        self.oracle_expr(arenas, stmt.cond);

        self.scope.enter();
        self.stmt_list(arenas, stmt.then_block);
        self.scope.leave();

        if let Some(else_block) = stmt.else_block {
            self.scope.enter();
            self.stmt_list(arenas, else_block.block);
            self.scope.leave();
        }
    }

    fn oracle_value_ident(
        &mut self,
        arenas: &domino_ast::Arenas,
        node: domino_ast::arena::Ref<identifier::OracleValueIdentifier>,
    ) {
        self.resolve_oracle_value_ident(arenas, node);
    }

    fn oracle_expr_invoc(
        &mut self,
        arenas: &Arenas,
        node: Ref<oracles::OracleInvocationExpression>,
    ) {
        let expr = arenas.oracle_expr_invoc.get(node);
        self.resolve_oracle_import(arenas, expr.oracle_name);

        let args = arenas.oracle_expr_list.get(expr.args);
        args.items
            .refs()
            .for_each(|node| self.oracle_expr(arenas, node));
    }

    // ignore trivia
    fn trivia(
        &mut self,
        _arenas: &domino_ast::Arenas,
        _node: domino_ast::arena::Ref<domino_ast::ast_nodes::Trivia>,
    ) {
    }
}

impl<'a> PackageVisitor<'a> {
    fn declare_oracle_arg(&mut self, arenas: &Arenas, decl_ref: Ref<oracles::OracleValueArgDecl>) {
        let decl = arenas.oracle_value_arg_decl.get(decl_ref);
        let ident_name = get_text(decl.name, &self.locations, &arenas.source);

        self.tables
            .oracle_value_names
            .set(decl.name, OracleValueResolution::Arg(decl_ref));
        self.scope
            .declare(ident_name, PackageDeclaration::OracleArg(decl_ref));
    }

    fn resolve_oracle_import(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::OracleImportIdentifier>,
    ) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);

        let Some(decl) = self.scope.lookup(ident_name).copied() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::UndefinedIdentifier::new(dx, ident),
                oracle_import_names
            );
        };

        let PackageDeclaration::OracleImport(import) = decl else {
            crate::fail_resolution!(
                self,
                ident,
                diag::ExpectedOracleIdentifier::new(dx, ident, decl),
                oracle_import_names
            );
        };

        self.tables
            .oracle_import_names
            .set(ident, OracleImportResolution::Import(import));
    }

    /// indexes a value identifier in an expression (i.e. "right of an assignment arrow").
    /// If the Identifier is not declared yet, that is an error.
    fn resolve_oracle_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::OracleValueIdentifier>,
    ) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);
        let Some(decl) = self.scope.lookup(ident_name).copied() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::UndefinedIdentifier::new(dx, ident),
                oracle_value_names
            );
        };

        let Ok(resolution) = decl.try_into() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::ExpectedValueIdentifier::new(dx, ident, decl),
                oracle_value_names
            );
        };

        self.tables.oracle_value_names.set(ident, resolution);
    }

    fn resolve_type_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::PackageTypeIdentifier>,
    ) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);
        let Some(decl) = self.scope.lookup(ident_name).copied() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::UndefinedIdentifier::new(dx, ident),
                type_names
            );
        };

        let Ok(resolution) = decl.try_into() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::ExpectedTypeIdentifier::new(dx, ident, decl),
                type_names
            );
        };

        self.tables.type_names.set(ident, resolution);
    }

    fn resolve_pkg_const_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::PackageConstValueIdentifier>,
    ) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);

        let Some(decl) = self.scope.lookup(ident_name).copied() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::UndefinedIdentifier::new(dx, ident),
                const_value_names
            );
        };

        let Ok(resolution) = decl.try_into() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::ExpectedConstValueIdentifier::new(dx, ident, decl),
                const_value_names
            );
        };

        self.tables.const_value_names.set(ident, resolution);
    }

    fn resolve_type_arg_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::PackageTypeArgumentIdentifier>,
    ) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);

        let Some(decl) = self.scope.lookup(ident_name).copied() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::UndefinedIdentifier::new(dx, ident),
                type_arg_names
            );
        };

        let Ok(resolution) = decl.try_into() else {
            crate::fail_resolution!(
                self,
                ident,
                diag::ExpectedTypeArgIdentifier::new(dx, ident, decl),
                type_arg_names
            );
        };

        self.tables.type_arg_names.set(ident, resolution);
    }

    /// Indexes an identifier in a pattern, i.e. that is being assigned a value.
    /// If it is not declared yet, that is not an error.
    fn resolve_or_declare_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::OracleValueIdentifier>,
        assign: Ref<statements::AssignStatement>,
    ) {
        let dx = Resolver {
            arenas,
            locations: &self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);
        let Some(decl) = self.scope.lookup(ident_name).copied() else {
            self.tables
                .oracle_value_names
                .set(ident, OracleValueResolution::Local(assign));
            self.scope
                .declare(ident_name, PackageDeclaration::OracleLocal(assign));
            return;
        };

        let Ok(resolution) = decl.try_into() else {
            let diag_ref = self
                .diagnostics
                .alloc(diag::ExpectedValueIdentifier::new(dx, ident, decl).into());
            self.tables
                .oracle_value_names
                .set(ident, OracleValueResolution::Error(diag_ref));
            return;
        };

        // don't allow assigning to constant or builtin
        match resolution {
            OracleValueResolution::Consts(_) | OracleValueResolution::Builtin(_) => {
                // dropping the ref here is fine, we don't need it because resolution itself
                // succeeded.
                self.diagnostics
                    .alloc(diag::AssignToConst::new(dx, ident).into());
            }
            _ => {}
        }

        self.tables.oracle_value_names.set(ident, resolution);
    }

    /// This is basically a custom override of the pat visitor, but one that has the assign as an
    /// additional argument. This allows us propagate the assign node throughout the recursion.
    fn pat_set_assign(
        &mut self,
        arenas: &Arenas,
        pat: Ref<statements::Pattern>,
        assign: Ref<statements::AssignStatement>,
    ) {
        match *arenas.pat.get(pat) {
            statements::Pattern::Identifier(ident) => {
                self.resolve_or_declare_value_ident(arenas, ident, assign)
            }
            statements::Pattern::Table(tab_ref) => {
                let tab = arenas.pat_table.get(tab_ref);
                self.resolve_or_declare_value_ident(arenas, tab.table_name, assign);
                self.oracle_expr(arenas, tab.index);
            }
            statements::Pattern::Tuple(tup_ref) => {
                let tup = arenas.pat_tuple.get(tup_ref);
                let items = arenas.pat_list.get(tup.items);
                items.items.refs().for_each(|pat| {
                    self.pat_set_assign(arenas, pat, assign);
                });
            }
        }
    }
}
