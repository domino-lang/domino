use domino_ast::{
    arena::{Arena, Ref},
    ast_nodes::{
        expressions, identifier, oracles, package,
        statements::{self, AssignStatement},
        types, NodeType, Visitor,
    },
    source::{SourceFile, SourceLocation},
    Arenas, DenseTable, GlobalTable,
};
use domino_diagnostic::Resolver;

use crate::{diag, scope::*, BuiltinType, BuiltinValue, Declaration};

#[derive(Debug, Clone, Copy)]
pub enum OracleDeclaration {
    Import(Ref<oracles::OracleSignature>),
    Definition(Ref<oracles::OracleDefinition>),
}

#[derive(Debug, Clone, Copy)]
pub enum OracleValueDeclaration {
    State(Ref<package::PackageConstDecl>),
    Consts(Ref<package::PackageConstDecl>),
    Arg(Ref<oracles::OracleValueArgDecl>),
    Local(Ref<statements::AssignStatement>),
    Builtin(BuiltinValue),
}

#[derive(Debug, Clone, Copy)]
pub enum TypeDeclaration {
    TypeParam(Ref<identifier::PackageTypeIdentifier>),
    Builtin(BuiltinType),
}

#[derive(Debug, Clone, Copy)]
pub enum TypeArgDeclaration {
    TypeParam(Ref<identifier::PackageTypeIdentifier>),
    Consts(Ref<package::PackageConstDecl>),
    Builtin(BuiltinType),
}

pub struct PackageVisitor<'a> {
    locations: &'a GlobalTable<SourceLocation>,
    scope: Scope,

    pub package_names: DenseTable<identifier::PackageIdentifier, Option<Ref<package::Package>>>,
    pub oracle_names: DenseTable<identifier::OracleIdentifier, Option<OracleDeclaration>>,
    pub const_value_names:
        DenseTable<identifier::PackageConstValueIdentifier, Option<Ref<package::PackageConstDecl>>>,
    pub oracle_value_names:
        DenseTable<identifier::OracleValueIdentifier, Option<OracleValueDeclaration>>,
    pub type_names: DenseTable<identifier::PackageTypeIdentifier, Option<TypeDeclaration>>,
    pub type_arg_names:
        DenseTable<identifier::PackageTypeArgumentIdentifier, Option<TypeArgDeclaration>>,

    pub diagnostics: Vec<diag::Diagnostic>,

    pub is_state: DenseTable<package::PackageConstDecl, Option<bool>>,

    /// This is a bit of a hack. When in a visitor function of a constant/state declaration block, we can't distinguish between the two. so we set a flag when entering state an immediate clear it. we then tag all state declaration with a flag, so we know they are mutable.
    ///
    /// actually maybe the other way around makes more sense? we'll see.
    pub inside_state: bool,
}

impl<'a> PackageVisitor<'a> {
    pub fn new(arenas: &Arenas, locations: &'a GlobalTable<SourceLocation>) -> Self {
        let scope = Scope::new();

        let package_names = DenseTable::with_entries(arenas.pkg_ident.len());
        let oracle_names = DenseTable::with_entries(arenas.oracle_ident.len());
        let const_value_names = DenseTable::with_entries(arenas.pkg_const_value_ident.len());
        let oracle_value_names = DenseTable::with_entries(arenas.oracle_value_ident.len());
        let type_names = DenseTable::with_entries(arenas.pkg_type_ident.len());
        let type_arg_names = DenseTable::with_entries(arenas.pkg_type_arg_ident.len());

        let is_state = DenseTable::with_entries(arenas.pkg_const_decl.len());
        let diagnostics = vec![];

        let inside_state = false;

        Self {
            locations,
            scope,

            package_names,
            oracle_names,
            const_value_names,
            oracle_value_names,
            type_names,
            type_arg_names,

            diagnostics,
            is_state,

            inside_state,
        }
    }
}

fn get_text<'a, T: NodeType>(
    node: Ref<T>,
    locations: &GlobalTable<SourceLocation>,
    source_arena: &'a Arena<SourceFile>,
) -> &'a str {
    let loc = *locations.get(&node.global_ref_id()).unwrap();
    source_arena.text(loc)
}

impl<'a> domino_ast::Visitor for PackageVisitor<'a> {
    fn package(&mut self, arenas: &Arenas, node: Ref<package::Package>) {
        let package = arenas.package.get(node);
        let package_name = get_text(package.name, self.locations, &arenas.source);

        self.scope.declare(package_name, Declaration::Package(node));
        self.package_names.set(package.name, node);

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

    fn pkg_item(&mut self, arenas: &Arenas, node: Ref<package::PackageItem>) {
        match *arenas.pkg_item.get(node) {
            package::PackageItem::TypeParams(node) => self.pkg_type_param_block(arenas, node),
            package::PackageItem::ConstParams(node) => self.pkg_const_param_block(arenas, node),
            package::PackageItem::State(node) => self.state_block(arenas, node),
            package::PackageItem::ImportOracles(node) => self.import_oracle_block(arenas, node),
            package::PackageItem::OracleDefinition(node) => self.oracle_def(arenas, node),
        }
    }

    fn pkg_type_param_block(&mut self, arenas: &Arenas, node: Ref<package::PackageTypeParamBlock>) {
        let type_block = arenas.pkg_type_param_block.get(node);

        self.pkg_type_decl_list(arenas, type_block.decls);
    }

    fn pkg_type_decl_list(&mut self, arenas: &Arenas, node: Ref<package::PackageTypeDeclList>) {
        arenas
            .pkg_type_decl_list
            .get(node)
            .items
            .refs()
            .for_each(|type_name| {
                let name = get_text(type_name, self.locations, &arenas.source);
                self.scope.declare(name, Declaration::TypeParam(type_name));
                self.type_names
                    .set(type_name, TypeDeclaration::TypeParam(type_name));
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

    fn package_type(&mut self, arenas: &Arenas, node: Ref<types::Type<types::PackageTypeKind>>) {
        let ty = arenas.package_type.get(node);
        match *ty {
            types::Type::Identifier(node) => {
                self.pkg_type_ident(arenas, node);
                self.resolve_type_ident(arenas, node)
            }
            types::Type::Tuple(node) => self.package_type_tuple(arenas, node),
            types::Type::Argumented(node) => self.package_type_app(arenas, node),
            types::Type::Fn(node) => self.package_type_fn(arenas, node),
        }
    }

    fn package_type_tuple(
        &mut self,
        arenas: &Arenas,
        node: Ref<types::TupleType<types::PackageTypeKind>>,
    ) {
        let ty = arenas.package_type_tuple.get(node);
        self.package_type_list(arenas, ty.0);
    }

    fn package_type_app(
        &mut self,
        arenas: &Arenas,
        node: Ref<types::ArgumentedType<types::PackageTypeKind>>,
    ) {
        let ty = arenas.package_type_app.get(node);
        self.resolve_type_ident(arenas, ty.name);
        self.package_type_applist(arenas, ty.args);
    }

    fn package_type_applist(
        &mut self,
        arenas: &Arenas,
        node: Ref<types::TypeArgList<types::PackageTypeKind>>,
    ) {
        let ty = arenas.package_type_applist.get(node);
        ty.items
            .refs()
            .for_each(|node| self.package_type_arg(arenas, node));
    }

    fn package_type_arg(
        &mut self,
        arenas: &Arenas,
        node: Ref<types::TypeArgument<types::PackageTypeKind>>,
    ) {
        let ty_arg = arenas.package_type_arg.get(node);
        match *ty_arg {
            types::TypeArgument::Identifier(ident) => self.resolve_type_arg_ident(arenas, ident),
            types::TypeArgument::Tuple(node) => self.package_type_applist(arenas, node),
            types::TypeArgument::Application(node) => self.package_type_app(arenas, node),
            types::TypeArgument::Type(node) => self.package_type(arenas, node),
            types::TypeArgument::Expr(node) => self.pkg_expr(arenas, node),
        }
    }

    fn package_type_fn(
        &mut self,
        arenas: &Arenas,
        node: Ref<types::FnType<types::PackageTypeKind>>,
    ) {
        let ty = arenas.package_type_fn.get(node);

        self.package_type(arenas, ty.ret_ty);
        self.package_type_list(arenas, ty.args);
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

    fn pkg_const_decl_list(&mut self, arenas: &Arenas, node: Ref<package::PackageConstDeclList>) {
        arenas
            .pkg_const_decl_list
            .get(node)
            .items
            .refs()
            .for_each(|node| self.pkg_const_decl(arenas, node))
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
            self.scope.declare(name, Declaration::State(node));
        } else {
            self.scope.declare(name, Declaration::Const(node));
        }

        self.const_value_names.set(decl.name, node);
        self.is_state.set(node, self.inside_state);
    }

    fn import_oracle_block(&mut self, arenas: &Arenas, node: Ref<package::ImportOraclesBlock>) {
        let decls = arenas.import_oracle_block.get(node).decls;
        arenas
            .oracle_decl_list
            .get(decls)
            .items
            .refs()
            .for_each(|node| {
                self.oracle_sig(arenas, node);

                let sig = arenas.oracle_sig.get(node);
                let name = get_text(sig.name, self.locations, &arenas.source);

                self.scope.declare(name, Declaration::OracleImport(node));
                self.oracle_names
                    .set(sig.name, OracleDeclaration::Import(node));
            });
    }

    /// NB: The arguments and oracle name of a definition are declared and indexed in
    /// [`Self::oracle_def`], because this function here is also called for imports, and we don't
    /// want to index the arguments of oracle imports.
    fn oracle_sig(&mut self, arenas: &Arenas, node: Ref<oracles::OracleSignature>) {
        let sig = arenas.oracle_sig.get(node);
        self.oracle_value_decl_list(arenas, sig.args);
        if let Some(oracle_ret_ty) = sig.ret_ty {
            self.package_type(arenas, oracle_ret_ty.ty);
        }
    }

    fn oracle_value_decl_list(&mut self, arenas: &Arenas, node: Ref<oracles::OracleValueDeclList>) {
        let args = arenas.oracle_value_decl_list.get(node);
        args.items
            .refs()
            .for_each(|arg_decl_ref| self.oracle_value_arg_decl(arenas, arg_decl_ref));
    }

    fn oracle_value_arg_decl(&mut self, arenas: &Arenas, node: Ref<oracles::OracleValueArgDecl>) {
        let arg = arenas.oracle_value_arg_decl.get(node);
        self.package_type(arenas, arg.ty);
    }

    fn oracle_def(&mut self, arenas: &Arenas, node: Ref<oracles::OracleDefinition>) {
        let oracle_def = arenas.oracle_def.get(node);
        let oracle_sig = arenas.oracle_sig.get(oracle_def.oracle_sig);
        let args = arenas.oracle_value_decl_list.get(oracle_sig.args);

        self.oracle_sig(arenas, oracle_def.oracle_sig);
        self.oracle_names
            .set(oracle_sig.name, OracleDeclaration::Definition(node));

        // enter before declaring oracle args
        self.scope.enter();
        args.items
            .refs()
            .for_each(|arg_decl_ref| self.declare_oracle_arg(arenas, arg_decl_ref));
        self.stmt_list(arenas, oracle_def.statements);
        self.scope.leave();
    }

    fn stmt_list(&mut self, arenas: &Arenas, node: Ref<statements::StatementList>) {
        arenas
            .stmt_list
            .get(node)
            .items
            .refs()
            .for_each(|node| self.stmt(arenas, node));
    }

    fn stmt(&mut self, arenas: &Arenas, node: Ref<statements::Statement>) {
        match *arenas.stmt.get(node) {
            statements::Statement::Abort => { /* nothing to do */ }
            statements::Statement::Assert(node) => self.stmt_assert(arenas, node),
            statements::Statement::Assign(node) => self.stmt_assign(arenas, node),
            statements::Statement::Expression(node) => self.stmt_expr(arenas, node),
            statements::Statement::IfThenElse(node) => self.stmt_ite(arenas, node),
            statements::Statement::Return(node) => self.stmt_ret(arenas, node),
        }
    }

    fn stmt_assert(&mut self, arenas: &Arenas, node: Ref<statements::AssertStatement>) {
        let assert = arenas.stmt_assert.get(node);
        self.oracle_expr(arenas, assert.expr);
    }

    fn stmt_assign(&mut self, arenas: &Arenas, node: Ref<statements::AssignStatement>) {
        let stmt = arenas.stmt_assign.get(node);

        self.pat(arenas, stmt.pat);
        self.oracle_expr(arenas, stmt.expr);

        self.pat_set_assign(arenas, stmt.pat, node);
    }

    fn stmt_expr(&mut self, arenas: &Arenas, node: Ref<statements::ExpressionStatement>) {
        let stmt = arenas.stmt_expr.get(node);
        self.oracle_expr(arenas, stmt.expr);
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

    fn stmt_ret(&mut self, arenas: &Arenas, node: Ref<statements::ReturnStatement>) {
        let stmt = arenas.stmt_ret.get(node);
        self.oracle_expr(arenas, stmt.expr);
    }

    fn oracle_expr(&mut self, arenas: &Arenas, node: Ref<oracles::OracleExpression>) {
        let expr = arenas.oracle_expr.get(node);
        match *expr {
            expressions::Expression::TableIndex(node) => self.oracle_expr_tableidx(arenas, node),
            expressions::Expression::Paren(node) => self.oracle_expr_paren(arenas, node),
            expressions::Expression::Tuple(node) => self.oracle_expr_tuple(arenas, node),
            expressions::Expression::Call(node) => self.oracle_expr_call(arenas, node),
            expressions::Expression::Identifier(node) => {
                self.oracle_value_ident(arenas, node);
                self.resolve_value_ident(arenas, node);
            }
            expressions::Expression::BinOp(node) => self.oracle_expr_binop(arenas, node),
            expressions::Expression::UnOp(node) => self.oracle_expr_unop(arenas, node),
            expressions::Expression::Invoke(node) => self.oracle_expr_invoc(arenas, node),
            expressions::Expression::Sample(node) => self.oracle_expr_sample(arenas, node),
            expressions::Expression::String | expressions::Expression::Int => {}
        }
    }

    fn oracle_expr_tableidx(&mut self, arenas: &Arenas, node: Ref<oracles::TableIndexExpression>) {
        let expr = arenas.oracle_expr_tableidx.get(node);
        self.resolve_value_ident(arenas, expr.table_name);
        self.oracle_expr(arenas, expr.index);
    }

    fn oracle_expr_paren(&mut self, arenas: &Arenas, node: Ref<oracles::ParenExpression>) {
        let expr = arenas.oracle_expr_paren.get(node);
        self.oracle_expr(arenas, expr.expr);
    }

    fn oracle_expr_tuple(&mut self, arenas: &Arenas, node: Ref<oracles::TupleExpression>) {
        let expr = arenas.oracle_expr_tuple.get(node);
        let items = arenas.oracle_expr_list.get(expr.0);
        items
            .items
            .refs()
            .for_each(|node| self.oracle_expr(arenas, node));
    }

    fn oracle_expr_call(&mut self, arenas: &Arenas, node: Ref<oracles::CallExpression>) {
        let expr = arenas.oracle_expr_call.get(node);
        self.oracle_expr(arenas, expr.name);

        let items = arenas.oracle_expr_list.get(expr.args);
        items
            .items
            .refs()
            .for_each(|node| self.oracle_expr(arenas, node));
    }

    fn oracle_expr_binop(&mut self, arenas: &Arenas, node: Ref<oracles::BinOpExpression>) {
        let expr = arenas.oracle_expr_binop.get(node);
        self.oracle_expr(arenas, expr.lhs);
        self.oracle_expr(arenas, expr.rhs);
    }

    fn oracle_expr_unop(&mut self, arenas: &Arenas, node: Ref<oracles::UnOpExpression>) {
        let expr = arenas.oracle_expr_unop.get(node);
        self.oracle_expr(arenas, expr.expr);
    }

    fn oracle_expr_sample(&mut self, arenas: &Arenas, node: Ref<oracles::SampleExpression>) {
        let expr = arenas.oracle_expr_sample.get(node);
        self.package_type(arenas, expr.ty);
    }

    fn oracle_expr_invoc(
        &mut self,
        arenas: &Arenas,
        node: Ref<oracles::OracleInvocationExpression>,
    ) {
        let expr = arenas.oracle_expr_invoc.get(node);
        self.resolve_oracle_ident(arenas, expr.oracle_name);

        let args = arenas.oracle_expr_list.get(expr.args);
        args.items
            .refs()
            .for_each(|node| self.oracle_expr(arenas, node));
    }
}

impl<'a> PackageVisitor<'a> {
    fn declare_oracle_arg(&mut self, arenas: &Arenas, decl_ref: Ref<oracles::OracleValueArgDecl>) {
        let decl = arenas.oracle_value_arg_decl.get(decl_ref);
        let ident_name = get_text(decl.name, &self.locations, &arenas.source);

        self.oracle_value_names
            .set(decl.name, OracleValueDeclaration::Arg(decl_ref));
        self.scope
            .declare(ident_name, Declaration::OracleArg(decl_ref));
    }

    fn resolve_oracle_ident(&mut self, arenas: &Arenas, ident: Ref<identifier::OracleIdentifier>) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);
        if let Some(decl) = self.scope.lookup(ident_name) {
            match *decl {
                Declaration::OracleImport(import) => {
                    self.oracle_names
                        .set(ident, OracleDeclaration::Import(import));
                }

                other_decl => self
                    .diagnostics
                    .push(diag::ExpectedOracleIdentifier::new(dx, ident, other_decl).into()),
            }
        } else {
            self.diagnostics
                .push(diag::UndefinedIdentifier::new(dx, ident).into())
        }
    }

    /// indexes a value identifier in an expression (i.e. "right of an assignment arrow").
    /// If the Identifier is not declared yet, that is an error.
    fn resolve_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::OracleValueIdentifier>,
    ) {
        let dx = Resolver {
            arenas,
            locations: self.locations,
        };

        let ident_name = get_text(ident, self.locations, &arenas.source);
        if let Some(decl) = self.scope.lookup(ident_name) {
            match *decl {
                Declaration::Const(decl) => {
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::Consts(decl));
                }
                Declaration::State(decl) => {
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::State(decl));
                }
                Declaration::OracleArg(decl) => {
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::Arg(decl));
                }
                Declaration::OracleLocal(assign) => self
                    .oracle_value_names
                    .set(ident, OracleValueDeclaration::Local(assign)),
                Declaration::BuiltinValue(builtin) => self
                    .oracle_value_names
                    .set(ident, OracleValueDeclaration::Builtin(builtin)),
                other_decl => {
                    self.diagnostics
                        .push(diag::ExpectedValueIdentifier::new(dx, ident, other_decl).into());
                }
            }
        } else {
            self.diagnostics
                .push(diag::UndefinedIdentifier::new(dx, ident).into())
        }
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
        if let Some(decl) = self.scope.lookup(ident_name) {
            match *decl {
                Declaration::TypeParam(decl) => {
                    self.type_names.set(ident, TypeDeclaration::TypeParam(decl));
                }
                Declaration::BuiltinType(builtin) => {
                    self.type_names
                        .set(ident, TypeDeclaration::Builtin(builtin));
                }

                other_decl => {
                    self.diagnostics
                        .push(diag::ExpectedTypeIdentifier::new(dx, ident, other_decl).into());
                }
            }
        } else {
            self.diagnostics
                .push(diag::UndefinedIdentifier::new(dx, ident).into())
        }
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
        if let Some(decl) = self.scope.lookup(ident_name) {
            match *decl {
                Declaration::TypeParam(decl) => {
                    self.type_arg_names
                        .set(ident, TypeArgDeclaration::TypeParam(decl));
                }
                Declaration::BuiltinType(builtin) => {
                    self.type_arg_names
                        .set(ident, TypeArgDeclaration::Builtin(builtin));
                }
                Declaration::Const(decl) => {
                    self.type_arg_names
                        .set(ident, TypeArgDeclaration::Consts(decl));
                }
                other_decl => {
                    self.diagnostics
                        .push(diag::ExpectedTypeArgIdentifier::new(dx, ident, other_decl).into());
                }
            }
        } else {
            self.diagnostics
                .push(diag::UndefinedIdentifier::new(dx, ident).into())
        }
    }

    /// Indexes an identifier in a pattern, i.e. that is being assigned a value.
    /// If it is not declared yet, that is not an error.
    fn resolve_or_declare_value_ident(
        &mut self,
        arenas: &Arenas,
        ident: Ref<identifier::OracleValueIdentifier>,
        assign: Ref<AssignStatement>,
    ) {
        let dx = Resolver {
            arenas,
            locations: &self.locations,
        };
        let ident_name = get_text(ident, self.locations, &arenas.source);
        if let Some(decl) = self.scope.lookup(ident_name) {
            match *decl {
                Declaration::Const(decl) => {
                    self.diagnostics
                        .push(diag::AssignToConst::new(dx, ident).into());
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::Consts(decl));
                }
                Declaration::State(decl) => {
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::State(decl));
                }
                Declaration::OracleArg(decl) => {
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::Arg(decl));
                }
                Declaration::OracleLocal(assign) => self
                    .oracle_value_names
                    .set(ident, OracleValueDeclaration::Local(assign)),
                Declaration::BuiltinValue(builtin) => {
                    self.diagnostics
                        .push(diag::AssignToConst::new(dx, ident).into());
                    self.oracle_value_names
                        .set(ident, OracleValueDeclaration::Builtin(builtin))
                }
                other_decl => {
                    self.diagnostics
                        .push(diag::ExpectedValueIdentifier::new(dx, ident, other_decl).into());
                }
            }
        } else {
            self.oracle_value_names
                .set(ident, OracleValueDeclaration::Local(assign));
            self.scope
                .declare(ident_name, Declaration::OracleLocal(assign));
        }
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

    pub fn diagnostics(&self) -> &[diag::Diagnostic] {
        &self.diagnostics
    }
}
