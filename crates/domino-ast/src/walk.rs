use crate::{
    arena::{Ref, Slice},
    ast_nodes::{InArena, Visit},
    Arenas, Visitor,
};

pub trait Walk: Sized {
    fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas);
}

pub fn walk<T, V>(visitor: &mut V, arenas: &Arenas, node: Ref<T>)
where
    T: Walk + InArena,
    V: Visitor + ?Sized,
{
    T::arena(arenas).get(node).walk(visitor, arenas)
}

pub fn visit_ref<T: Visit, V: Visitor + ?Sized>(visitor: &mut V, arenas: &Arenas, node: Ref<T>) {
    T::visit(visitor, arenas, node)
}

pub fn visit_slice<T: Visit, V: Visitor + ?Sized>(
    visitor: &mut V,
    arenas: &Arenas,
    slice: Slice<T>,
) {
    for node in slice.refs() {
        T::visit(visitor, arenas, node)
    }
}

mod impls {
    use super::*;

    use crate::ast_nodes::{
        common::ValueDecl,
        expressions::{
            BinOpExpression, CallExpression, Expression, ExpressionKind,
            OracleInvocationExpression, ParenExpression, SampleExpression, TableIndexExpression,
            TupleExpression, UnOpExpression,
        },
        game::{
            ComposeBlock, ComposeOracleAssignmentItem, ComposePackageInstanceItem, Game, GameItem,
        },
        identifier::{Identifier, IdentifierKind, OracleIdentifierKind, ValueIdentifierKind},
        instances::{
            InstanceAssignmentLhsKind, InstanceBlock, InstanceConstAssignmentItem,
            InstanceConstBlock, InstanceIdentifierKind, InstanceItem, InstanceTypeAssignmentItem,
            InstanceTypeBlock,
        },
        list::{Colon, Comma, List, ListNoDelim, Semicolon},
        oracles::{ArgDecl, OracleDefinition, OracleSignature},
        package::{ImportOraclesBlock, Package, PackageItem, StateBlock},
        params::{ConstParamBlock, TypeParamBlock},
        statements::{
            AssertStatement, AssignStatement, ExpressionStatement, IfThenElseStatement, Pattern,
            ReturnStatement, Statement, TablePattern, TuplePattern,
        },
        theorem::{
            AssumptionsBlock, AssumptionsItem, Bound, Conjecture, Equivalence,
            EquivalenceOracleBlock, EquivalenceOracleItem, GameHopItem, GameHops, InvariantSpec,
            LemmaBlock, LemmaItem, Path, Reduction, ReductionAssumptionLine, ReductionItem,
            ReductionMap, ReductionMapItem, SmtIdentifier, Theorem, TheoremItem,
        },
        types::{ArgumentedType, FnType, TupleType, Type, TypeArgument, TypeKind},
        File, Trivia, Trivium,
    };

    impl<IK: IdentifierKind> Walk for Identifier<IK> {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for Trivium {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for Comma {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for Colon {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for Semicolon {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for SmtIdentifier {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for Path {
        fn walk<V: Visitor + ?Sized>(&self, _visitor: &mut V, _arenas: &Arenas) {}
    }

    impl Walk for File<Package> {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visitor.trivia(arenas, self.leading_trivia);
            visitor.package(arenas, self.main);
            visitor.trivia(arenas, self.trailing_trivia);
        }
    }

    impl Walk for File<Game> {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visitor.trivia(arenas, self.leading_trivia);
            visitor.game(arenas, self.main);
            visitor.trivia(arenas, self.trailing_trivia);
        }
    }

    impl Walk for File<Theorem> {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visitor.trivia(arenas, self.leading_trivia);
            visitor.thm(arenas, self.main);
            visitor.trivia(arenas, self.trailing_trivia);
        }
    }

    impl Walk for Trivia {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_slice(visitor, arenas, self.trivia);
        }
    }

    impl<Node: Visit, Delim> Walk for List<Node, Delim> {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            // `delim_leading_trivia` has n or n-1 entries, so it is stepped manually rather than
            // zipped, to keep source order without dropping the trailing delimiter's trivia.
            let mut delims = self.delim_leading_trivia.refs();

            for (leading, item) in self.item_leading_trivia.refs().zip(self.items.refs()) {
                visit_ref(visitor, arenas, leading);
                visit_ref(visitor, arenas, item);
                if let Some(delim) = delims.next() {
                    visit_ref(visitor, arenas, delim);
                }
            }

            visit_ref(visitor, arenas, self.trailing_trivia);
        }
    }

    impl<Node: Visit> Walk for ListNoDelim<Node> {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            for (leading, item) in self.item_leading_trivia.refs().zip(self.items.refs()) {
                visit_ref(visitor, arenas, leading);
                visit_ref(visitor, arenas, item);
            }

            visit_ref(visitor, arenas, self.trailing_trivia);
        }
    }

    impl<TK: TypeKind> Walk for Type<TK>
    where
        Identifier<TK::TypeIdentifierKind>: Visit,
        TupleType<TK>: Visit,
        ArgumentedType<TK>: Visit,
        FnType<TK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                Type::Identifier(node) => visit_ref(visitor, arenas, node),
                Type::Tuple(node) => visit_ref(visitor, arenas, node),
                Type::Argumented(node) => visit_ref(visitor, arenas, node),
                Type::Fn(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl<TK: TypeKind> Walk for TupleType<TK>
    where
        List<Type<TK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.0);
        }
    }

    impl<TK: TypeKind> Walk for ArgumentedType<TK>
    where
        Identifier<TK::TypeIdentifierKind>: Visit,
        List<TypeArgument<TK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.post_name);
            visit_ref(visitor, arenas, self.args);
        }
    }

    impl<TK: TypeKind> Walk for TypeArgument<TK>
    where
        Identifier<TK::TypeArgIdentifierKind>: Visit,
        List<TypeArgument<TK>, Comma>: Visit,
        ArgumentedType<TK>: Visit,
        Type<TK>: Visit,
        Expression<TK::ExpressionKind>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                TypeArgument::Identifier(node) => visit_ref(visitor, arenas, node),
                TypeArgument::Tuple(node) => visit_ref(visitor, arenas, node),
                TypeArgument::Application(node) => visit_ref(visitor, arenas, node),
                TypeArgument::Type(node) => visit_ref(visitor, arenas, node),
                TypeArgument::Expr(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl<TK: TypeKind> Walk for FnType<TK>
    where
        List<Type<TK>, Comma>: Visit,
        Type<TK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.args_trivia);
            visit_ref(visitor, arenas, self.args);
            visit_ref(visitor, arenas, self.arrow_trivia);
            visit_ref(visitor, arenas, self.ret_trivia);
            visit_ref(visitor, arenas, self.ret_ty);
        }
    }

    impl<EK: ExpressionKind> Walk for Expression<EK>
    where
        TableIndexExpression<EK>: Visit,
        ParenExpression<EK>: Visit,
        TupleExpression<EK>: Visit,
        CallExpression<EK>: Visit,
        Identifier<EK::ValueIdentifierKind>: Visit,
        BinOpExpression<EK>: Visit,
        UnOpExpression<EK>: Visit,
        OracleInvocationExpression<EK>: Visit,
        SampleExpression<EK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                Expression::TableIndex(node) => visit_ref(visitor, arenas, node),
                Expression::Paren(node) => visit_ref(visitor, arenas, node),
                Expression::Tuple(node) => visit_ref(visitor, arenas, node),
                Expression::Call(node) => visit_ref(visitor, arenas, node),
                Expression::Identifier(node) => visit_ref(visitor, arenas, node),
                Expression::BinOp(node) => visit_ref(visitor, arenas, node),
                Expression::UnOp(node) => visit_ref(visitor, arenas, node),
                Expression::Invoke(node) => visit_ref(visitor, arenas, node),
                Expression::Sample(node) => visit_ref(visitor, arenas, node),
                Expression::String | Expression::Int => {}
            }
        }
    }

    impl<EK: ExpressionKind> Walk for BinOpExpression<EK>
    where
        Expression<EK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.lhs);
            visit_ref(visitor, arenas, self.pre_op_trivia);
            visit_ref(visitor, arenas, self.post_op_trivia);
            visit_ref(visitor, arenas, self.rhs);
        }
    }

    impl<EK: ExpressionKind> Walk for UnOpExpression<EK>
    where
        Expression<EK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.expr);
        }
    }

    impl<EK: ExpressionKind> Walk for ParenExpression<EK>
    where
        Expression<EK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.expr_trivia);
            visit_ref(visitor, arenas, self.expr);
            visit_ref(visitor, arenas, self.trailing_trivia);
        }
    }

    impl<EK: ExpressionKind> Walk for TupleExpression<EK>
    where
        List<Expression<EK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.0);
        }
    }

    impl<EK: ExpressionKind> Walk for CallExpression<EK>
    where
        Expression<EK>: Visit,
        List<Expression<EK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.args);
        }
    }

    impl<EK: ExpressionKind> Walk for TableIndexExpression<EK>
    where
        Identifier<EK::ValueIdentifierKind>: Visit,
        Expression<EK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.table_name);
            visit_ref(visitor, arenas, self.table_name_trivia);
            visit_ref(visitor, arenas, self.index_trivia);
            visit_ref(visitor, arenas, self.index);
            visit_ref(visitor, arenas, self.index_trailing_trivia);
        }
    }

    impl<EK: ExpressionKind> Walk for SampleExpression<EK>
    where
        Type<EK::TypeKind>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.ty);
        }
    }

    impl<EK: ExpressionKind> Walk for OracleInvocationExpression<EK>
    where
        List<Expression<EK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.oracle_name);
            visit_ref(visitor, arenas, self.oracle_name_trivia);
            visit_ref(visitor, arenas, self.args);
        }
    }

    impl Walk for Statement {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                Statement::Abort => {}
                Statement::Assert(node) => visit_ref(visitor, arenas, node),
                Statement::Assign(node) => visit_ref(visitor, arenas, node),
                Statement::Expression(node) => visit_ref(visitor, arenas, node),
                Statement::IfThenElse(node) => visit_ref(visitor, arenas, node),
                Statement::Return(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for AssertStatement {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.expr_trivia);
            visit_ref(visitor, arenas, self.expr);
            visit_ref(visitor, arenas, self.semicolon_trivia);
        }
    }

    impl Walk for AssignStatement {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.pat);
            visit_ref(visitor, arenas, self.pre_arrow_trivia);
            visit_ref(visitor, arenas, self.post_arrow_trivia);
            visit_ref(visitor, arenas, self.expr);
            visit_ref(visitor, arenas, self.semicolon_trivia);
        }
    }

    impl Walk for ExpressionStatement {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.expr);
            visit_ref(visitor, arenas, self.semicolon_trivia);
        }
    }

    impl Walk for IfThenElseStatement {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.cond_trivia);
            visit_ref(visitor, arenas, self.cond);
            visit_ref(visitor, arenas, self.cond_brace_trivia);
            visit_ref(visitor, arenas, self.then_block);

            if let Some(else_block) = self.else_block {
                visit_ref(visitor, arenas, else_block.pre_else_trivia);
                visit_ref(visitor, arenas, else_block.post_else_trivia);
                visit_ref(visitor, arenas, else_block.block);
            }
        }
    }

    impl Walk for ReturnStatement {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.expr);
            visit_ref(visitor, arenas, self.semicolon_trivia);
        }
    }

    impl Walk for Pattern {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                Pattern::Identifier(node) => visit_ref(visitor, arenas, node),
                Pattern::Table(node) => visit_ref(visitor, arenas, node),
                Pattern::Tuple(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for TablePattern {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.table_name);
            visit_ref(visitor, arenas, self.table_name_trivia);
            visit_ref(visitor, arenas, self.index_trivia);
            visit_ref(visitor, arenas, self.index);
            visit_ref(visitor, arenas, self.index_trailing_trivia);
        }
    }

    impl Walk for TuplePattern {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.items);
        }
    }

    // ---------------------------------------------------------------------------
    // oracles
    // ---------------------------------------------------------------------------

    impl<OI: OracleIdentifierKind> Walk for OracleSignature<OI>
    where
        Identifier<OI>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.args);

            if let Some(ret_ty) = self.ret_ty {
                visit_ref(visitor, arenas, ret_ty.pre_arrow_trivia);
                visit_ref(visitor, arenas, ret_ty.post_arrow_trivia);
                visit_ref(visitor, arenas, ret_ty.ty);
            }
        }
    }

    impl<IK: ValueIdentifierKind> Walk for ArgDecl<IK>
    where
        Identifier<IK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.pre_colon_trivia);
            visit_ref(visitor, arenas, self.post_colon_trivia);
            visit_ref(visitor, arenas, self.ty);
        }
    }

    impl Walk for OracleDefinition {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.sig_trivia);
            visit_ref(visitor, arenas, self.oracle_sig);
            visit_ref(visitor, arenas, self.brace_trivia);
            visit_ref(visitor, arenas, self.statements);
        }
    }

    // ---------------------------------------------------------------------------
    // common / params
    // ---------------------------------------------------------------------------

    impl<EK: ExpressionKind> Walk for ValueDecl<EK>
    where
        Identifier<EK::ValueIdentifierKind>: Visit,
        Type<EK::TypeKind>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.colon_trivia);
            visit_ref(visitor, arenas, self.ty_trivia);
            visit_ref(visitor, arenas, self.ty);
        }
    }

    impl<IK: IdentifierKind> Walk for TypeParamBlock<IK>
    where
        List<Identifier<IK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.decls);
        }
    }

    impl<EK: ExpressionKind> Walk for ConstParamBlock<EK>
    where
        List<ValueDecl<EK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.decls);
        }
    }

    // ---------------------------------------------------------------------------
    // instances (shared by game and theorem)
    // ---------------------------------------------------------------------------

    impl<LhsIK, RhsEK> Walk for InstanceConstAssignmentItem<LhsIK, RhsEK>
    where
        LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind,
        RhsEK: ExpressionKind,
        Identifier<LhsIK>: Visit,
        Expression<RhsEK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.ident);
            visit_ref(visitor, arenas, self.colon_trivia);
            visit_ref(visitor, arenas, self.expr_trivia);
            visit_ref(visitor, arenas, self.expr);
        }
    }

    impl<LhsIK, RhsEK> Walk for InstanceConstBlock<LhsIK, RhsEK>
    where
        LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsEK>,
        RhsEK: ExpressionKind,
        List<InstanceConstAssignmentItem<LhsIK, RhsEK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.list);
        }
    }

    impl<LhsIK, RhsTK> Walk for InstanceTypeAssignmentItem<LhsIK, RhsTK>
    where
        LhsIK: crate::ast_nodes::identifier::TypeIdentifierKind
            + InstanceAssignmentLhsKind<RhsKind = RhsTK>,
        RhsTK: TypeKind,
        Identifier<LhsIK>: Visit,
        Type<RhsTK>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.ident);
            visit_ref(visitor, arenas, self.colon_trivia);
            visit_ref(visitor, arenas, self.ty_trivia);
            visit_ref(visitor, arenas, self.ty);
        }
    }

    impl<LhsIK, RhsTK> Walk for InstanceTypeBlock<LhsIK, RhsTK>
    where
        LhsIK: crate::ast_nodes::identifier::TypeIdentifierKind
            + InstanceAssignmentLhsKind<RhsKind = RhsTK>,
        RhsTK: TypeKind,
        List<InstanceTypeAssignmentItem<LhsIK, RhsTK>, Comma>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.list);
        }
    }

    impl<IK: InstanceIdentifierKind> Walk for InstanceItem<IK>
    where
        InstanceConstBlock<IK::LhsValueIdentifierKind, IK::RhsExpressionKind>: Visit,
        InstanceTypeBlock<IK::LhsTypeIdentifierKind, IK::RhsTypeKind>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                InstanceItem::InstanceConst(node) => visit_ref(visitor, arenas, node),
                InstanceItem::InstanceType(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl<IK: InstanceIdentifierKind> Walk for InstanceBlock<IK>
    where
        Identifier<IK::InstanceIdentifierKind>: Visit,
        Identifier<IK::InstantiatedIdentifierKind>: Visit,
        ListNoDelim<InstanceItem<IK>>: Visit,
    {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.instance_name_trivia);
            visit_ref(visitor, arenas, self.instance_name);
            visit_ref(visitor, arenas, self.eq_trivia);
            visit_ref(visitor, arenas, self.instantiated_name_trivia);
            visit_ref(visitor, arenas, self.instantiated_name);
            visit_ref(visitor, arenas, self.brace_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    // ---------------------------------------------------------------------------
    // packages
    // ---------------------------------------------------------------------------

    impl Walk for StateBlock {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.decls);
        }
    }

    impl Walk for ImportOraclesBlock {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.decls);
        }
    }

    impl Walk for PackageItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                PackageItem::TypeParams(node) => visit_ref(visitor, arenas, node),
                PackageItem::ConstParams(node) => visit_ref(visitor, arenas, node),
                PackageItem::State(node) => visit_ref(visitor, arenas, node),
                PackageItem::ImportOracles(node) => visit_ref(visitor, arenas, node),
                PackageItem::OracleDefinition(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for Package {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name_trivia);
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.brace_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    // ---------------------------------------------------------------------------
    // games
    // ---------------------------------------------------------------------------

    impl Walk for ComposeOracleAssignmentItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.oracle_name);
            visit_ref(visitor, arenas, self.colon_trivia);
            visit_ref(visitor, arenas, self.pkg_inst_name_trivia);
            visit_ref(visitor, arenas, self.pkg_inst_name);
        }
    }

    impl Walk for ComposePackageInstanceItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.pkg_inst_name);
            visit_ref(visitor, arenas, self.colon_trivia);
            visit_ref(visitor, arenas, self.items_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for ComposeBlock {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for GameItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                GameItem::TypeParams(node) => visit_ref(visitor, arenas, node),
                GameItem::ConstParams(node) => visit_ref(visitor, arenas, node),
                GameItem::Instance(node) => visit_ref(visitor, arenas, node),
                GameItem::Compose(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for Game {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name_trivia);
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.brace_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    // ---------------------------------------------------------------------------
    // theorems
    // ---------------------------------------------------------------------------

    impl Walk for InvariantSpec {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.pre_colon_trivia);
            visit_ref(visitor, arenas, self.pre_open_trivia);
            visit_ref(visitor, arenas, self.paths);
        }
    }

    impl Walk for LemmaItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.pre_colon_trivia);
            visit_ref(visitor, arenas, self.pre_open_trivia);
            visit_ref(visitor, arenas, self.dependencies);
        }
    }

    impl Walk for LemmaBlock {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for EquivalenceOracleItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                EquivalenceOracleItem::InvariantSpec(node) => visit_ref(visitor, arenas, node),
                EquivalenceOracleItem::LemmaBlock(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for EquivalenceOracleBlock {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.pre_colon_trivia);
            visit_ref(visitor, arenas, self.pre_brace_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for Equivalence {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.kw_trivia);
            visit_ref(visitor, arenas, self.left_name);
            visit_ref(visitor, arenas, self.left_trivia);
            visit_ref(visitor, arenas, self.right_name);
            visit_ref(visitor, arenas, self.right_trivia);
            visit_ref(visitor, arenas, self.blocks);
        }
    }

    impl Walk for Bound {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.lhs);
            visit_ref(visitor, arenas, self.pre_tilde_trivia);
            visit_ref(visitor, arenas, self.post_tilde_trivia);
            visit_ref(visitor, arenas, self.rhs);
        }
    }

    impl Walk for AssumptionsItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.pre_colon_trivia);
            visit_ref(visitor, arenas, self.pre_brace_trivia);
            visit_ref(visitor, arenas, self.bound);
        }
    }

    impl Walk for AssumptionsBlock {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for Conjecture {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.left_trivia);
            visit_ref(visitor, arenas, self.left_name);
            visit_ref(visitor, arenas, self.right_trivia);
            visit_ref(visitor, arenas, self.right_name);
        }
    }

    impl Walk for ReductionAssumptionLine {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.name);
        }
    }

    impl Walk for ReductionMapItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.left_name);
            visit_ref(visitor, arenas, self.colon_trivia);
            visit_ref(visitor, arenas, self.right_trivia);
            visit_ref(visitor, arenas, self.right_name);
        }
    }

    impl Walk for ReductionMap {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.assumption_trivia);
            visit_ref(visitor, arenas, self.assumption_name);
            visit_ref(visitor, arenas, self.construction_trivia);
            visit_ref(visitor, arenas, self.construction_name);
            visit_ref(visitor, arenas, self.items_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for ReductionItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                ReductionItem::AssumptionLine(node) => visit_ref(visitor, arenas, node),
                ReductionItem::Map(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for Reduction {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.left_trivia);
            visit_ref(visitor, arenas, self.left_name);
            visit_ref(visitor, arenas, self.right_trivia);
            visit_ref(visitor, arenas, self.right_name);
            visit_ref(visitor, arenas, self.items_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for GameHopItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                GameHopItem::Reduction(node) => visit_ref(visitor, arenas, node),
                GameHopItem::Equivalence(node) => visit_ref(visitor, arenas, node),
                GameHopItem::Conjecture(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for GameHops {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }

    impl Walk for TheoremItem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            match *self {
                TheoremItem::ConstParams(node) => visit_ref(visitor, arenas, node),
                TheoremItem::GameInstance(node) => visit_ref(visitor, arenas, node),
                TheoremItem::Assumptions(node) => visit_ref(visitor, arenas, node),
                TheoremItem::GameHops(node) => visit_ref(visitor, arenas, node),
            }
        }
    }

    impl Walk for Theorem {
        fn walk<V: Visitor + ?Sized>(&self, visitor: &mut V, arenas: &Arenas) {
            visit_ref(visitor, arenas, self.name_trivia);
            visit_ref(visitor, arenas, self.name);
            visit_ref(visitor, arenas, self.brace_trivia);
            visit_ref(visitor, arenas, self.items);
        }
    }
}
