use crate::{
    arena::Ref,
    ast_nodes::{
        expressions,
        identifier::{
            Identifier, OracleIdentifier, OracleValueIdentifierKind, ValueIdentifierKind,
        },
        list::{Comma, List},
        statements::StatementList,
        types::{self, Type},
        ListItem, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug, Clone, Copy)]
pub struct OracleExpressionKind;

impl expressions::ExpressionKind for OracleExpressionKind {
    type TypeKind = types::PackageTypeKind;
    type ValueIdentifierKind = OracleValueIdentifierKind;
}

pub type OracleExpression = expressions::Expression<OracleExpressionKind>;

pub type BinOpExpression = expressions::BinOpExpression<OracleExpressionKind>;

pub type UnOpExpression = expressions::UnOpExpression<OracleExpressionKind>;

pub type OracleInvocationExpression = expressions::OracleInvocationExpression<OracleExpressionKind>;

pub type ExprList = expressions::ExprList<OracleExpressionKind>;

pub type TableIndexExpression = expressions::TableIndexExpression<OracleExpressionKind>;

pub type SampleExpression = expressions::SampleExpression<OracleExpressionKind>;

pub type ParenExpression = expressions::ParenExpression<OracleExpressionKind>;

pub type CallExpression = expressions::CallExpression<OracleExpressionKind>;

pub type TupleExpression = expressions::TupleExpression<OracleExpressionKind>;

expressions::impl_expr!(OracleExpressionKind);

/// oracle <gap> <name> <gap> ( <decl_list> )
#[derive(Debug, Clone, Copy)]
pub struct OracleSignature {
    pub name: Ref<OracleIdentifier>,
    pub trivia: Ref<Trivia>,
    pub args: Ref<OracleValueDeclList>,
    pub ret_ty: Option<OracleReturnType>,
}

impl ListItem for OracleSignature {
    const LIST_RULE: Rule = Rule::oracle_decl_list;
}

#[derive(Debug, Clone, Copy)]
pub struct OracleReturnType {
    pub pre_arrow_trivia: Ref<Trivia>,
    pub post_arrow_trivia: Ref<Trivia>,
    pub ty: Ref<Type<types::PackageTypeKind>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ArgDecl<IK: ValueIdentifierKind> {
    pub name: Ref<Identifier<IK>>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub post_colon_trivia: Ref<Trivia>,
    pub ty: Ref<Type<types::PackageTypeKind>>,
}

pub type OracleValueArgDecl = ArgDecl<OracleValueIdentifierKind>;
impl ListItem for OracleValueArgDecl {
    const LIST_RULE: Rule = Rule::expr_ident_decl_list;
}

/// A list of declarations, usually comma separated. Usually surrounded by parenthises
pub type OracleValueDeclList = List<ArgDecl<OracleValueIdentifierKind>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct OracleDefinition {
    pub sig_trivia: Ref<Trivia>,
    pub oracle_sig: Ref<OracleSignature>,
    pub brace_trivia: Ref<Trivia>,
    pub statements: Ref<StatementList>,
}

impl Parsable for OracleSignature {
    const RULE: Rule = Rule::oracle_sig;

    fn parse_inner(
        file_id: crate::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let name_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let args_pair = inner.next().unwrap();

        let name = Identifier::parse_ref(file_id, state, name_pair);
        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let args = OracleValueDeclList::parse_ref(file_id, state, args_pair);

        let ret_ty = inner.next().map(|pre_arrow_trivia_pair| {
            let post_arrow_trivia_pair = inner.next().unwrap();
            let ret_ty_pair = inner.next().unwrap();

            let pre_arrow_trivia = Trivia::parse_ref(file_id, state, pre_arrow_trivia_pair);
            let post_arrow_trivia = Trivia::parse_ref(file_id, state, post_arrow_trivia_pair);
            let ty = Type::parse_ref(file_id, state, ret_ty_pair);

            OracleReturnType {
                pre_arrow_trivia,
                post_arrow_trivia,
                ty,
            }
        });

        Self {
            name,
            trivia,
            args,
            ret_ty,
        }
    }
}

impl Parsable for OracleValueArgDecl {
    const RULE: Rule = Rule::expr_ident_decl;

    fn parse_inner(
        file_id: crate::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let name_pair = inner.next().unwrap();
        let pre_colon_trivia_pair = inner.next().unwrap();
        let post_colon_trivia_pair = inner.next().unwrap();
        let ty_pair = inner.next().unwrap();

        let name = Identifier::parse_ref(file_id, state, name_pair);
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, pre_colon_trivia_pair);
        let post_colon_trivia = Trivia::parse_ref(file_id, state, post_colon_trivia_pair);
        let ty = Type::parse_ref(file_id, state, ty_pair);

        Self {
            name,
            pre_colon_trivia,
            post_colon_trivia,
            ty,
        }
    }
}

impl Parsable for OracleDefinition {
    const RULE: Rule = Rule::oracle_def;

    fn parse_inner(
        file_id: crate::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _oracle_pair = inner.next().unwrap();
        let sig_trivia_pair = inner.next().unwrap();
        let oracle_sig_pair = inner.next().unwrap();
        let brace_trivia_pair = inner.next().unwrap();
        let statements_pair = inner.next().unwrap();

        let sig_trivia = Trivia::parse_ref(file_id, state, sig_trivia_pair);
        let oracle_sig = OracleSignature::parse_ref(file_id, state, oracle_sig_pair);
        let brace_trivia = Trivia::parse_ref(file_id, state, brace_trivia_pair);
        let statements = StatementList::parse_ref(file_id, state, statements_pair);

        Self {
            sig_trivia,
            oracle_sig,
            brace_trivia,
            statements,
        }
    }
}
