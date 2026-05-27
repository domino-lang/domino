use crate::{
    arena::{Ref, Slice},
    ast_nodes::{
        identifier::{Identifier, OracleIdentifier, OracleValueIdentifier},
        impl_node_type,
        list::{impl_comma_list, Comma, List},
        statements::StatementList,
        types::Type,
        PaddedRef, Parsable, Trivia,
    },
    Rule,
};

/// oracle <gap> <name> <gap> ( <decl_list> )
#[derive(Debug, Clone, Copy)]
pub struct OracleSignature {
    pub name: Ref<OracleIdentifier>,
    pub trivia: Slice<Trivia>,
    pub args: Ref<DeclList>,
    pub ret_ty: Option<OracleReturnType>,
}

#[derive(Debug, Clone, Copy)]
pub struct OracleReturnType {
    pub pre_arrow_trivia: Slice<Trivia>,
    pub post_arrow_trivia: Slice<Trivia>,
    pub ty: Ref<Type>,
}

/// A list of declarations, usually comma separated. Usually surrounded by parenthises
pub type DeclList = List<ArgDecl, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct ArgDecl {
    pub name: Ref<OracleValueIdentifier>,
    pub pre_colon_trivia: Slice<Trivia>,
    pub post_colon_trivia: Slice<Trivia>,
    pub ty: Ref<Type>,
}

#[derive(Debug, Clone, Copy)]
pub struct OracleDefinition {
    pub oracle_sig: PaddedRef<OracleSignature>,
    pub statements: Ref<StatementList>,
}

impl_node_type!(0x50, OracleSignature, noop_index);
impl_node_type!(0x51, DeclList, noop_index);
impl_node_type!(0x52, ArgDecl, noop_index);
impl_node_type!(0x53, OracleDefinition, noop_index);
impl_node_type!(0x58, PaddedRef<ArgDecl>);
impl_node_type!(0x59, PaddedRef<OracleSignature>);

impl Parsable for OracleSignature {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::oracle_sig);

        let mut inner = pair.into_inner();
        let name_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let args_pair = inner.next().unwrap();

        let name = Identifier::parse_ref(file_id, state, name_pair);
        let trivia = Slice::from_pair(file_id, state, trivia_pair);
        let args = DeclList::parse_ref(file_id, state, args_pair);

        let ret_ty = inner.next().map(|pre_arrow_trivia_pair| {
            let post_arrow_trivia_pair = inner.next().unwrap();
            let ret_ty_pair = inner.next().unwrap();

            let pre_arrow_trivia = Slice::from_pair(file_id, state, pre_arrow_trivia_pair);
            let post_arrow_trivia = Slice::from_pair(file_id, state, post_arrow_trivia_pair);
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

impl_comma_list!(
    ArgDecl,
    Rule::expr_ident_decl_list,
    Rule::padded_expr_ident_decl
);

impl Parsable for ArgDecl {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::expr_ident_decl);

        let mut inner = pair.into_inner();
        let name_pair = inner.next().unwrap();
        let pre_colon_trivia_pair = inner.next().unwrap();
        let post_colon_trivia_pair = inner.next().unwrap();
        let ty_pair = inner.next().unwrap();

        let name = Identifier::parse_ref(file_id, state, name_pair);
        let pre_colon_trivia = Slice::from_pair(file_id, state, pre_colon_trivia_pair);
        let post_colon_trivia = Slice::from_pair(file_id, state, post_colon_trivia_pair);
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
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::oracle_def);

        let mut inner = pair.into_inner();
        let _oracle_pair = inner.next().unwrap();
        let oracle_sig_pair = inner.next().unwrap();
        let statements_pair = inner.next().unwrap();

        let oracle_sig = PaddedRef::parse(file_id, state, oracle_sig_pair);
        let statements = StatementList::parse_ref(file_id, state, statements_pair);

        Self {
            oracle_sig,
            statements,
        }
    }
}
