use domino_ast::ast_nodes::{
    identifier::{Identifier, IdentifierKind},
    InArena, NodeType,
};

use crate::{ListItem, Parsable, Rule};

impl<IK: IdentifierKind> ListItem for Identifier<IK> {
    const LIST_RULE: Rule = Rule::ident_list;
}

impl<IK: IdentifierKind> Parsable for Identifier<IK>
where
    Identifier<IK>: NodeType + InArena,
{
    const RULE: Rule = Rule::identifier;

    fn parse_inner(
        _file_id: domino_ast::source::FileId,
        _state: &mut crate::State,
        _pair: crate::Pair,
    ) -> Self {
        Identifier::default()
    }
}
