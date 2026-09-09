use domino_ast::{
    ast_nodes::identifier::{Identifier, IdentifierKind},
    source::SourceFile,
    InArena, LocationTable,
};
use domino_collections::arena::{Arena, Ref};

pub(crate) fn get_text<'a, IK: IdentifierKind>(
    node: Ref<domino_ast::ast_nodes::identifier::Identifier<IK>>,
    locations: &LocationTable,
    source_arena: &'a Arena<SourceFile>,
) -> &'a str
where
    Identifier<IK>: InArena,
{
    let loc = locations.get(node);
    loc.text(source_arena)
}
