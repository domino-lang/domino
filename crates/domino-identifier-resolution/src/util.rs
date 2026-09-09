use domino_ast::{
    arena::{Arena, Ref},
    ast_nodes::{
        identifier::{Identifier, IdentifierKind},
        InArena,
    },
    source::SourceFile,
    LocationTable,
};

pub(crate) fn get_text<'a, IK: IdentifierKind>(
    node: Ref<domino_ast::ast_nodes::identifier::Identifier<IK>>,
    locations: &LocationTable,
    source_arena: &'a Arena<SourceFile>,
) -> &'a str
where
    Identifier<IK>: InArena,
{
    let loc = locations.get(node);
    source_arena.text(loc)
}
