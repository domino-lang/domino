use domino_ast::{
    arena::{Arena, Ref},
    ast_nodes::NodeType,
    source::{SourceFile, SourceLocation},
    GlobalTable,
};

pub(crate) fn get_text<'a, T: NodeType>(
    node: Ref<T>,
    locations: &GlobalTable<SourceLocation>,
    source_arena: &'a Arena<SourceFile>,
) -> &'a str {
    let id = node.global_ref_id();
    let loc = *locations.get(&id).unwrap();
    source_arena.text(loc)
}
