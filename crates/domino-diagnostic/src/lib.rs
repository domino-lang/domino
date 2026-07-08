use domino_ast::{
    arena::Ref,
    ast_nodes::{InArena, NodeType},
    Arenas, LocationTable,
};

pub type NamedSource = miette::NamedSource<String>;

pub struct Resolver<'a> {
    pub arenas: &'a Arenas,
    pub locations: &'a LocationTable,
}

impl<'a> Resolver<'a> {
    pub fn named_source<T: InArena + NodeType>(&self, reference: Ref<T>) -> NamedSource {
        let loc = self
            .locations
            .get(&reference.global_ref_id())
            .expect("found ast node without source location info");

        let source_file = self.arenas.source.get(loc.file_id);

        NamedSource::new(
            source_file.path.to_string_lossy(),
            source_file.contents.clone(),
        )
    }

    pub fn span<T: InArena + NodeType>(&self, reference: Ref<T>) -> miette::SourceSpan {
        let loc = self
            .locations
            .get(&reference.global_ref_id())
            .expect("found ast node without source location info");

        let start = loc.start as usize;
        let end = loc.end as usize;

        miette::SourceSpan::from(start..end)
    }
}
