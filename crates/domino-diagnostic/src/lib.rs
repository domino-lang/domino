use domino_ast::{Arenas, InArena, LocationTable, NodeType};
use domino_collections::arena::Ref;

pub type NamedSource = miette::NamedSource<String>;

#[derive(Clone, Copy)]
pub struct Resolver<'a> {
    pub arenas: &'a Arenas,
    pub locations: &'a LocationTable,
}

impl<'a> Resolver<'a> {
    pub fn named_source<T: InArena + NodeType>(&self, reference: Ref<T>) -> NamedSource {
        let loc = self.locations.get(reference);
        let source_file = self.arenas.source.get(loc.file_id);

        NamedSource::new(
            source_file.path.to_string_lossy(),
            source_file.contents.clone(),
        )
    }

    pub fn span<T: InArena + NodeType>(&self, reference: Ref<T>) -> miette::SourceSpan {
        let loc = self.locations.get(reference);
        let start = loc.start as usize;
        let end = loc.end as usize;

        miette::SourceSpan::from(start..end)
    }
}
