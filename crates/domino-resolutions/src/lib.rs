//! TODO: either move stuff out of here or rename it to domino-resolutions

use domino_ast::{Arenas, GlobalRefId, InArena, LocationTable, NodeType};
use domino_collections::arena::Ref;

pub trait DisplayDiagnostic {
    type Diag;
    fn display_diagnostic(&mut self, diag: impl IntoDiag<Self::Diag>);
}

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

    pub fn global_named_source(&self, id: GlobalRefId) -> NamedSource {
        domino_ast::with_global_ref_id!(id, |r| { self.named_source(r) })
    }

    pub fn span<T: InArena + NodeType>(&self, reference: Ref<T>) -> miette::SourceSpan {
        let loc = self.locations.get(reference);
        let start = loc.start as usize;
        let end = loc.end as usize;

        miette::SourceSpan::from(start..end)
    }

    pub fn global_span(&self, id: GlobalRefId) -> miette::SourceSpan {
        domino_ast::with_global_ref_id!(id, |r| { self.span(r) })
    }
}

pub trait DiagFrom<T>: Sized {
    fn diag_from<'a>(value: T, resolver: Resolver<'a>) -> Self;
}

pub trait IntoDiag<T> {
    fn into_diag<'a>(self, resolver: Resolver<'a>) -> T;
}

impl<T, F: DiagFrom<T>> IntoDiag<F> for T {
    fn into_diag<'a>(self, resolver: Resolver<'a>) -> F {
        F::diag_from(self, resolver)
    }
}

impl<T, F: From<T>> DiagFrom<T> for F {
    fn diag_from<'a>(value: T, _resolver: Resolver<'a>) -> Self {
        F::from(value)
    }
}

pub trait Resolves<From, To> {
    fn resolve(&self, from: Ref<From>) -> &To;
    fn resolve_mut(&mut self, from: Ref<From>) -> &mut To;
}
