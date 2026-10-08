use domino_ast::{Arenas, LocationTable, State};
use domino_resolutions::{DisplayDiagnostic, Resolver};

pub mod identifier_resolution;

pub struct Display<'a> {
    arenas: &'a Arenas,
    locations: &'a LocationTable,
}

impl<'a> Display<'a> {
    pub fn new(state: &'a State) -> Self {
        Self {
            arenas: &state.arenas,
            locations: &state.tables.locations,
        }
    }
}

impl<'a> DisplayDiagnostic for Display<'a> {
    type Diag = identifier_resolution::Diagnostic;

    fn display_diagnostic(
        &mut self,
        diag: impl domino_resolutions::IntoDiag<identifier_resolution::Diagnostic>,
    ) {
        let resolver = Resolver {
            arenas: self.arenas,
            locations: self.locations,
        };

        println!("{:?}", miette::Report::from(diag.into_diag(resolver)));
    }
}
