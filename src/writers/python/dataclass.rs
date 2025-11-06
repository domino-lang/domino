/*
*
*
* We need to
* - figure out the types to use on python's side
*   - bits_n
*     - BitVector? external dep.
*     - bitvec? same problem.
*     - maybe we just need deps
*   - int -> int
*   - bool -> bool
*
* - we need the const assignments in here - maybe simply full gameinstance?
* - what sample info do we need?
*   - here, not so much, but we need to find a way to do randomness mapping
*
* */

use core::fmt::Display;
use std::marker::PhantomData;

use pretty::RcDoc;

use crate::writers::python::ty::PyType;

use super::util::ToDoc;

pub mod game_state;
pub mod pkg_consts;
pub mod pkg_state;

pub(super) trait Dataclass<'a> {
    type Name: Display;

    fn name(&self) -> Self::Name;
    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType<'a>)>;
}

pub(crate) struct DataclassWriter<'a, DC: Dataclass<'a>>(pub DC, PhantomData<&'a ()>);

impl<'a, DC: Dataclass<'a>> DataclassWriter<'a, DC> {
    pub(crate) fn new(dataclass: DC) -> Self {
        Self(dataclass, PhantomData)
    }
}

impl<'a, DC: Dataclass<'a>> Display for DataclassWriter<'a, DC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(100, f)
    }
}

impl<'a, DC: Dataclass<'a>> ToDoc<'a> for DataclassWriter<'a, DC> {
    fn to_doc(&self) -> RcDoc<'a> {
        let mut fields: Vec<_> = self
            .0
            .fields()
            .into_iter()
            .map(|(name, ty)| {
                RcDoc::as_string(name)
                    .append(RcDoc::text(": "))
                    .append(RcDoc::as_string(ty))
            })
            .collect();

        if fields.is_empty() {
            fields = vec![RcDoc::text("pass")]
        }

        RcDoc::text("@dataclass")
            .append(RcDoc::line())
            .append(RcDoc::text("class "))
            .append(RcDoc::as_string(self.0.name()))
            .append(RcDoc::text(":"))
            .append(
                RcDoc::line()
                    .append(RcDoc::intersperse(fields, RcDoc::line()))
                    .nest(2),
            )
            .append(RcDoc::line())
            .append(RcDoc::line())
    }
}
