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

use crate::writers::python::ty::PyType;

pub mod game_state;
pub mod pkg_state;

trait Dataclass {
    fn name(&self) -> impl Display;
    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType)>;
}

pub struct DataclassWriter<DC: Dataclass>(pub DC);

impl<DC: Dataclass> Display for DataclassWriter<DC> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "@dataclass")?;
        writeln!(f, "class {}:", self.0.name())?;
        for (name, ty) in self.0.fields() {
            writeln!(f, "  {name}: {ty}")?;
        }
        Ok(())
    }
}
