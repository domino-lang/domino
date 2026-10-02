use maud::{html, Markup, PreEscaped, Render};

use std::fmt::Debug;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use crate::statement::{IfThenElse, Statement};

pub(super) fn join<V: Render + Debug>(with: &str, values: &[V]) -> Markup {
    if values.is_empty() {
        return html! {};
    }
    if values.len() == 1 {
        return html! {(values[0])};
    }
    let prefix = html! {
        @for value in &values[..(values.len()-1)] {
            (value) mo{(PreEscaped(with))}
        }
    };
    html! {(prefix) (values[values.len()-1])}
}

pub(super) fn ite_is_assert(ite: &IfThenElse) -> bool {
    ite.then_block.0.is_empty()
        && ite.else_block.0.len() == 1
        && matches!(ite.else_block.0[0], Statement::Abort(_))
}

pub(super) fn ensure_css_file(target: &Path) -> std::io::Result<()> {
    let fname = target.join("domino.css");
    if let Ok(mut file) = File::create_new(fname) {
        write!(file, "{}", include_str!("assets/domino.css"))?;
    }
    Ok(())
}
