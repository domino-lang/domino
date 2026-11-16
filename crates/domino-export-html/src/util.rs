use maud::{html, Markup, PreEscaped, Render};

use std::fmt::Debug;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use sspverif::statement::{IfThenElse, Statement};

pub(super) fn join<I, V>(with: &str, values: I) -> Markup
where
    V: Render + Debug,
    I: IntoIterator<Item = V>,
    I::IntoIter: ExactSizeIterator,
{
    let mut values = values.into_iter();

    let prefix = if let Some(val) = values.next() {
        html! {(val)}
    } else {
        return html! {};
    };

    html! {
        (prefix)
        @for value in values {
            mo{(PreEscaped(with))}
            (value)
        }
    }
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
