use pretty::RcDoc;

pub mod commasep;

/// can be turned into a pretty doc
pub(crate) trait ToDoc<'a> {
    fn to_doc(&self) -> RcDoc<'a>;
}
