use std::{collections::HashMap, marker::PhantomData};

use crate::{source::SourceLocation, GlobalRefId};

/// A generic dense table: keeps a table `Ref<NodeType>` -> `Data`. Since [`Ref`] is a dense
/// number, we just use the reference id as the index into the Vec.
pub struct DenseTable<NodeType, Data>(Vec<Data>, PhantomData<NodeType>);

pub type LocationTable = HashMap<GlobalRefId, SourceLocation>;

#[derive(Default, Debug)]
pub struct Tables {
    pub locations: LocationTable,
}
