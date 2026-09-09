pub use domino_collections::arena::*;

impl<NodeType, Data> crate::DenseTable<NodeType, Data> {
    pub fn iter(&self) -> impl Iterator<Item = (Ref<NodeType>, &Data)> {
        self.as_slice()
            .iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<NodeType, Data> IntoIterator for crate::DenseTable<NodeType, Data> {
    type Item = (Ref<NodeType>, Data);

    type IntoIter = std::iter::Map<
        std::iter::Enumerate<std::vec::IntoIter<Data>>,
        fn((usize, Data)) -> (Ref<NodeType>, Data),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec()
            .into_iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<NodeType, Data> crate::PartialDenseTable<NodeType, Data> {
    pub fn iter(&self) -> impl Iterator<Item = (Ref<NodeType>, &Option<Data>)> {
        self.as_slice()
            .iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<NodeType, Data> IntoIterator for crate::PartialDenseTable<NodeType, Data> {
    type Item = (Ref<NodeType>, Option<Data>);

    type IntoIter = std::iter::Map<
        std::iter::Enumerate<std::vec::IntoIter<Option<Data>>>,
        fn((usize, Option<Data>)) -> (Ref<NodeType>, Option<Data>),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec()
            .into_iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}
