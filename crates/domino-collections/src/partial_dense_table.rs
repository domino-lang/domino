use std::marker::PhantomData;

use crate::arena::Ref;

#[derive(Debug, Clone)]
pub struct PartialDenseTable<K, V>(Vec<Option<V>>, PhantomData<fn() -> K>);

impl<K, V> PartialDenseTable<K, V> {
    pub fn with_entries(size: usize) -> Self {
        let mut list = Vec::with_capacity(size);
        list.resize_with(size, || None);

        Self(list, PhantomData)
    }

    pub fn get(&self, key: Ref<K>) -> &Option<V> {
        &self.0[key.offset()]
    }

    pub fn get_mut(&mut self, key: Ref<K>) -> &mut Option<V> {
        &mut self.0[key.offset()]
    }

    pub fn set(&mut self, key: Ref<K>, value: V) {
        *self.get_mut(key) = Some(value);
    }

    pub fn as_slice(&self) -> &[Option<V>] {
        &self.0
    }

    pub fn into_vec(self) -> Vec<Option<V>> {
        self.0
    }

    pub fn missing<'a>(&'a self) -> impl Iterator<Item = Ref<K>> + 'a {
        self.iter().filter_map(|(r, v)| v.is_none().then_some(r))
    }
}

impl<K, V> PartialDenseTable<K, V> {
    pub fn iter(&self) -> impl Iterator<Item = (Ref<K>, &Option<V>)> {
        self.as_slice()
            .iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}

impl<K, V> IntoIterator for PartialDenseTable<K, V> {
    type Item = (Ref<K>, Option<V>);

    type IntoIter = std::iter::Map<
        std::iter::Enumerate<std::vec::IntoIter<Option<V>>>,
        fn((usize, Option<V>)) -> (Ref<K>, Option<V>),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec()
            .into_iter()
            .enumerate()
            .map(|(i, data)| (Ref::new_unchecked(i), data))
    }
}
