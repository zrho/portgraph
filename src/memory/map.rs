use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use super::EntityIndex;

pub struct SecondaryMap<K, V> {
    values: Vec<V>,
    default: V,
    phantom: PhantomData<K>,
}

impl<K: EntityIndex, V: Clone> SecondaryMap<K, V> {
    pub fn new() -> Self
    where
        V: Default,
    {
        Self {
            values: Vec::new(),
            default: V::default(),
            phantom: PhantomData,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self
    where
        V: Default,
    {
        Self {
            values: Vec::with_capacity(capacity),
            default: V::default(),
            phantom: PhantomData,
        }
    }

    pub fn resize(&mut self, new_len: usize) {
        self.values.resize(new_len, self.default.clone());
    }
}

impl<K: EntityIndex, V: Default + Clone> Default for SecondaryMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: EntityIndex, V> Index<K> for SecondaryMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.values.get(index.index()).unwrap_or(&self.default)
    }
}

impl<K: EntityIndex, V: Clone> IndexMut<K> for SecondaryMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        let index = index.index();

        if index >= self.values.len() {
            self.values.resize(index + 1, self.default.clone());
        }

        &mut self.values[index]
    }
}
