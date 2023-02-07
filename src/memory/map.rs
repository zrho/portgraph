use std::marker::PhantomData;
use std::mem::replace;
use std::ops::{Index, IndexMut};

use super::EntityIndex;

#[derive(Debug, Clone)]
pub struct SecondaryMap<K, V> {
    values: Vec<V>,
    default: V,
    phantom: PhantomData<K>,
}

impl<K, V> SecondaryMap<K, V> {
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

    #[inline]
    pub fn clear(&mut self) {
        self.values.clear()
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.values.shrink_to_fit();
    }
}

impl<K: EntityIndex, V: Clone> SecondaryMap<K, V> {
    pub fn resize(&mut self, new_len: usize) {
        self.values.resize(new_len, self.default.clone());
    }

    #[inline]
    pub fn get(&self, index: K) -> Option<&V> {
        self.values.get(index.index())
    }

    #[inline]
    pub fn get_mut(&mut self, index: K) -> Option<&mut V> {
        self.values.get_mut(index.index())
    }

    pub fn take(&mut self, index: K) -> Option<V> {
        Some(replace(
            self.values.get_mut(index.index())?,
            self.default.clone(),
        ))
    }

    #[inline]
    pub fn swap(&mut self, old_index: K, new_index: K) {
        self.values.swap(old_index.index(), new_index.index());
    }
}

impl<K, V: Default + Clone> Default for SecondaryMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: EntityIndex, V> Index<K> for SecondaryMap<K, V> {
    type Output = V;

    #[inline]
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
