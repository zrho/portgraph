use std::iter::Enumerate;
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
    pub fn len(&self) -> usize {
        self.values.len()
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

    pub fn push(&mut self, value: V) -> K {
        let index = self.values.len();
        self.values.push(value);
        K::new(index)
    }

    /// Changes the key of an entry.
    ///
    /// It is assumed but not checked that the entry at `old_index` was empty.
    /// If the entry at `new_index` was not definitely empty by being beyond the
    /// bounds of the map, a mutable reference to the value is returned.
    #[inline]
    pub fn rekey(&mut self, old_index: K, new_index: K) -> Option<&mut V> {
        if old_index.index() >= self.values.len() {
            if let Some(value) = self.values.get_mut(new_index.index()) {
                *value = self.default.clone()
            }

            None
        } else {
            let value = replace(&mut self.values[old_index.index()], self.default.clone());
            let entry = &mut self[new_index];
            *entry = value;
            Some(entry)
        }
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.values.iter().enumerate(),
            phantom_data: PhantomData,
        }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            iter: self.values.iter_mut().enumerate(),
            phantom_data: PhantomData,
        }
    }

    #[cold]
    fn resize_index_mut(&mut self, index: usize) -> &mut V {
        self.values.resize(index + 1, self.default.clone());
        &mut self.values[index]
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
            // This method is marked as cold
            self.resize_index_mut(index)
        } else {
            &mut self.values[index]
        }
    }
}

#[derive(Debug, Clone)]
pub struct Iter<'a, K, V> {
    iter: Enumerate<std::slice::Iter<'a, V>>,
    phantom_data: PhantomData<K>,
}

impl<'a, K: EntityIndex, V> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, value)| (K::new(i), value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Debug)]
pub struct IterMut<'a, K, V> {
    iter: Enumerate<std::slice::IterMut<'a, V>>,
    phantom_data: PhantomData<K>,
}

impl<'a, K: EntityIndex, V> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, value)| (K::new(i), value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
