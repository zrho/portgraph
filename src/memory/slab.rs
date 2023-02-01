use std::{
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use crate::memory::EntityIndex;

/// A slab arena that manages fixed-sized objects.
#[derive(Debug, Clone)]
pub struct Slab<K, V> {
    data: Vec<Entry<V>>,
    free: usize,
    len: usize,
    phantom: PhantomData<K>,
}

impl<K, V> Slab<K, V>
where
    K: EntityIndex,
{
    /// Creates an empty [`Slab<K, V>`].
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            free: 0,
            len: 0,
            phantom: PhantomData,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            free: 0,
            len: 0,
            phantom: PhantomData,
        }
    }

    /// Returns the number of stored values.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns whether there is no stored value.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns an upper bound on a valid index in this slab.
    pub fn upper_bound(&self) -> K {
        K::new(self.data.len())
    }

    pub fn contains(&self, key: K) -> bool {
        matches!(self.data.get(key.index()), Some(Entry::Full(_)))
    }

    pub fn insert(&mut self, value: V) -> K {
        let index = self.free;

        if index == self.data.len() {
            self.data.push(Entry::Full(value));
            self.free += 1;
        } else {
            let Entry::Free(next) = self.data[index] else { unreachable!() };
            self.free = next;
            self.data[index] = Entry::Full(value);
        }

        self.len += 1;

        K::new(index)
    }

    pub fn remove(&mut self, key: K) -> Option<V> {
        let index = key.index();
        let entry = self.data.get_mut(index)?;

        let entry_data = std::mem::replace(entry, Entry::Free(self.free));

        match entry_data {
            Entry::Free(_) => {
                *entry = entry_data;
                None
            }
            Entry::Full(value) => {
                self.free = index;
                self.len -= 1;
                Some(value)
            }
        }
    }

    pub fn get(&self, key: K) -> Option<&V> {
        match self.data.get(key.index()) {
            Some(Entry::Full(value)) => Some(value),
            _ => None,
        }
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        match self.data.get_mut(key.index()) {
            Some(Entry::Full(value)) => Some(value),
            _ => None,
        }
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.free = 0;
        self.len = 0;
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self)
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(self)
    }

    #[must_use]
    pub fn extend<I>(&mut self, values: I) -> Extend<'_, K, V, I::IntoIter>
    where
        I: IntoIterator<Item = V>,
    {
        // TODO: Reserve according to minimum size hint bound
        Extend {
            slab: self,
            values: values.into_iter(),
        }
    }

    /// Shrink the buffer to fit the currently present values.
    pub fn shrink_to_fit(&mut self) {
        // TODO Remove free entries at the end?
        self.data.shrink_to_fit()
    }

    /// Compacts the slab by moving all entries to the front.
    ///
    /// Calls a `rekey` function with the old and new key for every entry.
    pub fn compact<F>(&mut self, mut rekey: F)
    where
        F: FnMut(&mut V, K, K),
    {
        // See https://docs.rs/slab/latest/slab/struct.Slab.html#method.compact for a more sophisticated version of this

        let mut old_index = 0;
        let mut new_index = 0;

        self.data.retain_mut(|entry| match entry {
            Entry::Free(_) => {
                old_index += 1;
                false
            }
            Entry::Full(value) => {
                rekey(value, K::new(old_index), K::new(new_index));
                old_index += 1;
                new_index += 1;
                true
            }
        });

        self.free = self.data.len();
    }

    // TODO Reserve
    // TODO Compact
    // TODO Nicer debug representation
}

impl<K, V> Index<K> for Slab<K, V>
where
    K: EntityIndex,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).expect("invalid key")
    }
}

impl<K, V> IndexMut<K> for Slab<K, V>
where
    K: EntityIndex,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).expect("invalid key")
    }
}

impl<K, V> Default for Slab<K, V>
where
    K: EntityIndex,
{
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
enum Entry<V> {
    Free(usize),
    Full(V),
}

pub struct Iter<'a, K, V> {
    entries: std::iter::Enumerate<std::slice::Iter<'a, Entry<V>>>,
    len: usize,
    phantom: PhantomData<K>,
}

impl<'a, K, V> Iter<'a, K, V> {
    fn new(slab: &'a Slab<K, V>) -> Self {
        Self {
            entries: slab.data.iter().enumerate(),
            len: slab.len,
            phantom: PhantomData,
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: EntityIndex,
{
    type Item = (K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        for (index, entry) in self.entries.by_ref() {
            if let Entry::Full(value) = entry {
                self.len -= 1;
                let key = K::new(index);
                return Some((key, value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V>
where
    K: EntityIndex,
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> where K: EntityIndex {}

impl<'a, K, V> IntoIterator for &'a Slab<K, V>
where
    K: EntityIndex,
{
    type Item = (K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct IterMut<'a, K, V> {
    entries: std::iter::Enumerate<std::slice::IterMut<'a, Entry<V>>>,
    len: usize,
    phantom: PhantomData<K>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    fn new(slab: &'a mut Slab<K, V>) -> Self {
        Self {
            entries: slab.data.iter_mut().enumerate(),
            len: slab.len,
            phantom: PhantomData,
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: EntityIndex,
{
    type Item = (K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        for (index, entry) in self.entries.by_ref() {
            if let Entry::Full(value) = entry {
                self.len -= 1;
                let key = K::new(index);
                return Some((key, value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V>
where
    K: EntityIndex,
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, K, V> FusedIterator for IterMut<'a, K, V> where K: EntityIndex {}

impl<'a, K, V> IntoIterator for &'a mut Slab<K, V>
where
    K: EntityIndex,
{
    type Item = (K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct IntoIter<K, V> {
    entries: std::iter::Enumerate<std::vec::IntoIter<Entry<V>>>,
    len: usize,
    phantom: PhantomData<K>,
}

impl<K, V> IntoIter<K, V> {
    fn new(slab: Slab<K, V>) -> Self {
        Self {
            entries: slab.data.into_iter().enumerate(),
            len: slab.len,
            phantom: PhantomData,
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V>
where
    K: EntityIndex,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        for (index, entry) in self.entries.by_ref() {
            if let Entry::Full(value) = entry {
                self.len -= 1;
                let key = K::new(index);
                return Some((key, value));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V>
where
    K: EntityIndex,
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<K, V> FusedIterator for IntoIter<K, V> where K: EntityIndex {}

impl<K, V> IntoIterator for Slab<K, V>
where
    K: EntityIndex,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

pub struct Extend<'a, K, V, I> {
    slab: &'a mut Slab<K, V>,
    values: I,
}

impl<'a, K, V, I> Iterator for Extend<'a, K, V, I>
where
    K: EntityIndex,
    I: Iterator<Item = V>,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.values.next()?;
        Some(self.slab.insert(value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.values.size_hint()
    }
}

impl<'a, K, V, I> ExactSizeIterator for Extend<'a, K, V, I>
where
    K: EntityIndex,
    I: ExactSizeIterator<Item = V>,
{
    fn len(&self) -> usize {
        self.values.len()
    }
}

impl<'a, K, V, I> FusedIterator for Extend<'a, K, V, I>
where
    K: EntityIndex,
    I: FusedIterator<Item = V>,
{
}
