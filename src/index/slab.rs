use std::{
    cmp::Ordering,
    convert::Infallible,
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use crate::memory::EntityIndex;

use super::{IndexPool, IndexPoolAlloc, IndexPoolIter};

/// Slab index pool that manages fixed-sized objects with stable indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlabIndexPool<K, V> {
    data: Vec<Entry<V>>,
    /// Index of the next free entry. This is exactly the length of the `data` vector when the array is full.
    free_next: usize,
    /// The number of filled entries.
    len: usize,
    phantom: PhantomData<K>,
}

impl<K, V> IndexPool for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    type Index = K;
    type Value = V;

    #[inline]
    fn contains(&self, index: Self::Index) -> bool {
        matches!(self.data.get(index.index()), Some(Entry::Full(_)))
    }

    #[inline]
    fn get(&self, index: Self::Index) -> Option<&Self::Value> {
        match self.data.get(index.index()) {
            Some(Entry::Full(value)) => Some(value),
            _ => None,
        }
    }

    #[inline]
    fn get_mut(&mut self, index: Self::Index) -> Option<&mut Self::Value> {
        match self.data.get_mut(index.index()) {
            Some(Entry::Full(value)) => Some(value),
            _ => None,
        }
    }
}

impl<K, V> IndexPoolAlloc for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    type AllocError = Infallible;

    fn allocate(&mut self, value: Self::Value) -> Result<Self::Index, Self::AllocError> {
        let index = self.free_next;

        if index == self.data.len() {
            self.data.push(Entry::Full(value));
            self.free_next += 1;
        } else {
            let Entry::Free(next) = self.data[index] else { unreachable!() };
            self.free_next = next;
            self.data[index] = Entry::Full(value);
        }

        self.len += 1;

        Ok(K::new(index))
    }

    fn reserve(&mut self, n: usize) -> Result<(), Self::AllocError> {
        // Only reserve capacity that couldn't be serviced by the free list
        if let Some(extra_capacity) = n.checked_sub(self.free_list_len()) {
            self.data.reserve(extra_capacity)
        }

        Ok(())
    }

    fn free(&mut self, index: Self::Index) -> Option<Self::Value> {
        let index = index.index();
        let entry = self.data.get_mut(index)?;

        let entry_data = std::mem::replace(entry, Entry::Free(self.free_next));

        match entry_data {
            Entry::Free(_) => {
                *entry = entry_data;
                None
            }
            Entry::Full(value) => {
                self.free_next = index;
                self.len -= 1;
                Some(value)
            }
        }
    }

    #[inline]
    fn clear(&mut self) {
        self.data.clear();
        self.free_next = 0;
        self.len = 0;
    }

    fn compact<F>(&mut self, mut rekey: F)
    where
        F: FnMut(&mut Self::Value, Self::Index, Self::Index),
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

        self.free_next = self.data.len();
    }
}

impl<K, V> IndexPoolIter for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    type Indices<'a> = IndexIter<'a, K, V>
    where
        Self: 'a;

    type Values<'a> = Iter<'a, K, V>
    where
        Self: 'a;

    type ValuesMut<'a> = IterMut<'a, K, V>
    where
        Self: 'a;

    #[inline]
    fn indices(&self) -> Self::Indices<'_> {
        IndexIter::new(self)
    }

    #[inline]
    fn values(&self) -> Self::Values<'_> {
        Iter::new(self)
    }

    #[inline]
    fn values_mut(&mut self) -> Self::ValuesMut<'_> {
        IterMut::new(self)
    }
}

impl<K, V> SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    /// Creates an empty [`Slab<K, V>`].
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            free_next: 0,
            len: 0,
            phantom: PhantomData,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            free_next: 0,
            len: 0,
            phantom: PhantomData,
        }
    }

    /// Length of the free list.
    #[inline]
    fn free_list_len(&self) -> usize {
        self.data.len() - self.len
    }

    /// Returns an upper bound on a valid index in this slab.
    pub fn upper_bound(&self) -> K {
        K::new(self.data.len())
    }

    /// Returns the index at which the next entry will be inserted.
    #[inline(always)]
    pub fn next_index(&self) -> K {
        K::new(self.free_next)
    }

    // TODO: Add a `get_mut_disjoint` function with nice API to `IndexPool`
    pub fn get_mut_2(&mut self, key0: K, key1: K) -> Option<(&mut V, &mut V)> {
        let index0 = key0.index();
        let index1 = key1.index();

        let entries = match index0.cmp(&index1) {
            Ordering::Less => {
                let (slice0, slice1) = self.data.split_at_mut(index1);
                (slice0.get_mut(index0), slice1.get_mut(0))
            }
            Ordering::Greater => {
                let (slice1, slice0) = self.data.split_at_mut(index0);
                (slice0.get_mut(0), slice1.get_mut(index1))
            }
            Ordering::Equal => panic!(),
        };

        match entries {
            (Some(Entry::Full(value0)), Some(Entry::Full(value1))) => Some((value0, value1)),
            _ => None,
        }
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

    // TODO Reserve
    // TODO Compact
    // TODO Nicer debug representation
}

impl<K, V> Index<K> for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).expect("invalid key")
    }
}

impl<K, V> IndexMut<K> for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).expect("invalid key")
    }
}

impl<K, V> Default for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Entry<V> {
    Free(usize),
    Full(V),
}

pub struct IndexIter<'a, K, V>(Iter<'a, K, V>);

impl<'a, K, V> IndexIter<'a, K, V>
where
    K: EntityIndex,
{
    #[inline]
    fn new(slab: &'a SlabIndexPool<K, V>) -> Self {
        Self(slab.iter())
    }
}

impl<'a, K, V> Iterator for IndexIter<'a, K, V>
where
    K: EntityIndex,
{
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (index, _) = self.0.next()?;
        Some(index)
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K, V> ExactSizeIterator for IndexIter<'a, K, V>
where
    K: EntityIndex,
{
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, V> FusedIterator for IndexIter<'a, K, V> where K: EntityIndex {}

pub struct Iter<'a, K, V> {
    entries: std::iter::Enumerate<std::slice::Iter<'a, Entry<V>>>,
    len: usize,
    phantom: PhantomData<K>,
}

impl<'a, K, V> Iter<'a, K, V> {
    #[inline]
    fn new(slab: &'a SlabIndexPool<K, V>) -> Self {
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

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V>
where
    K: EntityIndex,
{
    #[inline]
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> where K: EntityIndex {}

impl<'a, K, V> IntoIterator for &'a SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    type Item = (K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
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
    #[inline]
    fn new(slab: &'a mut SlabIndexPool<K, V>) -> Self {
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

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
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

impl<'a, K, V> IntoIterator for &'a mut SlabIndexPool<K, V>
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
    #[inline]
    fn new(slab: SlabIndexPool<K, V>) -> Self {
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

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V>
where
    K: EntityIndex,
{
    #[inline]
    fn len(&self) -> usize {
        self.len
    }
}

impl<K, V> FusedIterator for IntoIter<K, V> where K: EntityIndex {}

impl<K, V> IntoIterator for SlabIndexPool<K, V>
where
    K: EntityIndex,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

pub struct Extend<'a, K, V, I> {
    slab: &'a mut SlabIndexPool<K, V>,
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
        Some(self.slab.allocate(value).unwrap())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.values.size_hint()
    }
}

impl<'a, K, V, I> ExactSizeIterator for Extend<'a, K, V, I>
where
    K: EntityIndex,
    I: ExactSizeIterator<Item = V>,
{
    #[inline]
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
