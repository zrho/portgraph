use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

use crate::memory::EntityIndex;

/// An arena for dynamically sized lists of indices.
#[derive(Debug, Clone)]
pub struct ListPool<V> {
    data: Vec<V>,

    /// Heads of the free lists for each size class.
    free: Vec<usize>,
}

impl<V> ListPool<V>
where
    V: EntityIndex,
{
    /// Create a new empty list pool.
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            free: Vec::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            free: Vec::new(),
        }
    }

    /// Allocate a block of a given size class and return its starting index in `data`.
    ///
    /// This will attempt to use a block from the free list of the size class.
    /// If there is none, the `data` vector will be grown to accommodate the new block.
    fn allocate_block(&mut self, size_class: SizeClass) -> usize {
        let free = self
            .free
            .get(size_class.0 as usize)
            .and_then(|block| block.checked_sub(1));

        match free {
            Some(block) => {
                self.free[size_class.0 as usize] = self.data[block + 1].index();
                block
            }
            None => {
                let block = self.data.len();
                self.data.resize(block + size_class.total_size(), V::new(0));
                block
            }
        }
    }

    /// Frees a block of a given size class.
    fn free_block(&mut self, block: usize, size_class: SizeClass) {
        let size_class = size_class.0 as usize;

        // Ensure that the free list is long enough
        if self.free.len() <= size_class {
            self.free.resize(size_class + 1, 0);
        }

        self.data[block] = V::new(0);
        self.data[block + 1] = V::new(self.free[size_class]);
        self.free[size_class] = block + 1;
    }

    /// Reallocate a block to change size classes.
    /// When reallocating, `preserve_elements` many items will be copied over.
    ///
    /// Will do nothing if `size_class == new_size_class`.
    fn reallocate_block(
        &mut self,
        block: usize,
        size_class: SizeClass,
        new_size_class: SizeClass,
        preserve_elements: usize,
    ) -> usize {
        debug_assert!(preserve_elements < size_class.total_size());
        debug_assert!(preserve_elements < new_size_class.total_size());

        if size_class == new_size_class {
            return block;
        }

        let new_block = self.allocate_block(new_size_class);
        self.data
            .copy_within(block + 1..block + 1 + preserve_elements, new_block + 1);
        self.free_block(block, size_class);
        new_block
    }

    /// Get the block index and list length.
    /// If the list index is zero or out of bounds, return `None`.
    #[inline]
    fn get_block(&self, list: ListIndex<V>) -> Option<(usize, usize)> {
        // When the list index is zero, the subtraction will wrap around.
        // In that case the index will be out of bounds, producing `None`.
        // This trick uses the bounds check to achieve three things at once:
        //  1. Check if the list index is 0, indicating the unique empty list.
        //  2. Check if the index is out of bounds.
        //  3. Subtract 1 from the list index to get the block index without an additional underflow check.
        let block = list.index().wrapping_sub(1);
        self.data.get(block).map(|len| (block, len.index()))
    }

    /// Push an item to the end of a list.
    ///
    /// Since this potentially reallocates the list, a new list index is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::memory::list::{ListPool, ListIndex};
    /// let mut pool = ListPool::<u32>::new();
    /// let list = ListIndex::default();
    /// let list = pool.push(list, 1);
    /// let list = pool.push(list, 2);
    /// let list = pool.push(list, 3);
    /// let list = pool.push(list, 4);
    /// assert_eq!(pool.slice(list), [1, 2, 3, 4]);
    /// ```
    pub fn push(&mut self, list: ListIndex<V>, item: V) -> ListIndex<V> {
        match self.get_block(list) {
            Some((block, len)) => {
                let size_class = SizeClass::for_size(len);
                let new_size_class = SizeClass::for_size(len + 1);
                let block = self.reallocate_block(block, size_class, new_size_class, len);

                self.data[block] = V::new(len + 1);
                self.data[block + len + 1] = item;

                ListIndex::new(block + 1)
            }
            None => {
                let size_class = SizeClass::for_size(1);
                let block = self.allocate_block(size_class);

                self.data[block] = V::new(1);
                self.data[block + 1] = item;

                ListIndex::new(block + 1)
            }
        }
    }

    fn remove_last(&mut self, list: ListIndex<V>) -> ListIndex<V> {
        match self.get_block(list) {
            Some((block, len)) if len > 1 => {
                let size_class = SizeClass::for_size(len);
                let new_size_class = SizeClass::for_size(len - 1);
                let block = self.reallocate_block(block, size_class, new_size_class, len - 1);

                self.data[block] = V::new(len - 1);

                ListIndex::new(block + 1)
            }
            Some((block, len)) => {
                let size_class = SizeClass::for_size(len);
                self.free_block(block, size_class);
                ListIndex::new(0)
            }
            None => list,
        }
    }

    /// Extend a list with the contents of an iterator.
    ///
    /// Since this potentially reallocates the list, a new list index is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::memory::list::ListPool;
    /// let mut pool = ListPool::<u32>::new();
    /// let list = pool.from_iter([1, 2, 3]);
    /// let list = pool.extend(list, [4, 5]);
    /// let list = pool.extend(list, [6]);
    /// assert_eq!(pool.slice(list), [1, 2, 3, 4, 5, 6]);
    /// ```
    pub fn extend<I>(&mut self, list: ListIndex<V>, items: I) -> ListIndex<V>
    where
        I: IntoIterator<Item = V>,
    {
        let items = items.into_iter();
        let (min, max) = items.size_hint();

        if Some(min) != max {
            return items.fold(list, |list, item| self.push(list, item));
        }

        if min == 0 {
            return list;
        }

        let (block, len) = match self.get_block(list) {
            Some((block, len)) => {
                let size_class = SizeClass::for_size(len);
                let new_size_class = SizeClass::for_size(len + min);
                let block = self.reallocate_block(block, size_class, new_size_class, len);
                self.data[block] = V::new(len + min);
                (block, len)
            }
            None => {
                let size_class = SizeClass::for_size(min);
                let block = self.allocate_block(size_class);
                self.data[block] = V::new(min);
                (block, 0)
            }
        };

        let targets = &mut self.data[block + 1 + len..block + 1 + len + min];

        for (target, item) in targets.iter_mut().zip(items) {
            *target = item;
        }

        ListIndex::new(block + 1)
    }

    /// Insert an element into a list at an index, shifting all elements after it to the left.
    ///
    /// Because this shifts over the following elements, it has a worst-case performance of *O*(n).
    ///
    /// Since this potentially reallocates the list, a new list index is returned.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::memory::list::ListPool;
    /// let mut pool = ListPool::<u32>::new();
    /// let list = pool.from_iter([1, 2, 3]);
    /// let list = pool.insert(list, 1, 4);
    /// assert_eq!(pool.slice(list), [1, 4, 2, 3]);
    /// let list = pool.insert(list, 4, 5);
    /// assert_eq!(pool.slice(list), [1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, list: ListIndex<V>, index: usize, item: V) -> ListIndex<V> {
        let list = self.push(list, V::new(0));
        let slice = self.slice_mut(list);
        slice.copy_within(index..slice.len() - 1, index + 1);
        slice[index] = item;
        list
    }

    /// Removes and returns the element at position `index` within a list, shifting all elements after it to the left.
    ///
    /// Because this shifts over the remaining elements, it has a worst-case performance of *O*(n).
    /// If you don’t need the order of elements to be preserved, use [`swap_remove`] instead.
    ///
    /// Since this potentially reallocates the list, a new list index is returned.
    ///
    /// [`swap_remove`]: ListPool::swap_remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::memory::list::ListPool;
    /// let mut pool = ListPool::<u32>::new();
    /// let list = pool.from_iter([0, 1, 2, 3]);
    /// let (list, item) = pool.remove(list, 1);
    /// assert_eq!(item, 1);
    /// assert_eq!(pool.slice(list), [0, 2, 3]);
    /// let (list, item) = pool.remove(list, 0);
    /// assert_eq!(item, 0);
    /// assert_eq!(pool.slice(list), [2, 3]);
    /// ```
    pub fn remove(&mut self, list: ListIndex<V>, index: usize) -> (ListIndex<V>, V) {
        let slice = self.slice_mut(list);
        let item = slice.get(index).copied().expect("index is out of bounds");
        slice.copy_within(index + 1.., index);
        let list = self.remove_last(list);
        (list, item)
    }

    /// Removes an element from a list and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is *O*(1). If you need to preserve the element order, use [`remove`] instead.
    ///
    /// Since this potentially reallocates the list, a new list index is returned.
    ///
    /// [`remove`]: ListPool::remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::memory::list::ListPool;
    /// let mut pool = ListPool::<u32>::new();
    /// let list = pool.from_iter([0, 1, 2, 3]);
    ///
    /// let (list, item) = pool.swap_remove(list, 1);
    /// assert_eq!(item, 1);
    /// assert_eq!(pool.slice(list), [0, 3, 2]);
    ///
    /// let (list, item) = pool.swap_remove(list, 0);
    /// assert_eq!(item, 0);
    /// assert_eq!(pool.slice(list), [2, 3]);
    /// ```
    pub fn swap_remove(&mut self, list: ListIndex<V>, index: usize) -> (ListIndex<V>, V) {
        let slice = self.slice_mut(list);
        let item = slice.get(index).copied().expect("index is out of bounds");
        slice[index] = slice.last().copied().unwrap();
        let list = self.remove_last(list);
        (list, item)
    }

    /// Create a new list from the contents of an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use portgraph::memory::list::ListPool;
    /// let mut pool = ListPool::<u32>::new();
    /// let list = pool.from_iter([0, 1, 2, 3]);
    ///
    /// assert_eq!(pool.slice(list), [0, 1, 2, 3]);
    /// ```
    #[inline]
    pub fn from_iter<I>(&mut self, items: I) -> ListIndex<V>
    where
        I: IntoIterator<Item = V>,
    {
        self.extend(ListIndex::new(0), items)
    }

    /// Remove a list from this pool.
    pub fn clear(&mut self, list: ListIndex<V>) {
        if let Some((block, len)) = self.get_block(list) {
            let size_class = SizeClass::for_size(len);
            self.free_block(block, size_class);
        }
    }

    /// Remove all data from this pool.
    pub fn clear_all(&mut self) {
        self.data.clear();
        self.free.clear();
    }

    /// Get an immutable slice with the contents of a list.
    pub fn slice(&self, list: ListIndex<V>) -> &[V] {
        match self.get_block(list) {
            Some((block, len)) => &self.data[block + 1..block + 1 + len],
            None => &[],
        }
    }

    /// Get a mutable slice with the contents of a list.
    pub fn slice_mut(&mut self, list: ListIndex<V>) -> &mut [V] {
        match self.get_block(list) {
            Some((block, len)) => &mut self.data[block + 1..block + 1 + len],
            None => &mut [],
        }
    }

    /// Shrink the buffer to fit the currently present lists.
    pub fn shrink_to_fit(&mut self) {
        // TODO Shrink to fit
    }

    // TODO Nicer debug representation
    // TODO Compact? Perhaps use a bitvec to indicate starting positions of lists
}

impl<V> Index<ListIndex<V>> for ListPool<V>
where
    V: EntityIndex,
{
    type Output = [V];

    fn index(&self, index: ListIndex<V>) -> &Self::Output {
        self.slice(index)
    }
}

impl<V> IndexMut<ListIndex<V>> for ListPool<V>
where
    V: EntityIndex,
{
    fn index_mut(&mut self, index: ListIndex<V>) -> &mut Self::Output {
        self.slice_mut(index)
    }
}

impl<V> Default for ListPool<V>
where
    V: EntityIndex,
{
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ListIndex<V> {
    index: u32,
    phantom: PhantomData<V>,
}

impl<V> Default for ListIndex<V> {
    fn default() -> Self {
        Self {
            index: 0,
            phantom: Default::default(),
        }
    }
}

impl<V> EntityIndex for ListIndex<V>
where
    V: EntityIndex,
{
    fn try_new(index: usize) -> Option<Self> {
        if index <= u32::MAX as usize {
            Some(Self {
                index: index as u32,
                phantom: PhantomData,
            })
        } else {
            None
        }
    }

    fn index(self) -> usize {
        self.index as usize
    }
}

#[derive(Debug, Clone)]
pub struct EntityList<V> {
    index: ListIndex<V>,
}

impl<V> Default for EntityList<V> {
    fn default() -> Self {
        Self {
            index: Default::default(),
        }
    }
}

impl<V> EntityList<V>
where
    V: EntityIndex,
{
    pub fn new(index: ListIndex<V>) -> Self {
        Self { index }
    }

    pub fn new_from_iter<I>(iter: I, pool: &mut ListPool<V>) -> Self
    where
        I: IntoIterator<Item = V>,
    {
        Self::new(pool.from_iter(iter))
    }

    pub fn push(&mut self, item: V, pool: &mut ListPool<V>) {
        self.index = pool.push(self.index, item);
    }

    pub fn clear(&mut self, pool: &mut ListPool<V>) {
        pool.clear(self.index);
        self.index = ListIndex::default()
    }

    pub fn slice<'a>(&self, pool: &'a ListPool<V>) -> &'a [V] {
        pool.slice(self.index)
    }

    pub fn slice_mut<'a>(&self, pool: &'a mut ListPool<V>) -> &'a mut [V] {
        pool.slice_mut(self.index)
    }

    pub fn insert(&mut self, index: usize, item: V, pool: &mut ListPool<V>) {
        self.index = pool.insert(self.index, index, item);
    }

    pub fn remove(&mut self, index: usize, pool: &mut ListPool<V>) -> V {
        let (new_index, item) = pool.remove(self.index, index);
        self.index = new_index;
        item
    }

    pub fn swap_remove(&mut self, index: usize, pool: &mut ListPool<V>) -> V {
        let (new_index, item) = pool.swap_remove(self.index, index);
        self.index = new_index;
        item
    }

    pub fn get(&self, index: usize, pool: &ListPool<V>) -> Option<V> {
        self.slice(pool).get(index).copied()
    }

    pub fn get_mut<'a>(&self, index: usize, pool: &'a mut ListPool<V>) -> Option<&'a mut V> {
        self.slice_mut(pool).get_mut(index)
    }

    pub fn len(&self, pool: &ListPool<V>) -> usize {
        self.slice(pool).len()
    }

    pub fn is_empty(&self) -> bool {
        self.index == ListIndex::default()
    }

    pub fn extend<I>(&mut self, iter: I, pool: &mut ListPool<V>)
    where
        I: IntoIterator<Item = V>,
    {
        self.index = pool.extend(self.index, iter);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct SizeClass(u8);

impl SizeClass {
    #[inline]
    pub const fn total_size(self) -> usize {
        4 << (self.0 as usize)
    }

    #[inline]
    pub const fn for_size(size: usize) -> Self {
        Self(30 - (size as u32 | 3).leading_zeros() as u8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_class_for_size() {
        assert_eq!(SizeClass::for_size(0), SizeClass(0));
        assert_eq!(SizeClass::for_size(1), SizeClass(0));
        assert_eq!(SizeClass::for_size(2), SizeClass(0));
        assert_eq!(SizeClass::for_size(3), SizeClass(0));
        assert_eq!(SizeClass::for_size(4), SizeClass(1));
        assert_eq!(SizeClass::for_size(8), SizeClass(2));
    }

    #[test]
    fn size_class_total_size() {
        assert_eq!(SizeClass(0).total_size(), 4);
        assert_eq!(SizeClass(1).total_size(), 8);
        assert_eq!(SizeClass(2).total_size(), 16);
        assert_eq!(SizeClass(3).total_size(), 32);
    }
}
