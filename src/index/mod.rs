//! Components which manage indices.
use std::error::Error;

pub mod slab;

pub use slab::SlabIndexPool;

/// Memory pool which manages indices and associated values.
///
/// There is a wide design space for implementors of this trait.
///
///  - Generational indices.
///  - Bitsets and free lists.
///  - Locality optimisations such as local free lists.
pub trait IndexPool: std::ops::IndexMut<Self::Index, Output = Self::Value> {
    /// Index into the pool.
    type Index: Copy;

    /// Type of the value associated to the index.
    /// This can be `()` for pools which do not have an associated value.
    type Value;

    /// Returns whether the pool contains an `index`.
    fn contains(&self, index: Self::Index) -> bool;

    /// Borrows the value associated to an `index`.
    fn get(&self, index: Self::Index) -> Option<&Self::Value>;

    /// Mutably borrows the value associated to an `index`.
    fn get_mut(&mut self, index: Self::Index) -> Option<&mut Self::Value>;

    /// Mutably borrows the values of a disjoint collection of `indices`.
    fn get_disjoint_mut<const N: usize>(
        &mut self,
        indices: [Self::Index; N],
    ) -> Option<[&mut Self::Value; N]>;
}

/// [`IndexPool`] that allows to allocate and free indices.
pub trait IndexPoolAlloc: IndexPool {
    /// Error that can occur during allocation, e.g. when exceeding the capacity
    /// of a pool with finite capacity. In cases that this can not happen (apart
    /// from the system running out of memory) this error type should be
    /// [`Infallible`].
    ///
    /// [`Infallible`]: std::convert::Infallible
    type AllocError: Error;

    /// Allocates a new index given its initial `value`.
    ///
    /// # Errors
    ///
    /// May fail to allocate a new index. After a successful call to
    /// [`IndexPoolAlloc::reserve`] allocation must not fail for at least the
    /// number of indices reserved.
    ///
    /// # Panic
    ///
    /// May panic when the size of the pool would exceed or nearly exceed an
    /// integer type assumed to be big enough for overflow to be unlikely, e.g.
    /// `u32` or `usize` depending on the context.
    fn allocate(&mut self, value: Self::Value) -> Result<Self::Index, Self::AllocError>;

    /// Tries to reserve enough capacity to allocate `n` additional indices.
    ///
    /// # Errors
    ///
    /// May fail to reserve sufficient capacity for `n` new indices.
    ///
    /// # Panic
    ///
    /// May panic when the size of the pool would exceed or nearly exceed an
    /// integer type assumed to be big enough for overflow to be unlikely, e.g.
    /// `u32` or `usize` depending on the context.
    fn reserve(&mut self, n: usize) -> Result<(), Self::AllocError>;

    /// Attempts to free an `index`, returning its associated value. Returns
    /// `None` if the index is not allocated at this point.
    fn free(&mut self, index: Self::Index) -> Option<Self::Value>;

    /// Clears the pool by freeing all indices at once.
    fn clear(&mut self);

    /// Compacts the index space of the pool. Depending on the pool this is
    /// allowed to do nothing.
    ///
    /// Whenever a valid index is moved the `rekey` callback is invoked with the following values:
    ///  - A mutable borrow of the value associated to the index.
    ///  - The old index, now considered no longer valid.
    ///  - The new index, which was not valid before (i.e. calls to [`IndexPool::contains`] would have returned `false`).
    fn compact<F>(&mut self, rekey: F)
    where
        F: FnMut(&mut Self::Value, Self::Index, Self::Index);
}

/// [`IndexPool`] that allows to iterate over indices and values.
///
/// Index pools that implement this trait contain a finite number of valid indices at any point.
pub trait IndexPoolIter: IndexPool {
    /// Iterator created by [`IndexPoolIter::indices`].
    type Indices<'a>: Iterator<Item = Self::Index>
    where
        Self: 'a;

    /// Iterator created by [`IndexPoolIter::values`].
    type Values<'a>: Iterator<Item = (Self::Index, &'a Self::Value)>
    where
        Self: 'a;

    /// Iterator created by [`IndexPoolIter::values_mut`].
    type ValuesMut<'a>: Iterator<Item = (Self::Index, &'a mut Self::Value)>
    where
        Self: 'a;

    /// Iterates over the indices in the pool.
    fn indices(&self) -> Self::Indices<'_>;

    /// Iterates over pairs of indices and borrowed values in the pool.
    fn values(&self) -> Self::Values<'_>;

    /// Iterates over pairs of indices and mutably borrowed values in the pool.
    fn values_mut(&mut self) -> Self::ValuesMut<'_>;

    /// Returns the number of valid indices in the pool.
    #[inline]
    fn len(&self) -> usize {
        self.indices().count()
    }

    /// Returns whether the pool is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.indices().next().is_some()
    }
}
