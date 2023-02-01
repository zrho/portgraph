//! A collection of tools to efficiently manage memory.
//!
//! Ultimately this module should have its own crate since it can be useful outside of graphs.
//! Inspired by the memory management in Cranelift IR.
pub mod list;
pub mod slab;

pub use list::ListPool;
pub use slab::Slab;

pub trait EntityIndex: Copy + Eq + Default {
    fn new(index: usize) -> Self {
        Self::try_new(index).unwrap()
    }

    fn try_new(index: usize) -> Option<Self>;
    fn index(self) -> usize;
}

pub trait Reserved {
    fn reserved() -> Self;
    fn is_reserved(&self) -> bool;
}

/// Macro which provides the common implementation of an n-bit entity reference
///
/// Based on [`cranelift_entity`'s `entity_impl!`](https://docs.rs/cranelift-entity/0.89.2/cranelift_entity/macro.entity_impl.html)
#[macro_export]
macro_rules! entity_impl {
    ($entity:ident, $backing:ty, $reserved_max:expr) => {
        impl $crate::memory::EntityIndex for $entity {
            #[inline(always)]
            fn try_new(ix: usize) -> Option<Self> {
                if ($reserved_max && ix < (<$backing>::MAX as usize))
                    || (!$reserved_max && ix <= (<$backing>::MAX as usize))
                    || (<$backing>::BITS) > usize::BITS
                {
                    Some($entity(ix as $backing))
                } else {
                    None
                }
            }

            #[inline(always)]
            fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

#[macro_export]
macro_rules! reserved_impl {
    ($entity:ident, $backing:ty) => {
        impl $crate::memory::Reserved for $entity {
            #[inline(always)]
            fn reserved() -> Self {
                Self(<$backing>::MAX)
            }

            #[inline(always)]
            fn is_reserved(&self) -> bool {
                self.0 == <$backing>::MAX
            }
        }
    };
}

macro_rules! int_entity_impl {
    ($entity:ident) => {
        impl $crate::memory::EntityIndex for $entity {
            #[inline(always)]
            fn try_new(ix: usize) -> Option<Self> {
                if (ix <= <$entity>::MAX as usize || <$entity>::BITS > usize::BITS) {
                    Some(ix as $entity)
                } else {
                    None
                }
            }

            #[inline(always)]
            fn index(self) -> usize {
                self as usize
            }
        }
    };
}

int_entity_impl!(u128);
int_entity_impl!(u64);
int_entity_impl!(u32);
int_entity_impl!(u16);
int_entity_impl!(u8);
