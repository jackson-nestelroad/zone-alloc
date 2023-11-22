#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::marker::PhantomData;

use crate::{
    BorrowError,
    ElementRef,
    ElementRefMut,
    Handle,
    Registry,
};

/// A strong handle to data registered in a specific [`StrongRegistry`].
///
/// Strong handles are useful for separating handles from different registries. A handle from one
/// strong registry cannot be used for a different strong registry because the handle type is
/// statically enforced at compile time.
pub trait StrongHandle: From<Handle> {
    /// Returns the associated handle.
    fn handle(&self) -> Handle;
}

/// The same as [`Registry<T>`], but with strongly-typed handles to prevent handles from being
/// shared across multiple registries.
///
/// The handle type must implement the [`StrongHandle`] trait.
pub struct StrongRegistry<H, T> {
    registry: Registry<T>,
    phantom_handle: PhantomData<H>,
}

impl<H, T> StrongRegistry<H, T>
where
    H: StrongHandle,
{
    /// Creates a new strong registry.
    pub fn new() -> Self {
        Self {
            registry: Registry::new(),
            phantom_handle: PhantomData,
        }
    }

    /// Creates a new strong registry with the given capacity.
    pub fn with_capacity(size: usize) -> Self {
        Self {
            registry: Registry::with_capacity(size),
            phantom_handle: PhantomData,
        }
    }

    /// Checks if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.registry.is_empty()
    }

    /// Returns the number of elements owned by the strong registry.
    pub fn len(&self) -> usize {
        self.registry.len()
    }

    /// Registers a new value in the arena, returning a handle to that value.
    pub fn register(&self, value: T) -> H {
        H::from(self.registry.register(value))
    }

    /// Registers the contents of an iterator in the registry.
    ///
    /// Returns a numeric range of handles `[a, b)`, where `a` is the handle of the first element
    /// inserted and `b` is the handle after the last element inserted.
    pub fn register_extend<I>(&self, iterable: I) -> (H, H)
    where
        I: IntoIterator<Item = T>,
    {
        let (a, b) = self.registry.register_extend(iterable);
        (H::from(a), H::from(b))
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    pub fn reserve(&self, additional: usize) {
        self.registry.reserve(additional)
    }

    /// Converts the [`StrongRegistry<T>`] into a [`Vec<T>`].
    ///
    /// Items will maintain their handle as their vector index.
    pub fn into_vec(self) -> Vec<T> {
        self.registry.into_vec()
    }

    /// Returns an iterator that provides immutable access to all elements in the registry, in order
    /// of registration.
    pub fn iter(&self) -> impl Iterator<Item = Result<ElementRef<T>, BorrowError>> {
        self.registry.iter()
    }

    /// Returns an iterator that provides mutable access to all elements in the registry, in order
    /// of registration.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = Result<ElementRefMut<T>, BorrowError>> {
        self.registry.iter_mut()
    }

    /// Returns a reference to a value previously registered in the registry.
    ///
    /// Panics if there is a borrow error.
    pub fn get_unchecked(&self, handle: H) -> ElementRef<T> {
        self.registry.get_unchecked(handle.handle())
    }

    /// Tries to get a reference to a value previously registered in the registry.
    pub fn get(&self, handle: H) -> Result<ElementRef<T>, BorrowError> {
        self.registry.get(handle.handle())
    }

    /// Returns a mutable reference to a value previously registered in the registry.
    ///
    /// Panics if there is a borrow error.
    pub fn get_mut_unchecked(&self, handle: H) -> ElementRefMut<T> {
        self.registry.get_mut_unchecked(handle.handle())
    }

    /// Tries to get a mutable reference to a value previously registered in the registry.
    pub fn get_mut(&self, handle: H) -> Result<ElementRefMut<T>, BorrowError> {
        self.registry.get_mut(handle.handle())
    }
}

#[cfg(test)]
mod strong_registry_test {
    use core::cell::Cell;

    use crate::{
        Handle,
        StrongHandle,
        StrongRegistry,
    };

    // A shared counter for how many times a value is deallocated.
    struct DropCounter<'c>(&'c Cell<u32>);

    impl<'c> Drop for DropCounter<'c> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct NodeHandle(Handle);

    impl From<Handle> for NodeHandle {
        fn from(value: Handle) -> Self {
            Self(value)
        }
    }

    impl StrongHandle for NodeHandle {
        fn handle(&self) -> Handle {
            self.0
        }
    }

    // A node type, like one used in a list, tree, or graph data structure.
    //
    // Helps us verify that arena-allocated values can refer to each other.
    struct Node<'d, T> {
        parent: Option<NodeHandle>,
        value: T,
        #[allow(dead_code)]
        drop_counter: DropCounter<'d>,
    }

    impl<'a, 'd, T> Node<'d, T> {
        pub fn new(parent: Option<NodeHandle>, value: T, drop_counter: DropCounter<'d>) -> Self {
            Self {
                parent,
                value,
                drop_counter,
            }
        }
    }

    #[test]
    fn works_exactly_like_registry() {
        let drop_counter = Cell::new(0);
        {
            let registry = StrongRegistry::with_capacity(2);
            assert!(registry.is_empty());

            // Allocate a chain of nodes that refer to each other.
            let mut handle = registry.register(Node::new(None, 1, DropCounter(&drop_counter)));
            assert_eq!(registry.len(), 1);
            assert!(!registry.is_empty());
            handle = registry.register(Node::new(Some(handle), 2, DropCounter(&drop_counter)));
            assert_eq!(registry.len(), 2);
            handle = registry.register(Node::new(Some(handle), 3, DropCounter(&drop_counter)));
            assert_eq!(registry.len(), 3);
            handle = registry.register(Node::new(Some(handle), 4, DropCounter(&drop_counter)));
            assert_eq!(registry.len(), 4);

            let mut node = registry.get(handle).unwrap();
            assert_eq!(node.value, 4);
            node = registry.get(node.parent.unwrap()).unwrap();
            assert_eq!(node.value, 3);
            node = registry.get(node.parent.unwrap()).unwrap();
            assert_eq!(node.value, 2);
            node = registry.get(node.parent.unwrap()).unwrap();
            assert_eq!(node.value, 1);
            assert_eq!(node.parent, None);
            assert_eq!(drop_counter.get(), 0);
        }
        // All values deallocated at the same time.
        assert_eq!(drop_counter.get(), 4);
    }
}
