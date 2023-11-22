#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::{
    base_registry::{
        BaseRegistry,
        BaseRegistryEntry,
    },
    BorrowError,
    ElementRef,
    ElementRefMut,
};

/// A handle to data registered in a specific [`Registry`].
///
/// A handle is returned when an element is registered in a registry. It can be passed back to the
/// registry to get a mutable reference to the same data.
pub type Handle = usize;

/// A container that can be used for registering values of a given type and retrieving references by
/// handle.
///
/// A registry is a centralized container that values can be inserted into and borrowed from. A
/// registry provides several guarantees:
/// - Arena-based allocated values using an [`Arena`][`crate::Arena`] (all references are valid for
///   the lifetime of the container).
/// - Runtime-checked immutable and mutable borrow rules.
/// - Values can be borrowed completely independent of one another.
///
/// A single value can be moved into the registry using [`Registry::register`], and multiple values
/// can be moved in using [`Registry::register_extend`].
pub struct Registry<T> {
    base: BaseRegistry<usize, T, Vec<BaseRegistryEntry<T>>>,
}

impl<T> Registry<T> {
    /// Creates a new registry.
    pub fn new() -> Self {
        Self {
            base: BaseRegistry::new(),
        }
    }

    /// Creates a new registry with the given capacity.
    pub fn with_capacity(size: usize) -> Self {
        Self {
            base: BaseRegistry::with_capacity(size),
        }
    }

    /// Checks if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Returns the number of elements owned by the registry.
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Registers a new value in the arena, returning a handle to that value.
    pub fn register(&self, value: T) -> Handle {
        let handle = self.base.len();
        let (data, borrow_state) = self.base.insert(value);
        self.base
            .entries_mut()
            .push(BaseRegistryEntry::new(data, borrow_state));
        handle
    }

    /// Registers the contents of an iterator in the registry.
    ///
    /// Returns a numeric range of handles `[a, b)`, where `a` is the handle of the first element
    /// inserted and `b` is the handle after the last element inserted.
    pub fn register_extend<I>(&self, iterable: I) -> (Handle, Handle)
    where
        I: IntoIterator<Item = T>,
    {
        let data = self.base.insert_extend(iterable);
        let first = self.base.entries().len();
        self.base.entries_mut().extend(
            data.into_iter()
                .map(|data| BaseRegistryEntry::new(data.0, data.1)),
        );
        let next = self.base.len();
        (first, next)
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    pub fn reserve(&self, additional: usize) {
        self.base.reserve(additional)
    }

    /// Converts the [`Registry<T>`] into a [`Vec<T>`].
    ///
    /// Items will maintain their handle as their vector index.
    pub fn into_vec(self) -> Vec<T> {
        self.base.into_vec()
    }

    /// Returns an iterator that provides immutable access to all elements in the registry, in order
    /// of registration.
    pub fn iter(&self) -> impl Iterator<Item = Result<ElementRef<T>, BorrowError>> {
        self.base.entries().iter().map(|entry| entry.borrow())
    }

    /// Returns an iterator that provides mutable access to all elements in the registry, in order
    /// of registration.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = Result<ElementRefMut<T>, BorrowError>> {
        self.base
            .entries_mut()
            .iter_mut()
            .map(|entry| entry.borrow_mut())
    }

    /// Returns a reference to a value previously registered in the registry.
    ///
    /// Panics if there is a borrow error.
    pub fn get_unchecked(&self, handle: Handle) -> ElementRef<T> {
        self.base.borrow(&handle)
    }

    /// Tries to get a reference to a value previously registered in the registry.
    pub fn get(&self, handle: Handle) -> Result<ElementRef<T>, BorrowError> {
        self.base.try_borrow(&handle)
    }

    /// Returns a mutable reference to a value previously registered in the registry.
    ///
    /// Panics if there is a borrow error.
    pub fn get_mut_unchecked(&self, handle: Handle) -> ElementRefMut<T> {
        self.base.borrow_mut(&handle)
    }

    /// Tries to get a mutable reference to a value previously registered in the registry.
    pub fn get_mut(&self, handle: Handle) -> Result<ElementRefMut<T>, BorrowError> {
        self.base.try_borrow_mut(&handle)
    }
}

#[cfg(test)]
mod registry_test {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::{
        vec,
        vec::Vec,
    };
    use core::cell::Cell;

    use crate::{
        BorrowError,
        Handle,
        Registry,
    };

    // A shared counter for how many times a value is deallocated.
    struct DropCounter<'c>(&'c Cell<u32>);

    impl<'c> Drop for DropCounter<'c> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    // A node type, like one used in a list, tree, or graph data structure.
    //
    // Helps us verify that arena-allocated values can refer to each other.
    struct Node<'d, T> {
        parent: Option<Handle>,
        value: T,
        #[allow(dead_code)]
        drop_counter: DropCounter<'d>,
    }

    impl<'a, 'd, T> Node<'d, T> {
        pub fn new(parent: Option<Handle>, value: T, drop_counter: DropCounter<'d>) -> Self {
            Self {
                parent,
                value,
                drop_counter,
            }
        }
    }

    #[test]
    #[allow(dropping_references)]
    fn allocates_and_owns_values() {
        let drop_counter = Cell::new(0);
        {
            let registry = Registry::with_capacity(2);
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

            let node = registry.get(handle).unwrap();
            assert_eq!(node.value, 4);
            let node = registry.get(node.parent.unwrap()).unwrap();
            assert_eq!(node.value, 3);
            let node = registry.get(node.parent.unwrap()).unwrap();
            assert_eq!(node.value, 2);
            let node = registry.get(node.parent.unwrap()).unwrap();
            assert_eq!(node.value, 1);
            assert_eq!(node.parent, None);
            assert_eq!(drop_counter.get(), 0);
        }
        // All values deallocated at the same time.
        assert_eq!(drop_counter.get(), 4);
    }

    #[test]
    fn register_extend_allocates_and_returns_handle_range() {
        let registry = Registry::new();
        let mut next_handle = 0;
        for i in 0..15 {
            let (begin, end) = registry.register_extend(0..i);
            assert_eq!(begin, next_handle);
            assert_eq!(end - begin, i);
            for (j, handle) in (0..i).zip(begin..end) {
                assert!(registry.get_unchecked(handle).eq(&j));
            }
            next_handle = end;
        }
    }

    #[test]
    fn register_extend_allocates_and_owns_values() {
        let drop_counter = Cell::new(0);
        {
            let registry = Registry::with_capacity(2);
            let iter = (0..100).map(|i| Node::new(None, i, DropCounter(&drop_counter)));
            let root = registry.register_extend(iter).0;
            let iter = (0..100).map(|i| Node::new(Some(root), i, DropCounter(&drop_counter)));
            registry.register_extend(iter);
            assert_eq!(drop_counter.get(), 0);
        }
        assert_eq!(drop_counter.get(), 200);
    }

    #[test]
    fn into_vec_reflects_insertion_order() {
        let registry = Registry::new();
        for &s in &["a", "b", "c", "d"] {
            registry.register(s);
        }
        let vec = registry.into_vec();
        assert_eq!(vec, vec!["a", "b", "c", "d"])
    }

    #[test]
    fn iter_itereates_in_order() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let registry = Registry::new();
        for i in 0..10 {
            registry.register(NoCopy(i));
        }
        assert!(registry
            .iter()
            .zip((0..10).map(|i| NoCopy(i)))
            .all(|(a, b)| a.is_ok_and(|a| a.eq(&b))));
    }

    #[test]
    fn iter_mut_itereates_in_order() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let mut registry = Registry::new();
        for i in 0..10 {
            registry.register(NoCopy(i));
        }
        assert!(registry
            .iter_mut()
            .zip((0..10).map(|i| NoCopy(i)))
            .all(|(a, b)| a.is_ok_and(|a| a.eq(&b))));
    }

    #[test]
    fn iter_mut_allows_mutable_access() {
        let mut registry = Registry::new();
        for i in 0..10 {
            registry.register(i);
        }
        for i in registry.iter_mut() {
            assert!(i.is_ok());
            *i.unwrap() += 1;
        }
        assert!(registry
            .iter_mut()
            .zip(1..11)
            .all(|(a, b)| a.is_ok_and(|a| a.eq(&b))));
    }

    #[test]
    fn handles_valid_with_large_blocks() {
        let registry = Registry::with_capacity(2);
        // Commit the first block and start the next.
        let first_range = registry.register_extend(0..1);
        let second_range = registry.register_extend(0..100);
        // Since the current block has elements in it, a new block is created.
        registry.reserve(1000);
        // These should fit in the same block.
        let third_range = registry.register_extend(0..500);
        let fourth_range = registry.register_extend(501..1000);

        // Validate that all handles still refer to the inserted values.
        assert!((first_range.0..first_range.1)
            .zip(0..1)
            .all(|(handle, value)| *registry.get_unchecked(handle) == value));
        assert!((second_range.0..second_range.1)
            .zip(0..100)
            .all(|(handle, value)| *registry.get_unchecked(handle) == value));
        assert!((third_range.0..third_range.1)
            .zip(0..500)
            .all(|(handle, value)| *registry.get_unchecked(handle) == value));
        assert!((fourth_range.0..fourth_range.1)
            .zip(501..1000)
            .all(|(handle, value)| *registry.get_unchecked(handle) == value));
    }

    #[test]
    fn tracks_length() {
        let registry = Registry::with_capacity(16);
        registry.register_extend(0..4);
        assert_eq!(registry.len(), 4);
        registry.register(5);
        assert_eq!(registry.len(), 5);
        registry.register(6);
        assert_eq!(registry.len(), 6);
        registry.register_extend(0..100);
        assert_eq!(registry.len(), 106);
    }

    #[test]
    fn borrow_out_of_bounds() {
        let registry = Registry::new();
        registry.register_extend(0..4);
        assert_eq!(registry.get(5).err(), Some(BorrowError::OutOfBounds));
        assert_eq!(registry.get_mut(6).err(), Some(BorrowError::OutOfBounds));
    }

    #[test]
    fn counts_immutable_borrws() {
        let registry = Registry::new();
        registry.register_extend(1..5);
        {
            let borrow_1 = registry.get(1);
            let borrow_2 = registry.get(1);
            let borrow_3 = registry.get(1);
            assert!(borrow_1.as_ref().is_ok_and(|val| val.eq(&2)));
            assert!(borrow_2.as_ref().is_ok_and(|val| val.eq(&2)));
            drop(borrow_1);
            drop(borrow_2);
            assert_eq!(
                registry.get_mut(1).err(),
                Some(BorrowError::AlreadyBorrowed)
            );
            assert!(borrow_3.is_ok_and(|val| val.eq(&2)));
        }
        assert!(registry.get_mut(1).is_ok_and(|val| val.eq(&2)));
    }

    #[test]
    fn only_one_mutable_borrow() {
        let registry = Registry::new();
        registry.register_extend(1..5);
        let mut borrow_1 = registry.get_mut(2);
        assert!(borrow_1.as_ref().is_ok_and(|val| val.eq(&3)));
        assert_eq!(
            registry.get_mut(2).err(),
            Some(BorrowError::AlreadyBorrowed)
        );
        *borrow_1.as_deref_mut().unwrap() *= 2;
        drop(borrow_1);
        let borrow_2 = registry.get_mut(2);
        assert!(borrow_2.as_ref().is_ok_and(|val| val.eq(&6)));
    }

    #[test]
    fn borrows_do_not_interfere() {
        let registry = Registry::new();
        registry.register_extend(1..5);
        let borrow_0_1 = registry.get(0);
        let borrow_1_1 = registry.get_mut(1);
        let borrow_2_1 = registry.get(2);
        let borrow_2_2 = registry.get(2);
        let borrow_3_1 = registry.get_mut(3);
        assert!(borrow_0_1.as_ref().is_ok_and(|val| val.eq(&1)));
        assert!(borrow_1_1.as_ref().is_ok_and(|val| val.eq(&2)));
        assert!(borrow_2_1.as_ref().is_ok_and(|val| val.eq(&3)));
        assert!(borrow_2_2.as_ref().is_ok_and(|val| val.eq(&3)));
        assert!(borrow_3_1.as_ref().is_ok_and(|val| val.eq(&4)));
    }

    #[test]
    fn immutable_borrow_can_be_cloned() {
        let registry = Registry::new();
        registry.register_extend(1..5);
        let borrow_1 = registry.get_unchecked(0);
        let borrow_2 = borrow_1.clone();
        assert!(borrow_1.eq(&1));
        assert!(borrow_2.eq(&1));
        drop(borrow_1);
        assert_eq!(
            registry.get_mut(0).err(),
            Some(BorrowError::AlreadyBorrowed)
        );
        drop(borrow_2);
        assert!(registry.get_mut(0).is_ok_and(|val| val.eq(&1)));
    }

    #[test]
    fn can_register_with_borrows_out() {
        let registry = Registry::with_capacity(16);
        registry.register_extend(1..5);
        let borrow_1 = registry.get(0);
        let borrow_2 = registry.get_mut(1);
        registry.register_extend(5..100);
        let borrow_3 = registry.get(4);
        let borrow_4 = registry.get(97);
        assert!(borrow_1.is_ok_and(|a| a.eq(&1)));
        assert!(borrow_2.is_ok_and(|a| a.eq(&2)));
        assert!(borrow_3.is_ok_and(|a| a.eq(&5)));
        assert!(borrow_4.is_ok_and(|a| a.eq(&98)));
    }

    #[test]
    fn borrow_in_iterator_succeeds_with_borrow_out() {
        let registry = Registry::new();
        registry.register_extend(1..5);
        let borrow = registry.get(2);
        assert_eq!(
            registry
                .iter()
                .map(|result| result.err())
                .collect::<Vec<Option<BorrowError>>>(),
            vec![None, None, None, None]
        );
        drop(borrow);
    }

    #[test]
    fn borrow_in_iterator_fails_with_mutable_borrow_out() {
        let registry = Registry::new();
        registry.register_extend(1..5);
        let borrow = registry.get_mut(2);
        assert_eq!(
            registry
                .iter()
                .map(|result| result.err())
                .collect::<Vec<Option<BorrowError>>>(),
            vec![None, None, Some(BorrowError::AlreadyBorrowed), None]
        );
        drop(borrow);
    }
}
