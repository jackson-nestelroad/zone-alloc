#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::Arena;
use core::{
    cell::{
        RefCell,
        RefMut,
    },
    mem,
    slice,
};

/// A handle to data registered in a specific [`Registry`].
///
/// A handle is returned when an element is registered in a registry. It can be passed back to the
/// registry to get a mutable reference to the same data.
pub type Handle = usize;

/// A container that can be used for registering values of a given type and retrieving references by
/// handle.
///
/// A [`Registry`] is a centralized data source that values can be inserted into. After insertion,
/// the registry returns a [`Handle`], which will refer to the same value for the lifetime of the
/// registry.
///
/// A single value can be moved into the registry using [`Registry::register`], and multiple values
/// can be moved in using [`Registry::register_extend`].
///
/// Internally, a registry uses an [`Arena`] for allocating values, which guarantees references are
/// valid for the lifetime of the arena. A [`Registry`] adds the additional guarantees that all
/// handles will refer to a single value in the underlying arena for the lifetime of the registry.
pub struct Registry<T> {
    // Internally, a registry is based on the following ideas:
    //  - All references to data in an arena is valid for the entire lifetime of the arena.
    //  - If a reference is valid, the corresponding pointer is also valid.
    //  - Thus, we can save a mapping of handles to pointers to arena-allocated data that will be
    //    valid for the lifetime of the registry.
    arena: Arena<T>,
    handles: RefCell<Vec<*mut T>>,
}

/// Iterator over mutable elements in a [`Registry`].
pub struct IterMut<'r, T> {
    // Store the mutable reference to the handles vector, so that we enforce that it is still being
    // used. We extended the lifetime of the iterator so that we could store it here.
    #[allow(dead_code)]
    handles: RefMut<'r, Vec<*mut T>>,
    iter: slice::Iter<'r, *mut T>,
}

impl<'r, T> Iterator for IterMut<'r, T> {
    type Item = &'r mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().cloned().map(|r| unsafe { &mut *r })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> Registry<T> {
    /// Creates a new registry.
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            handles: RefCell::new(Vec::new()),
        }
    }

    /// Creates a new registry with the given capacity.
    pub fn with_capacity(size: usize) -> Self {
        Self {
            arena: Arena::with_capacity(size),
            handles: RefCell::new(Vec::with_capacity(size)),
        }
    }

    /// Returns the number of elements owned by the registry.
    pub fn len(&self) -> usize {
        self.arena.len()
    }

    /// Registers a new value in the arena, returning a handle to that value.
    pub fn register(&self, value: T) -> Handle {
        // Allocate the value in the arena.
        let data = self.arena.alloc(value);
        // Add a new handle to this reference.
        let mut handles = self.handles.borrow_mut();
        let handle = handles.len();
        handles.push(data as *mut T);
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
        // Allocate all values in the arena.
        let data = self.arena.alloc_extend(iterable);
        // Add handles to all references.
        let mut handles = self.handles.borrow_mut();
        let first = handles.len();
        let next = first + data.len();
        handles.extend(data.iter_mut().map(|r| r as *mut T));
        (first, next)
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    pub fn reserve(&self, additional: usize) {
        self.arena.reserve(additional);
        self.handles.borrow_mut().reserve(additional);
    }

    /// Converts the [`Registry<T>`] into a [`Vec<T>`].
    ///
    /// Items will maintain their handle as their vector index.
    pub fn into_vec(self) -> Vec<T> {
        // Arena maintains insertion order, which is the same as how we generate handles. Thus, we
        // can rely on the arena's conversion to a vector.
        self.arena.into_vec()
    }

    /// Returns an iterator that provides mutable access to all elements in the registry, in order
    /// of registration.
    ///
    /// Registries only allow mutable iteration because the entire registry must be borrowed for the
    /// duration of the iteration. The mutable borrow to call this method allows Rust's borrow
    /// checker to enforce this rule.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        let handles = self.handles.borrow_mut();
        let iter = handles.iter();
        let iter = unsafe { mem::transmute(iter) };
        IterMut { handles, iter }
    }

    /// Returns a mutable reference to a value previously registered in the registry.
    pub fn get_mut(&self, handle: Handle) -> Option<&mut T> {
        self.handles
            .borrow()
            .get(handle)
            .cloned()
            .map(|r| unsafe { &mut *r })
    }

    /// Returns a reference to a value previously registered in the registry.
    pub fn get(&self, handle: Handle) -> Option<&T> {
        self.handles
            .borrow()
            .get(handle)
            .cloned()
            .map(|r| unsafe { &*r })
    }
}

#[cfg(test)]
mod registry_test {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::vec;

    use crate::{
        Handle,
        Registry,
    };
    use core::cell::Cell;

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

            // Allocate a chain of nodes that refer to each other.
            let mut handle = registry.register(Node::new(None, 1, DropCounter(&drop_counter)));
            assert_eq!(registry.len(), 1);
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

    #[test]
    fn register_extend_allocates_and_returns_handle_range() {
        let registry = Registry::new();
        let mut next_handle = 0;
        for i in 0..15 {
            let (begin, end) = registry.register_extend(0..i);
            assert_eq!(begin, next_handle);
            assert_eq!(end - begin, i);
            for (j, handle) in (0..i).zip(begin..end) {
                assert_eq!(registry.get(handle).cloned(), Some(j));
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
            .all(|(a, b)| a == &b));
    }

    #[test]
    fn iter_mut_allows_mutable_access() {
        let mut registry = Registry::new();
        for i in 0..10 {
            registry.register(i);
        }
        for i in registry.iter_mut() {
            *i += 1
        }
        assert!(registry.iter_mut().zip(1..11).all(|(a, b)| a == &b));
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
            .all(|(handle, value)| registry.get(handle).unwrap() == &value));
        assert!((second_range.0..second_range.1)
            .zip(0..100)
            .all(|(handle, value)| registry.get(handle).unwrap() == &value));
        assert!((third_range.0..third_range.1)
            .zip(0..500)
            .all(|(handle, value)| registry.get(handle).unwrap() == &value));
        assert!((fourth_range.0..fourth_range.1)
            .zip(501..1000)
            .all(|(handle, value)| registry.get(handle).unwrap() == &value));
    }
}
