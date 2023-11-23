#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::borrow::Borrow;

use hashbrown::HashMap;

use crate::{
    base_registry::{
        BaseRegistry,
        BaseRegistryEntry,
        KeyedBaseRegistry,
    },
    registry_container::Key,
    BorrowError,
    ElementRef,
    ElementRefMut,
};

/// A container that can be used for registering values of a given type and retrieving references by
/// a caller-specified key.
///
/// A registry is a centralized container that values can be inserted into and borrowed from. A
/// registry provides several guarantees:
/// - Arena-based allocated values using an [`Arena`][`crate::Arena`] (all references are valid for
///   the lifetime of the container).
/// - Runtime-checked immutable and mutable borrow rules.
/// - Values can be borrowed completely independent of one another.
///
/// A single value can be moved into the registry using [`KeyedRegistry::register`], and multiple
/// values can be moved in using [`KeyedRegistry::register_extend`].
pub struct KeyedRegistry<K, V> {
    base: BaseRegistry<K, V, HashMap<K, BaseRegistryEntry<V>>>,
}

impl<K, V> KeyedRegistry<K, V>
where
    K: Key,
{
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

    /// Registers a new value in the arena.
    ///
    /// Returns whether or not the value was registered in the registry. If there is already a value
    /// associated with the given key, no insertion occurs.
    pub fn register(&self, key: K, value: V) -> bool {
        if self.base.entries().contains_key(&key) {
            return false;
        }
        let (data, borrow_state) = self.base.insert(value);
        self.base
            .entries_mut()
            .insert(key, BaseRegistryEntry::new(data, borrow_state));
        true
    }

    /// Registers the contents of an iterator in the registry.
    pub fn register_extend<I>(&self, iterable: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        // First, reserve room in the underlying arena if we can. This is part of what we try to
        // guarantee with arena allocation, anyway, so we try our best to make the guarantee here.
        let iter = iterable.into_iter();
        self.base.reserve(iter.size_hint().0);

        // Extend overwrites values, so we need to check for duplicates ahead of time to avoid
        // overwriting any values.
        for (key, value) in iter.filter(|(key, _)| !self.base.entries().contains_key(key)) {
            let data = self.base.insert(value);
            self.base
                .entries_mut()
                .insert(key, BaseRegistryEntry::new(data.0, data.1));
        }
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    pub fn reserve(&self, additional: usize) {
        self.base.reserve(additional)
    }

    /// Converts the [`KeyedRegistry<K, V>`] into a [`Vec<V>`].
    ///
    /// Keys are completely lost.
    pub fn into_vec(self) -> Vec<V> {
        self.base.into_vec()
    }

    /// Returns an iterator that provides immutable access to all key-value pairs in the registry.
    pub fn iter(&self) -> impl Iterator<Item = (&K, Result<ElementRef<V>, BorrowError>)> {
        self.base
            .entries()
            .iter()
            .map(|(key, entry)| (key, entry.borrow()))
    }

    /// Returns an iterator that provides mutable access to all key-value pairs in the registry.
    pub fn iter_mut(
        &mut self,
    ) -> impl Iterator<Item = (&K, Result<ElementRefMut<V>, BorrowError>)> {
        self.base
            .entries_mut()
            .iter_mut()
            .map(|(key, entry)| (key, entry.borrow_mut()))
    }

    /// Returns an iterator over all keys in the registry.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.base.entries_mut().keys()
    }

    /// Returns an iterator that provides immutable access to all elements in the registry.
    pub fn values(&self) -> impl Iterator<Item = Result<ElementRef<V>, BorrowError>> {
        self.base.entries().values().map(|entry| entry.borrow())
    }

    /// Returns an iterator that provides mutable access to all elements in the registry.
    pub fn values_mut(&mut self) -> impl Iterator<Item = Result<ElementRefMut<V>, BorrowError>> {
        self.base
            .entries_mut()
            .values_mut()
            .map(|entry| entry.borrow_mut())
    }

    /// Returns a reference to a value previously registered in the registry.
    ///
    /// Panics if there is a borrow error.
    pub fn get_unchecked<R>(&self, key: &R) -> ElementRef<V>
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        KeyedBaseRegistry::borrow(&self.base, key)
    }

    /// Tries to get a reference to a value previously registered in the registry.
    pub fn get<R>(&self, key: &R) -> Result<ElementRef<V>, BorrowError>
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        KeyedBaseRegistry::try_borrow(&self.base, key)
    }

    /// Returns a mutable reference to a value previously registered in the registry.
    ///
    /// Panics if there is a borrow error.
    pub fn get_mut_unchecked<R>(&self, key: &R) -> ElementRefMut<V>
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        KeyedBaseRegistry::borrow_mut(&self.base, key)
    }

    /// Tries to get a mutable reference to a value previously registered in the registry.
    pub fn get_mut<R>(&self, key: &R) -> Result<ElementRefMut<V>, BorrowError>
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        KeyedBaseRegistry::try_borrow_mut(&self.base, key)
    }

    /// Checks if the registry contains an item associated with the given key.
    pub fn contains_key<R>(&self, key: &R) -> bool
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        self.base.entries().contains_key(key)
    }
}

#[cfg(test)]
mod registry_test {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::{
        borrow::ToOwned,
        format,
        string::String,
        vec,
        vec::Vec,
    };
    use core::cell::Cell;

    use crate::{
        BorrowError,
        KeyedRegistry,
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
        parent: Option<String>,
        value: T,
        #[allow(dead_code)]
        drop_counter: DropCounter<'d>,
    }

    impl<'a, 'd, T> Node<'d, T> {
        pub fn new(parent: Option<String>, value: T, drop_counter: DropCounter<'d>) -> Self {
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
            let registry = KeyedRegistry::<String, Node<i32>>::with_capacity(2);
            assert!(registry.is_empty());

            // Allocate a chain of nodes that refer to each other.
            assert!(registry.register(
                "node-1".to_owned(),
                Node::new(None, 1, DropCounter(&drop_counter)),
            ));
            assert_eq!(registry.len(), 1);
            assert!(!registry.is_empty());
            assert!(registry.register(
                "node-2".to_owned(),
                Node::new(Some("node-1".to_owned()), 2, DropCounter(&drop_counter)),
            ));
            assert_eq!(registry.len(), 2);
            assert!(registry.register(
                "node-3".to_owned(),
                Node::new(Some("node-2".to_owned()), 3, DropCounter(&drop_counter)),
            ));
            assert_eq!(registry.len(), 3);
            assert!(registry.register(
                "node-4".to_owned(),
                Node::new(Some("node-3".to_owned()), 4, DropCounter(&drop_counter)),
            ));
            assert_eq!(registry.len(), 4);

            let node = registry.get("node-4").unwrap();
            assert_eq!(node.value, 4);
            let node = registry.get("node-3").unwrap();
            assert_eq!(node.value, 3);
            let node = registry.get("node-2").unwrap();
            assert_eq!(node.value, 2);
            let node = registry.get("node-1").unwrap();
            assert_eq!(node.value, 1);
            assert_eq!(node.parent, None);
            assert_eq!(drop_counter.get(), 0);
        }
        // All values deallocated at the same time.
        assert_eq!(drop_counter.get(), 4);
    }

    #[test]
    fn register_extend_allocates() {
        let registry = KeyedRegistry::<String, i32>::new();
        for i in 0..15 {
            let len_before = registry.len();
            registry.register_extend((0..i).map(|j| (format!("key-{i}-{j}"), j)));
            assert_eq!(registry.len(), len_before + i as usize);
            for j in 0..i {
                assert!(registry.get_unchecked(&format!("key-{i}-{j}")).eq(&j));
            }
        }
    }

    #[test]
    fn register_extend_allocates_and_owns_values() {
        let drop_counter = Cell::new(0);
        {
            let registry = KeyedRegistry::<String, Node<i32>>::with_capacity(2);
            let iter = (0..100).map(|i| {
                (
                    format!("key-1-{i}"),
                    Node::new(None, i, DropCounter(&drop_counter)),
                )
            });
            registry.register_extend(iter);
            let iter = (0..100).map(|i| {
                (
                    format!("key-2-{i}"),
                    Node::new(None, i, DropCounter(&drop_counter)),
                )
            });
            registry.register_extend(iter);
            assert_eq!(drop_counter.get(), 0);
        }
        assert_eq!(drop_counter.get(), 200);
    }

    #[test]
    fn into_vec_contains_all_values() {
        let registry = KeyedRegistry::with_capacity(1);
        for &s in &["a", "b", "c", "d"] {
            registry.register(s, s);
        }
        let vec = registry.into_vec();
        assert_eq!(vec.len(), 4);
        assert!(vec.contains(&"a"));
        assert!(vec.contains(&"b"));
        assert!(vec.contains(&"c"));
        assert!(vec.contains(&"d"));
    }

    #[test]
    fn iter_itereates_all_key_value_pairs() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, NoCopy(i));
        }
        let mut vec = registry.iter().collect::<Vec<_>>();
        vec.sort_by(|(a, _), (b, _)| a.cmp(&b));
        assert!(vec
            .iter()
            .zip(0..10)
            .all(|((key, val), i)| key.eq(&&i) && val.as_ref().is_ok_and(|val| val.0.eq(&i))));
    }

    #[test]
    fn iter_mut_itereates_all_elements() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let mut registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, NoCopy(i));
        }
        let mut vec = registry.iter_mut().collect::<Vec<_>>();
        vec.sort_by(|(a, _), (b, _)| a.cmp(&b));
        assert!(vec
            .iter()
            .zip(0..10)
            .all(|((key, val), i)| key.eq(&&i) && val.as_ref().is_ok_and(|val| val.0.eq(&i))));
    }

    #[test]
    fn iter_mut_allows_mutable_access() {
        let mut registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, i);
        }
        for (_, i) in registry.iter_mut() {
            assert!(i.is_ok());
            *i.unwrap() += 1;
        }
        let mut vec = registry.iter().collect::<Vec<_>>();
        vec.sort_by(|(a, _), (b, _)| a.cmp(&b));
        assert!(vec
            .iter()
            .zip(0..10)
            .all(|((key, val), i)| key.eq(&&i) && val.as_ref().is_ok_and(|val| val.eq(&(i + 1)))));
    }

    #[test]
    fn values_itereates_all_elements() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, NoCopy(i));
        }
        let mut vec = registry.values().collect::<Vec<_>>();
        vec.sort_by(|a, b| a.as_ref().unwrap().0.cmp(&b.as_ref().unwrap().0));
        assert!(vec
            .iter()
            .zip(0..10)
            .all(|(val, i)| val.as_ref().is_ok_and(|val| val.0.eq(&i))));
    }

    #[test]
    fn values_mut_itereates_all_elements() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let mut registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, NoCopy(i));
        }
        let mut vec = registry.values_mut().collect::<Vec<_>>();
        vec.sort_by(|a, b| a.as_ref().unwrap().0.cmp(&b.as_ref().unwrap().0));
        assert!(vec
            .iter()
            .zip(0..10)
            .all(|(a, b)| a.as_ref().is_ok_and(|a| a.0.eq(&b))));
    }

    #[test]
    fn values_mut_allows_mutable_access() {
        let mut registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, i);
        }
        for i in registry.values_mut() {
            assert!(i.is_ok());
            *i.unwrap() += 1;
        }
        let mut vec = registry.values().collect::<Vec<_>>();
        vec.sort_by(|a, b| a.as_ref().unwrap().cmp(&b.as_ref().unwrap()));
        assert!(vec
            .iter()
            .zip(1..11)
            .all(|(a, b)| a.as_ref().is_ok_and(|a| a.eq(&b))));
    }

    #[test]
    fn keys_itereates_all_elements() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let registry = KeyedRegistry::new();
        for i in 0..10 {
            registry.register(i, NoCopy(i));
        }
        let mut vec = registry.keys().collect::<Vec<_>>();
        vec.sort_by(|a, b| a.cmp(b));
        assert!(vec.iter().zip(0..10).all(|(val, i)| val.eq(&&i)));
    }

    #[test]
    fn tracks_length() {
        let registry = KeyedRegistry::with_capacity(16);
        registry.register_extend((0..4).map(|i| (i, i)));
        assert_eq!(registry.len(), 4);
        registry.register(5, 5);
        assert_eq!(registry.len(), 5);
        registry.register(6, 6);
        assert_eq!(registry.len(), 6);
        registry.register_extend((7..107).map(|i| (i, i)));
        assert_eq!(registry.len(), 106);
    }

    #[test]
    fn borrow_out_of_bounds() {
        let registry = KeyedRegistry::new();
        registry.register_extend((0..4).map(|i| (i, i)));
        assert_eq!(registry.get(&5).err(), Some(BorrowError::OutOfBounds));
        assert_eq!(registry.get_mut(&6).err(), Some(BorrowError::OutOfBounds));
    }

    #[test]
    fn counts_immutable_borrws() {
        let registry = KeyedRegistry::new();
        registry.register_extend((1..5).map(|i| (i, i)));
        {
            let borrow_1 = registry.get(&2);
            let borrow_2 = registry.get(&2);
            let borrow_3 = registry.get(&2);
            assert!(borrow_1.as_ref().is_ok_and(|val| val.eq(&2)));
            assert!(borrow_2.as_ref().is_ok_and(|val| val.eq(&2)));
            drop(borrow_1);
            drop(borrow_2);
            assert_eq!(
                registry.get_mut(&2).err(),
                Some(BorrowError::AlreadyBorrowed)
            );
            assert!(borrow_3.is_ok_and(|val| val.eq(&2)));
        }
        assert!(registry.get_mut(&2).is_ok_and(|val| val.eq(&2)));
    }

    #[test]
    fn only_one_mutable_borrow() {
        let registry = KeyedRegistry::new();
        registry.register_extend((1..5).map(|i| (i, i)));
        let mut borrow_1 = registry.get_mut(&3);
        assert!(borrow_1.as_ref().is_ok_and(|val| val.eq(&3)));
        assert_eq!(
            registry.get_mut(&3).err(),
            Some(BorrowError::AlreadyBorrowed)
        );
        *borrow_1.as_deref_mut().unwrap() *= 2;
        drop(borrow_1);
        let borrow_2 = registry.get_mut(&3);
        assert!(borrow_2.as_ref().is_ok_and(|val| val.eq(&6)));
    }

    #[test]
    fn borrows_do_not_interfere() {
        let registry = KeyedRegistry::new();
        registry.register_extend((1..5).map(|i| (i, i)));
        let borrow_1_1 = registry.get(&1);
        let borrow_2_1 = registry.get_mut(&2);
        let borrow_3_1 = registry.get(&3);
        let borrow_3_2 = registry.get(&3);
        let borrow_4_1 = registry.get_mut(&4);
        assert!(borrow_1_1.as_ref().is_ok_and(|val| val.eq(&1)));
        assert!(borrow_2_1.as_ref().is_ok_and(|val| val.eq(&2)));
        assert!(borrow_3_1.as_ref().is_ok_and(|val| val.eq(&3)));
        assert!(borrow_3_2.as_ref().is_ok_and(|val| val.eq(&3)));
        assert!(borrow_4_1.as_ref().is_ok_and(|val| val.eq(&4)));
    }

    #[test]
    fn immutable_borrow_can_be_cloned() {
        let registry = KeyedRegistry::new();
        registry.register_extend((1..5).map(|i| (i, i)));
        let borrow_1 = registry.get_unchecked(&1);
        let borrow_2 = borrow_1.clone();
        assert!(borrow_1.eq(&1));
        assert!(borrow_2.eq(&1));
        drop(borrow_1);
        assert_eq!(
            registry.get_mut(&1).err(),
            Some(BorrowError::AlreadyBorrowed)
        );
        drop(borrow_2);
        assert!(registry.get_mut(&1).is_ok_and(|val| val.eq(&1)));
    }

    #[test]
    fn can_register_with_borrows_out() {
        let registry = KeyedRegistry::with_capacity(16);
        registry.register_extend((1..5).map(|i| (i, i)));
        let borrow_1 = registry.get(&1);
        let borrow_2 = registry.get_mut(&2);
        registry.register_extend((5..100).map(|i| (i, i)));
        let borrow_3 = registry.get(&5);
        let borrow_4 = registry.get(&98);
        assert!(borrow_1.is_ok_and(|a| a.eq(&1)));
        assert!(borrow_2.is_ok_and(|a| a.eq(&2)));
        assert!(borrow_3.is_ok_and(|a| a.eq(&5)));
        assert!(borrow_4.is_ok_and(|a| a.eq(&98)));
    }

    #[test]
    fn does_not_overwrite_values() {
        let registry = KeyedRegistry::new();
        assert!(registry.register(0, 0));
        assert!(!registry.register(0, 1));
        assert!(registry.get_unchecked(&0).eq(&0));
        assert_eq!(registry.len(), 1);
        registry.register_extend((1..10).map(|i| (i, i)));
        assert_eq!(registry.len(), 10);
        registry.register_extend((1..10).map(|i| (i, i)));
        assert_eq!(registry.len(), 10);
        registry.register_extend((5..15).map(|i| (i, i)));
        assert_eq!(registry.len(), 15);
    }

    #[test]
    fn borrow_in_iterator_succeeds_with_borrow_out() {
        let registry = KeyedRegistry::new();
        registry.register_extend((1..5).map(|i| (i, i)));
        let borrow = registry.get(&2);
        assert_eq!(
            registry
                .iter()
                .map(|(_, result)| result.err())
                .collect::<Vec<Option<BorrowError>>>(),
            vec![None, None, None, None]
        );
        drop(borrow);
    }

    #[test]
    fn borrow_in_iterator_fails_with_mutable_borrow_out() {
        let registry = KeyedRegistry::new();
        registry.register_extend((1..5).map(|i| (i, i)));
        let borrow = registry.get_mut(&2);
        assert_eq!(
            registry
                .iter()
                .map(|(_, result)| result.err())
                .collect::<Vec<Option<BorrowError>>>(),
            vec![None, None, Some(BorrowError::AlreadyBorrowed), None]
        );
        drop(borrow);
    }

    #[test]
    fn contains_key_works() {
        let registry = KeyedRegistry::new();
        assert!(!registry.contains_key("foo"));
        assert!(!registry.contains_key("bar"));
        assert!(!registry.contains_key("baz"));
        registry.register("foo".to_owned(), "bar".to_owned());
        assert!(registry.contains_key("foo"));
        assert!(!registry.contains_key("bar"));
        assert!(!registry.contains_key("baz"));
        registry.register("bar".to_owned(), "baz".to_owned());
        assert!(registry.contains_key("foo"));
        assert!(registry.contains_key("bar"));
        assert!(!registry.contains_key("baz"));
    }
}
