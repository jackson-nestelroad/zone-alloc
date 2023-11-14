#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

use core::{
    borrow::Borrow,
    cell::{
        RefCell,
        RefMut,
    },
    mem,
};

#[cfg(feature = "ahash")]
use ahash::HashMapExt;

use crate::Arena;

#[cfg(feature = "ahash")]
pub type KeyMap<K, V> = ahash::HashMap<K, V>;
#[cfg(all(feature = "std", not(feature = "ahash")))]
pub type KeyMap<K, V> = std::collections::HashMap<K, V>;
#[cfg(all(not(feature = "std"), not(feature = "ahash")))]
pub type KeyMap<K, V> = alloc::collections::BTreeMap<K, V>;

#[cfg(feature = "ahash")]
pub trait Key = core::cmp::Eq + core::hash::Hash;
#[cfg(all(feature = "std", not(feature = "ahash")))]
pub trait Key = core::cmp::Eq + core::hash::Hash;
#[cfg(all(not(feature = "std"), not(feature = "ahash")))]
pub trait Key = core::cmp::Ord;

#[cfg(any(feature = "std", feature = "ahash"))]
pub type KeyMapIter<'a, K, V> = std::collections::hash_map::Iter<'a, K, V>;
#[cfg(all(not(feature = "std"), not(feature = "ahash")))]
pub type KeyMapIter<'a, K, V> = alloc::collections::btree_map::Iter<'a, K, V>;

/// Iterator over mutable elements in a [`KeyedArena`].
pub struct IterMut<'a, K, T> {
    // Store the mutable reference to the entries map, so that we enforce that it is still being
    // used. We extended the lifetime of the iterator so that we could store it here.
    #[allow(dead_code)]
    entries: RefMut<'a, KeyMap<K, *mut T>>,
    iter: KeyMapIter<'a, K, *mut T>,
}

impl<'a, K, T> Iterator for IterMut<'a, K, T> {
    type Item = (&'a K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| unsafe { (k, &mut **v) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// The same as [`Arena<T>`], but each inserted value is internally mapped to a custom key for
/// retrieving the value later.
///
/// Similar to [`crate::Registry`], except a [`KeyMap`] is used internally, which requires key
/// hashing or ordering. Hashing is used by default. In `no_std` builds, ordering is used.
pub struct KeyedArena<K, T> {
    arena: Arena<T>,
    entries: RefCell<KeyMap<K, *mut T>>,
}

impl<K, T> KeyedArena<K, T>
where
    K: Key,
{
    /// Creates a new keyed arena.
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            entries: RefCell::new(KeyMap::new()),
        }
    }

    /// Creates a new keyed arena with the given capacity.
    #[cfg(any(feature = "std", feature = "ahash"))]
    pub fn with_capacity(size: usize) -> Self {
        Self {
            arena: Arena::with_capacity(size),
            entries: RefCell::new(KeyMap::with_capacity(size)),
        }
    }

    /// Returns the number of elements owned by the arena.
    pub fn len(&self) -> usize {
        self.arena.len()
    }

    /// Inserts a new value in the arena, returning a mutable reference to that vaue.
    ///
    /// Returns [`None`] if a value already exists for `key`.
    pub fn insert(&self, key: K, value: T) -> Option<&mut T> {
        let mut entries = self.entries.borrow_mut();
        if entries.contains_key(&key) {
            return None;
        }
        let data = self.arena.alloc(value);
        entries.insert(key, data);
        Some(data)
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    #[cfg(any(feature = "std", feature = "ahash"))]
    pub fn reserve(&self, additional: usize) {
        self.arena.reserve(additional);
        self.entries.borrow_mut().reserve(additional)
    }

    /// Returns an iterator that provides mutable access to all elements in the arena.
    ///
    /// There is no guaranteed order of entries.
    ///
    /// [`KeyedArena`]s only allow mutable iteration because the entire arena must be borrowed for
    /// the duration of the iteration. The mutable borrow to call this method allows Rust's
    /// borrow checker to enforce this rule.
    pub fn iter_mut(&mut self) -> IterMut<K, T> {
        let entries = self.entries.borrow_mut();
        let iter = entries.iter();
        let iter = unsafe { mem::transmute(iter) };
        IterMut { entries, iter }
    }

    /// Returns an iterator over all keys in the arena.
    pub fn keys(&mut self) -> impl Iterator<Item = &K> {
        self.iter_mut().map(|(k, _)| k)
    }

    /// Returns an iterator over mutable references to all elements in the arena.
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.iter_mut().map(|(_, v)| v)
    }

    /// Returns a mutable reference to a value previously inserted into the arena.
    pub fn get_mut<R>(&self, key: &R) -> Option<&mut T>
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        self.entries
            .borrow()
            .get(key)
            .cloned()
            .map(|r| unsafe { &mut *r })
    }

    /// Returns a reference to a value previously inserted into the arena.
    pub fn get<R>(&self, key: &R) -> Option<&T>
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        self.entries
            .borrow()
            .get(key)
            .cloned()
            .map(|r| unsafe { &*r })
    }

    /// Checks if the arena contains a value for the given `key`.
    pub fn contains_key<R>(&self, key: &R) -> bool
    where
        K: Borrow<R>,
        R: Key + ?Sized,
    {
        self.entries.borrow().contains_key(key)
    }
}

impl<K, V> FromIterator<(K, V)> for KeyedArena<K, V>
where
    K: Key,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let arena = Self::new();
        for (key, value) in iter {
            arena.insert(key, value);
        }
        arena
    }
}

#[cfg(test)]
mod keyed_arena_test {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::{
        borrow::ToOwned,
        collections::BTreeSet,
        string::String,
    };
    use core::cell::Cell;
    #[cfg(feature = "std")]
    use std::collections::BTreeSet;

    use crate::KeyedArena;

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
            let arena: KeyedArena<String, Node<'_, i32>> = KeyedArena::new();

            // Allocate a chain of nodes that refer to each other.
            let node = arena.insert(
                "node1".to_owned(),
                Node::new(None, 1, DropCounter(&drop_counter)),
            );
            assert!(node.is_some());
            assert_eq!(arena.len(), 1);
            let node = arena.insert(
                "node2".to_owned(),
                Node::new(Some("node1".to_owned()), 2, DropCounter(&drop_counter)),
            );
            assert!(node.is_some());
            assert_eq!(arena.len(), 2);
            let node = arena.insert(
                "node3".to_owned(),
                Node::new(Some("node2".to_owned()), 3, DropCounter(&drop_counter)),
            );
            assert!(node.is_some());
            assert_eq!(arena.len(), 3);
            let node = arena.insert(
                "node4".to_owned(),
                Node::new(Some("node3".to_owned()), 4, DropCounter(&drop_counter)),
            );
            assert!(node.is_some());
            assert_eq!(arena.len(), 4);
            let node = arena.insert(
                "node1".to_owned(),
                Node::new(None, 5, DropCounter(&drop_counter)),
            );
            assert!(node.is_none());
            assert_eq!(arena.len(), 4);

            let mut node = arena.get("node4").unwrap();
            assert_eq!(node.value, 4);
            node = arena.get(node.parent.as_ref().unwrap()).unwrap();
            assert_eq!(node.value, 3);
            node = arena.get(node.parent.as_ref().unwrap()).unwrap();
            assert_eq!(node.value, 2);
            node = arena.get(node.parent.as_ref().unwrap()).unwrap();
            assert_eq!(node.value, 1);
            assert_eq!(node.parent, None);

            // We dropped a value from the failed insertion above.
            assert_eq!(drop_counter.get(), 1);
        }
        // All inserted values deallocated at the same time.
        assert_eq!(drop_counter.get(), 5);
    }

    #[test]
    fn iter_mut_itereates_all_values() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let mut arena = KeyedArena::new();
        for i in 0..10 {
            arena.insert(i, NoCopy(i));
        }
        assert_eq!(
            arena.keys().cloned().collect::<BTreeSet<_>>(),
            (0..10).collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn iter_mut_allows_mutable_access() {
        let mut arena = KeyedArena::new();
        for i in 0..10 {
            arena.insert(i, i);
        }
        for (_, v) in arena.iter_mut() {
            *v += 1;
        }
        assert_eq!(
            arena
                .values_mut()
                .map(|val| val.clone())
                .collect::<BTreeSet<_>>(),
            (1..11).collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn contains_key_checks_values() {
        let arena = KeyedArena::new();
        for i in 0..10 {
            arena.insert(i, i);
        }
        for i in 0..10 {
            assert!(arena.contains_key(&i));
        }
        assert!(!arena.contains_key(&11));
        assert!(!arena.contains_key(&20));
        assert!(!arena.contains_key(&-1));
    }

    #[test]
    fn constructible_from_iterator() {
        let arena: KeyedArena<i32, i32> = (0..100).zip(0..100).collect();
        assert_eq!(arena.len(), 100);
    }
}
