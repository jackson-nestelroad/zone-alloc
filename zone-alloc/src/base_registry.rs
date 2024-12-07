#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::{
    borrow::Borrow,
    cell::{
        Cell,
        UnsafeCell,
    },
    iter,
    marker::PhantomData,
    ptr::NonNull,
};

use crate::{
    element::{
        BorrowRef,
        BorrowRefMut,
        BorrowState,
    },
    registry_container::{
        Key,
        KeyedRegistryContainer,
        RegistryContainer,
    },
    Arena,
    BorrowError,
    ElementRef,
    ElementRefMut,
};

/// An entry in a [`BaseRegistry`], which refers to a value in an [`Arena`].
///
/// SAFETY: This data structure should not own any data.
pub(crate) struct BaseRegistryEntry<T> {
    data: NonNull<T>,
    borrow_state: NonNull<Cell<BorrowState>>,
}

impl<T> BaseRegistryEntry<T> {
    pub fn new(data: &mut T, borrow_state: &Cell<BorrowState>) -> Self {
        Self {
            data: data.into(),
            borrow_state: borrow_state.into(),
        }
    }

    pub fn borrow(&self) -> Result<ElementRef<T>, BorrowError> {
        BorrowRef::new(unsafe { self.borrow_state.as_ref() })
            .ok_or(BorrowError::AlreadyBorrowed)
            .map(|borrow_ref| ElementRef::new(self.data, borrow_ref))
    }

    pub fn borrow_mut(&self) -> Result<ElementRefMut<T>, BorrowError> {
        BorrowRefMut::new(unsafe { self.borrow_state.as_ref() })
            .ok_or(BorrowError::AlreadyBorrowed)
            .map(|borrow_ref| ElementRefMut::new(self.data.into(), borrow_ref))
    }
}

/// A container that facilitates borrow access to data in an [`Arena`].
///
/// A registry is a centralized container that values can be inserted into and borrowed from. A
/// registry provides several guarantees:
/// - Arena-based allocated values using an [`Arena`] (all references are valid for the lifetime of
///   the container).
/// - Runtime-checked immutable and mutable borrow rules.
/// - Values can be borrowed completely independent of one another.
///
/// This type is used as the base for different registry types. It wraps an [`Arena`] and some
/// underlying container that maps a key to each element in the arena. The mapping container can be
/// a [`Vec`] or a [`HashMap`][`std::collections::HashMap`], or any other container that implements
/// [`RegistryContainer`].
///
/// There are three internal containers:
/// - `arena` - The value arena.
/// - `borrow_states` - An arena for borrow states, one per value.
/// - `entries` - The key-value container, one entry per key-value pair.
///
/// It is completely up to wrapping implementations to uphold the following invariants:
/// - The value arena, borrow state arena, and key-value container are all the exact same length.
/// - For each value inserted into the arena, there is exactly one borrow state and one entry in the
///   key-value container.
/// - Key conflicts do not result in an extra value being placed in the value arena.
pub(crate) struct BaseRegistry<K, V, R> {
    arena: Arena<V>,
    borrow_states: Arena<Cell<BorrowState>>,
    // SAFETY: The elements of `entries` do not own any data. `entries` is safe to resize without
    // worrying about external references as long as no references to the elements themselves
    // exist.
    entries: UnsafeCell<R>,
    phantom_key: PhantomData<K>,
}

impl<K, V, R> BaseRegistry<K, V, R>
where
    R: RegistryContainer<K, BaseRegistryEntry<V>>,
{
    /// Creates a new registry.
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            borrow_states: Arena::new(),
            entries: R::new().into(),
            phantom_key: PhantomData,
        }
    }

    /// Creates a new registry with the given capacity.
    pub fn with_capacity(size: usize) -> Self {
        Self {
            arena: Arena::with_capacity(size),
            borrow_states: Arena::with_capacity(size),
            entries: R::with_capacity(size).into(),
            phantom_key: PhantomData,
        }
    }

    /// Returns a reference to the key-value container.
    pub fn entries(&self) -> &R {
        // SAFETY: This container does not own any data. No references to elements in this container
        // should ever be stored. It is purely used for data lookup.
        unsafe { &*self.entries.get() }
    }

    /// Returns a mutable reference to the key-value container.
    pub fn entries_mut(&self) -> &mut R {
        // SAFETY: This container does not own any data. No references to elements in this container
        // should ever be stored. It is purely used for data lookup.
        unsafe { &mut *self.entries.get() }
    }

    /// Checks if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.entries().is_empty()
    }

    /// Returns the number of elements owned by the registry.
    pub fn len(&self) -> usize {
        // The arena and entries should have the same length.
        self.entries().len()
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    pub fn reserve(&self, additional: usize) {
        self.arena.reserve(additional);
        self.borrow_states.reserve(additional);
        self.entries_mut().reserve(additional);
    }

    /// Inserts a new value into the arena, returning a mutable reference to that value and its
    /// borrow state.
    ///
    /// This method *does not* insert a value into the key-value container. This must be done
    /// manually by the wrapping implementation.
    pub fn insert(&self, value: V) -> (&mut V, &mut Cell<BorrowState>) {
        (
            self.arena.alloc(value),
            self.borrow_states.alloc(BorrowState::default().into()),
        )
    }

    /// Inserts multiple values into the arena, returning an iterator of mutable references to
    /// inserted values and their associated borrow states.
    ///
    /// This method *does not* insert values into the key-value container. This must be done
    /// manually by the wrapping implementation.
    pub fn insert_extend<I>(
        &self,
        iterable: I,
    ) -> impl Iterator<Item = (&mut V, &mut Cell<BorrowState>)>
    where
        I: IntoIterator<Item = V>,
    {
        let values = self.arena.alloc_extend(iterable);
        let borrow_states = self
            .borrow_states
            .alloc_extend(iter::repeat(BorrowState::default().into()).take(values.len()));
        values.into_iter().zip(borrow_states.into_iter())
    }

    /// Extracts the value arena out into a [`Vec<T>`].
    ///
    /// Items will be in the same order of allocation in the arena. Keys will be completely lost.
    pub fn into_vec(self) -> Vec<V> {
        self.arena.into_vec()
    }

    /// Immutably borrows the element corresponding to `key`.
    ///
    /// Panics if there is a borrow error.
    pub fn borrow(&self, key: &K) -> ElementRef<V> {
        self.try_borrow(key)
            .unwrap_or_else(|err| panic!("Borrow error: {err}"))
    }

    /// Tries to immutably borrow the element corresponding to `key`.
    pub fn try_borrow(&self, key: &K) -> Result<ElementRef<V>, BorrowError> {
        self.entries()
            .get(&key)
            .ok_or(BorrowError::OutOfBounds)
            .and_then(|entry| entry.borrow())
    }

    /// Mutably borrows the element corresponding to `key`.
    ///
    /// Panics if there is a borrow error.
    pub fn borrow_mut(&self, key: &K) -> ElementRefMut<V> {
        self.try_borrow_mut(key)
            .unwrap_or_else(|err| panic!("Borrow error: {err}"))
    }

    /// Tries to mutably borrow the element corresponding to `key`.
    pub fn try_borrow_mut(&self, key: &K) -> Result<ElementRefMut<V>, BorrowError> {
        self.entries()
            .get(&key)
            .ok_or(BorrowError::OutOfBounds)
            .and_then(|entry| entry.borrow_mut())
    }

    /// Checks if the registry is safe to drop.
    ///
    /// A registry is safe to drop if all elements are not borrowed. This check is not thread safe.
    pub fn safe_to_drop(&mut self) -> bool {
        self.borrow_states
            .iter_mut()
            .all(|borrow_state| borrow_state.get() == BorrowState::NotBorrowed)
    }
}

impl<K, V, R> Default for BaseRegistry<K, V, R>
where
    R: RegistryContainer<K, BaseRegistryEntry<V>>,
{
    fn default() -> Self {
        Self::new()
    }
}

/// Trait for borrowing by key in a [`BaseRegistry`].
pub trait KeyedBaseRegistry<K, V> {
    /// Immutably borrows the element corresponding to `key`.
    ///
    /// Panics if there is a borrow error.
    fn borrow<L>(&self, key: &L) -> ElementRef<V>
    where
        K: Borrow<L>,
        L: Key + ?Sized;

    /// Tries to immutably borrow the element corresponding to `key`.
    fn try_borrow<L>(&self, key: &L) -> Result<ElementRef<V>, BorrowError>
    where
        K: Borrow<L>,
        L: Key + ?Sized;

    /// Mutably borrows the element corresponding to `key`.
    ///
    /// Panics if there is a borrow error.
    fn borrow_mut<L>(&self, key: &L) -> ElementRefMut<V>
    where
        K: Borrow<L>,
        L: Key + ?Sized;

    /// Tries to mutably borrow the element corresponding to `key`.
    fn try_borrow_mut<L>(&self, key: &L) -> Result<ElementRefMut<V>, BorrowError>
    where
        K: Borrow<L>,
        L: Key + ?Sized;
}

impl<K, V, R> KeyedBaseRegistry<K, V> for BaseRegistry<K, V, R>
where
    K: Key,
    R: KeyedRegistryContainer<K, BaseRegistryEntry<V>>,
{
    fn borrow<L>(&self, key: &L) -> ElementRef<V>
    where
        K: Borrow<L>,
        L: Key + ?Sized,
    {
        KeyedBaseRegistry::try_borrow(self, key).unwrap_or_else(|err| panic!("Borrow error: {err}"))
    }

    fn try_borrow<L>(&self, key: &L) -> Result<ElementRef<V>, BorrowError>
    where
        K: Borrow<L>,
        L: Key + ?Sized,
    {
        KeyedRegistryContainer::get(self.entries(), key)
            .ok_or(BorrowError::OutOfBounds)
            .and_then(|entry| entry.borrow())
    }

    fn borrow_mut<L>(&self, key: &L) -> ElementRefMut<V>
    where
        K: Borrow<L>,
        L: Key + ?Sized,
    {
        KeyedBaseRegistry::try_borrow_mut(self, key)
            .unwrap_or_else(|err| panic!("Borrow error: {err}"))
    }

    fn try_borrow_mut<L>(&self, key: &L) -> Result<ElementRefMut<V>, BorrowError>
    where
        K: Borrow<L>,
        L: Key + ?Sized,
    {
        KeyedRegistryContainer::get(self.entries(), key)
            .ok_or(BorrowError::OutOfBounds)
            .and_then(|entry| entry.borrow_mut())
    }
}

#[cfg(test)]
mod base_registry_test {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::{
        vec,
        vec::Vec,
    };
    use core::mem;

    use crate::{
        base_registry::{
            BaseRegistry,
            BaseRegistryEntry,
        },
        BorrowError,
        ElementRef,
        ElementRefMut,
    };

    type VecBasedRegistry<T> = BaseRegistry<usize, T, Vec<BaseRegistryEntry<T>>>;

    fn insert_into_registry<T>(registry: &VecBasedRegistry<T>, value: T) {
        let (data, borrow_state) = registry.insert(value);
        registry.entries_mut().push(BaseRegistryEntry {
            data: data.into(),
            borrow_state: borrow_state.into(),
        });
    }

    fn insert_many_into_registry<T, I>(registry: &VecBasedRegistry<T>, iterable: I)
    where
        I: IntoIterator<Item = T>,
    {
        for value in iterable {
            insert_into_registry(registry, value);
        }
    }

    #[test]
    fn tracks_length() {
        let registry = VecBasedRegistry::with_capacity(16);
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        assert_eq!(registry.len(), 4);
        insert_into_registry(&registry, 5);
        assert_eq!(registry.len(), 5);
        insert_into_registry(&registry, 6);
        assert_eq!(registry.len(), 6);
        insert_many_into_registry(&registry, 0..100);
        assert_eq!(registry.len(), 106);
    }

    #[test]
    fn borrow_out_of_bounds() {
        let registry = VecBasedRegistry::new();
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        assert_eq!(
            registry.try_borrow(&5).err(),
            Some(BorrowError::OutOfBounds)
        );
        assert_eq!(
            registry.try_borrow_mut(&6).err(),
            Some(BorrowError::OutOfBounds)
        );
    }

    #[test]
    fn counts_immutable_borrws() {
        let registry = VecBasedRegistry::new();
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        {
            let borrow_1 = registry.try_borrow(&1);
            let borrow_2 = registry.try_borrow(&1);
            let borrow_3 = registry.try_borrow(&1);
            assert!(borrow_1.as_ref().is_ok_and(|val| val.eq(&2)));
            assert!(borrow_2.as_ref().is_ok_and(|val| val.eq(&2)));
            drop(borrow_1);
            drop(borrow_2);
            assert_eq!(
                registry.try_borrow_mut(&1).err(),
                Some(BorrowError::AlreadyBorrowed)
            );
            assert!(borrow_3.is_ok_and(|val| val.eq(&2)));
        }
        assert!(registry.try_borrow_mut(&1).is_ok_and(|val| val.eq(&2)));
    }

    #[test]
    fn only_one_mutable_borrow() {
        let registry = VecBasedRegistry::new();
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        let mut borrow_1 = registry.try_borrow_mut(&2);
        assert!(borrow_1.as_ref().is_ok_and(|val| val.eq(&3)));
        assert_eq!(
            registry.try_borrow_mut(&2).err(),
            Some(BorrowError::AlreadyBorrowed)
        );
        *borrow_1.as_deref_mut().unwrap() *= 2;
        drop(borrow_1);
        let borrow_2 = registry.try_borrow_mut(&2);
        assert!(borrow_2.as_ref().is_ok_and(|val| val.eq(&6)));
    }

    #[test]
    fn borrows_do_not_interfere() {
        let registry = VecBasedRegistry::new();
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        let borrow_0_1 = registry.try_borrow(&0);
        let borrow_1_1 = registry.try_borrow_mut(&1);
        let borrow_2_1 = registry.try_borrow(&2);
        let borrow_2_2 = registry.try_borrow(&2);
        let borrow_3_1 = registry.try_borrow_mut(&3);
        assert!(borrow_0_1.as_ref().is_ok_and(|val| val.eq(&1)));
        assert!(borrow_1_1.as_ref().is_ok_and(|val| val.eq(&2)));
        assert!(borrow_2_1.as_ref().is_ok_and(|val| val.eq(&3)));
        assert!(borrow_2_2.as_ref().is_ok_and(|val| val.eq(&3)));
        assert!(borrow_3_1.as_ref().is_ok_and(|val| val.eq(&4)));
    }

    #[test]
    fn immutable_borrow_can_be_cloned() {
        let registry = VecBasedRegistry::new();
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        let borrow_1 = registry.borrow(&0);
        let borrow_2 = borrow_1.clone();
        assert!(borrow_1.eq(&1));
        assert!(borrow_2.eq(&1));
        drop(borrow_1);
        assert_eq!(
            registry.try_borrow_mut(&0).err(),
            Some(BorrowError::AlreadyBorrowed)
        );
        drop(borrow_2);
        assert!(registry.try_borrow_mut(&0).is_ok_and(|val| val.eq(&1)));
    }

    #[test]
    fn converts_to_vector() {
        let registry = VecBasedRegistry::new();
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        assert_eq!(registry.into_vec(), vec![1, 2, 3, 4]);
    }

    #[test]
    fn can_insert_with_borrows_out() {
        let registry = VecBasedRegistry::with_capacity(16);
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        let borrow_1 = registry.borrow(&0);
        let borrow_2 = registry.borrow_mut(&1);
        insert_many_into_registry(&registry, 5..100);
        let borrow_3 = registry.borrow(&4);
        let borrow_4 = registry.borrow(&97);
        assert!(borrow_1.eq(&1));
        assert!(borrow_2.eq(&2));
        assert!(borrow_3.eq(&5));
        assert!(borrow_4.eq(&98));
    }

    #[test]
    fn safe_to_drop_tracks_borrows() {
        let mut registry = VecBasedRegistry::new();
        assert!(registry.safe_to_drop());
        insert_many_into_registry(&registry, [1, 2, 3, 4]);
        assert!(registry.safe_to_drop());

        let borrow_1: ElementRef<'_, i32> = unsafe { mem::transmute(registry.borrow(&0)) };
        let borrow_2: ElementRef<'_, i32> = unsafe { mem::transmute(registry.borrow(&0)) };
        let borrow_3: ElementRefMut<'_, i32> = unsafe { mem::transmute(registry.borrow_mut(&1)) };
        assert!(!registry.safe_to_drop());

        assert!(borrow_1.eq(&1));
        assert!(borrow_2.eq(&1));
        assert!(borrow_3.eq(&2));

        drop(borrow_1);
        assert!(!registry.safe_to_drop());
        drop(borrow_2);
        assert!(!registry.safe_to_drop());
        drop(borrow_3);
        assert!(registry.safe_to_drop());
    }
}
