#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

use core::{
    cell::Cell,
    fmt::Debug,
    marker::PhantomData,
    ops::{
        Deref,
        DerefMut,
    },
    ptr::NonNull,
};

/// The state of a borrowed element.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum BorrowState {
    /// The element is not borrowed.
    #[default]
    NotBorrowed,
    /// The element is borrowed with N readers.
    Reading(usize),
    /// The element is borrowed for writing.
    Writing,
}

impl BorrowState {
    #[inline]
    fn add_reader(self) -> Option<Self> {
        match self {
            Self::NotBorrowed => Some(Self::Reading(1)),
            Self::Reading(n) => Some(Self::Reading(n + 1)),
            Self::Writing => None,
        }
    }

    #[inline]
    fn add_reader_unchecked(self) -> Self {
        match self {
            Self::Reading(n) => Self::Reading(n + 1),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn drop_reader(self) -> Self {
        match self {
            Self::Reading(n) if n > 1 => Self::Reading(n - 1),
            _ => Self::NotBorrowed,
        }
    }

    #[inline]
    fn add_writer(self) -> Option<Self> {
        match self {
            Self::NotBorrowed => Some(Self::Writing),
            _ => None,
        }
    }
}

/// A borrow reference, which is a shared reference to an element's borrow state.
#[derive(Debug)]
pub(crate) struct BorrowRef<'borrow> {
    state: &'borrow Cell<BorrowState>,
}

impl<'borrow> BorrowRef<'borrow> {
    pub fn new(state: &'borrow Cell<BorrowState>) -> Option<Self> {
        state.set(state.get().add_reader()?);
        Some(Self { state })
    }
}

impl Clone for BorrowRef<'_> {
    fn clone(&self) -> Self {
        self.state.set(self.state.get().add_reader_unchecked());
        Self { state: self.state }
    }
}

impl Drop for BorrowRef<'_> {
    fn drop(&mut self) {
        self.state.set(self.state.get().drop_reader());
    }
}

/// A mutable borrow reference, which is a reference to an element's borrow state.
#[derive(Debug)]
pub(crate) struct BorrowRefMut<'borrow> {
    state: &'borrow Cell<BorrowState>,
}

impl<'borrow> BorrowRefMut<'borrow> {
    pub fn new(state: &'borrow Cell<BorrowState>) -> Option<Self> {
        state.set(state.get().add_writer()?);
        Some(Self { state })
    }
}

impl Drop for BorrowRefMut<'_> {
    fn drop(&mut self) {
        self.state.set(BorrowState::NotBorrowed);
    }
}

/// An immutably borrowed element.
#[derive(Clone)]
pub struct ElementRef<'borrow, T> {
    value: NonNull<T>,
    #[allow(unused)]
    borrow_ref: BorrowRef<'borrow>,
}

impl<'borrow, T> ElementRef<'borrow, T>
where
    T: 'borrow,
{
    /// Creates a new immutable borrow.
    pub(crate) fn new(value: NonNull<T>, borrow_ref: BorrowRef<'borrow>) -> Self {
        Self { value, borrow_ref }
    }
}

impl<T> Deref for ElementRef<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.value.as_ref() }
    }
}

impl<T> Debug for ElementRef<'_, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

/// A mutably borrowed element.
pub struct ElementRefMut<'borrow, T> {
    value: NonNull<T>,
    #[allow(unused)]
    borrow_ref: BorrowRefMut<'borrow>,
    phantom: PhantomData<&'borrow mut T>,
}

impl<'borrow, T> ElementRefMut<'borrow, T>
where
    T: 'borrow,
{
    /// Creates a new mutable borrow.
    pub(crate) fn new(value: NonNull<T>, borrow_ref: BorrowRefMut<'borrow>) -> Self {
        Self {
            value,
            borrow_ref,
            phantom: PhantomData,
        }
    }
}

impl<T> Deref for ElementRefMut<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.value.as_ref() }
    }
}

impl<T> DerefMut for ElementRefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.value.as_mut() }
    }
}

impl<T> Debug for ElementRefMut<'_, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}
