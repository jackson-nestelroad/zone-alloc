#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::{
    cell::{
        RefCell,
        RefMut,
    },
    cmp,
    iter,
    mem,
    slice,
    str,
};

const MIN_CAPACITY: usize = 1;
const DEFAULT_INITIAL_SIZE: usize = 1024;

/// A container that can be used for arena allocation of values of a given type.
///
/// An [`Arena`] guarantees that all references returned are valid for the lifetime of the arena. A
/// single value can be moved into the arena using [`Arena::alloc`], and multiple values can be
/// moved into one contiguous block of memory owned by the arena using [`Arena::alloc_extend`].
///
/// All items in the arena are deallocated at the same time when the arena goes out of scope. There
/// is no support for controlled dealloation of certain items in memory, so this arena type is most
/// useful for designs where several groups of values should be allocated and deallocated together
/// over the life of a program.
///
/// Internally, arena allocation is achieved by allocating contiguous blocks of memory that are
/// never resized (to ensure values are never moved). All items will be allocated in a single,
/// contiguous block of memory. When the arena's current memory block is full, the block is
/// "committed", and a new, larger block of memory is allocated for future items.
///
/// This data type is not thread safe. In fact, usage across multiple threads will likely panic.
pub struct Arena<T> {
    blocks: RefCell<MemoryBlocks<T>>,
}

/// Memory blocks for arena allocation, in their own struct to enable interior mutability on the
/// arena object.
struct MemoryBlocks<T> {
    current: Vec<T>,
    committed: Vec<Vec<T>>,
}

impl<T> MemoryBlocks<T> {
    fn remaining_space_in_current_block(&self) -> usize {
        self.current.capacity() - self.current.len()
    }

    #[inline(never)]
    #[cold]
    fn reserve(&mut self, num: usize) {
        let double = self
            .current
            .capacity()
            .checked_mul(2)
            .expect("capacity overflow");
        let required = num.checked_next_power_of_two().expect("capacity overflow");
        let new_capacity = cmp::max(double, required);
        if self.current.is_empty() {
            // Small optimization: if the current block has not been used, we can just resize it.
            self.current.reserve(new_capacity);
        } else {
            // Commit the current block and replace it with a new block.
            self.committed.push(mem::replace(
                &mut self.current,
                Vec::with_capacity(new_capacity),
            ));
        }
    }
}

enum IterMutState<'a, T> {
    Committed {
        index: usize,
        iter: slice::IterMut<'a, T>,
    },
    Current {
        iter: slice::IterMut<'a, T>,
    },
}

/// Iterator over mutable elements in an [`Arena`].
pub struct IterMut<'a, T> {
    blocks: RefMut<'a, MemoryBlocks<T>>,
    state: IterMutState<'a, T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            self.state = match self.state {
                IterMutState::Committed {
                    mut index,
                    ref mut iter,
                } => match iter.next() {
                    Some(item) => return Some(item),
                    None => {
                        index += 1;
                        if index < self.blocks.committed.len() {
                            let iter = self.blocks.committed[index].iter_mut();
                            let iter = unsafe { mem::transmute(iter) };
                            IterMutState::Committed { index, iter }
                        } else {
                            let iter = self.blocks.current.iter_mut();
                            let iter = unsafe { mem::transmute(iter) };
                            IterMutState::Current { iter }
                        }
                    }
                },
                IterMutState::Current { ref mut iter } => return iter.next(),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.state {
            IterMutState::Committed { index, iter } => {
                let next = index + 1;
                let known_remainder = self.blocks.current.len()
                    + if next < self.blocks.committed.len() {
                        self.blocks.committed[next..]
                            .iter()
                            .fold(0, |acc, b| acc + b.len())
                    } else {
                        0
                    };
                let (min, max) = iter.size_hint();
                return (known_remainder + min, max.map(|n| n + known_remainder));
            }
            IterMutState::Current { iter } => iter.size_hint(),
        }
    }
}

impl<T> Arena<T> {
    /// Creates a new arena.
    pub fn new() -> Self {
        let size = cmp::max(1, mem::size_of::<T>());
        Self::with_capacity(DEFAULT_INITIAL_SIZE / size)
    }

    /// Creates a new arena with the given capacity.
    pub fn with_capacity(size: usize) -> Self {
        let size = cmp::max(MIN_CAPACITY, size);
        Self {
            blocks: RefCell::new(MemoryBlocks {
                current: Vec::with_capacity(size),
                committed: Vec::new(),
            }),
        }
    }

    /// Checks if the arena is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements allocated in the arena.
    pub fn len(&self) -> usize {
        let blocks = self.blocks.borrow();
        blocks
            .committed
            .iter()
            .fold(blocks.current.len(), |acc, b| acc + b.len())
    }

    /// Allocates a new value in the arena, returning a mutable reference to that value.
    pub fn alloc(&self, value: T) -> &mut T {
        self.alloc_in_current_block(value)
            .unwrap_or_else(|value| self.alloc_in_new_block(value))
    }

    #[inline]
    fn alloc_in_current_block(&self, value: T) -> Result<&mut T, T> {
        let mut blocks = self.blocks.borrow_mut();
        let len = blocks.current.len();
        if blocks.current.len() < blocks.current.capacity() {
            blocks.current.push(value);
            Ok(unsafe { &mut *blocks.current.as_mut_ptr().add(len) })
        } else {
            // Return the value back out so it can be moved to a new block.
            Err(value)
        }
    }

    fn alloc_in_new_block(&self, value: T) -> &mut T {
        &mut self.alloc_extend(iter::once(value))[0]
    }

    /// Allocates the contents of an iterator in the arena into a contiguous block of memory.
    ///
    /// Returns a mutable slice containing all allocated values.
    pub fn alloc_extend<I>(&self, iterable: I) -> &mut [T]
    where
        I: IntoIterator<Item = T>,
    {
        let mut blocks = self.blocks.borrow_mut();
        let mut iter = iterable.into_iter();
        // The index in the current block where our slice starts.
        let mut slice_start_index = 0;
        // Iterators can provide a size hint. If an iterator tells us it needs more space than the
        // current block has, we optimize and just create a new block for the iterator up front.
        let min_size = iter.size_hint().0;
        if min_size > blocks.remaining_space_in_current_block() {
            blocks.reserve(min_size);
            blocks.current.extend(iter);
        } else {
            // We have no size information about the iterator, so we start by adding elements to the
            // current block. If we run out of space, we just allocate a new block for
            // the whole iterator.
            slice_start_index = blocks.current.len();
            let mut i = 0;
            while let Some(value) = iter.next() {
                if blocks.current.len() == blocks.current.capacity() {
                    // Allocate a new block, because the current block doesn't have enough space.
                    let blocks = &mut *blocks;
                    blocks.reserve(i + 1);
                    // Move the elements we added to the previous block to this new block.
                    let prev = blocks.committed.last_mut().unwrap();
                    let prev_len = prev.len();
                    blocks.current.extend(prev.drain(prev_len - i..));
                    blocks.current.push(value);
                    blocks.current.extend(iter);
                    slice_start_index = 0;
                    break;
                }
                blocks.current.push(value);
                i += 1;
            }
        }

        // Extend the lifetime of added elements to the lifetime of `self`.
        // This is valid as long as we ensure we never move or deallocate items.
        unsafe {
            let slice_len = blocks.current.len() - slice_start_index;
            slice::from_raw_parts_mut(
                blocks.current.as_mut_ptr().add(slice_start_index),
                slice_len,
            )
        }
    }

    /// Ensures there is enough continuous space for at least `additional` values.
    pub fn reserve(&self, additional: usize) {
        let mut blocks = self.blocks.borrow_mut();

        if additional > blocks.remaining_space_in_current_block() {
            blocks.reserve(additional);
        }
    }

    /// Converts the [`Arena<T>`] into a [`Vec<T>`].
    ///
    /// Items will be in the same order of allocation in the arena.
    pub fn into_vec(self) -> Vec<T> {
        let mut blocks = self.blocks.into_inner();
        let mut out = Vec::with_capacity(
            blocks
                .committed
                .iter()
                .fold(blocks.current.len(), |acc, b| acc + b.len()),
        );
        for mut block in blocks.committed {
            out.append(&mut block);
        }
        out.append(&mut blocks.current);
        out
    }

    /// Returns an iterator that provides mutable access to all elements in the arena, in order of
    /// allocation.
    ///
    /// Arenas only allow mutable iteration because the entire arena must be borrowed for the
    /// duration of the iteration. The mutable borrow to call this method allows Rust's borrow
    /// checker to enforce this rule.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        let mut blocks = self.blocks.borrow_mut();
        let state = if !blocks.committed.is_empty() {
            let index = 0;
            let iter = blocks.committed[index].iter_mut();
            let iter = unsafe { mem::transmute(iter) };
            IterMutState::Committed { index, iter }
        } else {
            let iter = unsafe { mem::transmute(blocks.current.iter_mut()) };
            IterMutState::Current { iter }
        };
        IterMut { blocks, state }
    }
}

impl Arena<u8> {
    /// Allocates a string slice in the arena, returning a mutable reference to it.
    pub fn alloc_str(&self, s: &str) -> &mut str {
        let slice = self.alloc_extend(s.bytes());
        // Valid because the string came in as utf-8.
        unsafe { str::from_utf8_unchecked_mut(slice) }
    }
}

impl<A> FromIterator<A> for Arena<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let arena = Self::with_capacity(iter.size_hint().0);
        arena.alloc_extend(iter);
        arena
    }
}

#[cfg(test)]
mod arena_test {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::vec;
    use core::{
        cell::Cell,
        mem,
    };

    use crate::Arena;

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
    struct Node<'a, 'd, T> {
        parent: Option<&'a Node<'a, 'd, T>>,
        value: T,
        #[allow(dead_code)]
        drop_counter: DropCounter<'d>,
    }

    impl<'a, 'd, T> Node<'a, 'd, T> {
        pub fn new(
            parent: Option<&'a Node<'a, 'd, T>>,
            value: T,
            drop_counter: DropCounter<'d>,
        ) -> Self {
            Self {
                parent,
                value,
                drop_counter,
            }
        }
    }

    fn commited_blocks<T>(arena: &Arena<T>) -> usize {
        arena.blocks.borrow().committed.len()
    }

    #[test]
    #[allow(dropping_references)]
    fn allocates_and_owns_values() {
        let drop_counter = Cell::new(0);
        {
            let arena = Arena::with_capacity(2);
            assert!(arena.is_empty());

            // Allocate a chain of nodes that refer to each other.
            let mut node: &Node<u32> = arena.alloc(Node::new(None, 1, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 0);
            assert_eq!(arena.len(), 1);
            assert!(!arena.is_empty());
            node = arena.alloc(Node::new(Some(node), 2, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 0);
            assert_eq!(arena.len(), 2);
            node = arena.alloc(Node::new(Some(node), 3, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 1);
            assert_eq!(arena.len(), 3);
            node = arena.alloc(Node::new(Some(node), 4, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 1);
            assert_eq!(arena.len(), 4);

            assert_eq!(node.value, 4);
            assert_eq!(node.parent.unwrap().value, 3);
            assert_eq!(node.parent.unwrap().parent.unwrap().value, 2);
            assert_eq!(
                node.parent.unwrap().parent.unwrap().parent.unwrap().value,
                1
            );
            assert!(node
                .parent
                .unwrap()
                .parent
                .unwrap()
                .parent
                .unwrap()
                .parent
                .is_none());

            // Dropping a node doesn't work. It's trivial (since we return references), but this at
            // least guarantees we don't break our interface.
            mem::drop(node);
            assert_eq!(drop_counter.get(), 0);

            node = arena.alloc(Node::new(None, 5, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 1);
            node = arena.alloc(Node::new(Some(node), 6, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 1);
            node = arena.alloc(Node::new(Some(node), 7, DropCounter(&drop_counter)));
            assert_eq!(commited_blocks(&arena), 2);

            assert_eq!(node.value, 7);
            assert_eq!(node.parent.unwrap().value, 6);
            assert_eq!(node.parent.unwrap().parent.unwrap().value, 5);
            assert!(node.parent.unwrap().parent.unwrap().parent.is_none());

            assert_eq!(drop_counter.get(), 0);
        }
        // All values deallocated at the same time.
        assert_eq!(drop_counter.get(), 7);
    }

    #[test]
    #[cfg(feature = "std")]
    fn allocates_strings() {
        let arena = Arena::new();
        let str = arena.alloc_str("abcd");
        assert_eq!(str, "abcd");
        let str = arena.alloc_str("defg");
        assert_eq!(str, "defg");
        let str = "hijklmnop".to_owned();
        let str = arena.alloc_str(&str);
        assert_eq!(str, "hijklmnop");
    }

    #[test]
    fn supports_circular_reference() {
        struct CircularNode<'a, T> {
            value: T,
            other: Cell<Option<&'a CircularNode<'a, T>>>,
        }

        let arena = Arena::with_capacity(2);
        let a = arena.alloc(CircularNode {
            value: 1,
            other: Cell::new(None),
        });
        let b = arena.alloc(CircularNode {
            value: 2,
            other: Cell::new(None),
        });
        a.other.set(Some(b));
        b.other.set(Some(a));
        assert_eq!(a.other.get().unwrap().value, 2);
        assert_eq!(b.other.get().unwrap().value, 1);
    }

    #[test]
    fn alloc_extend_allocates_and_returns_slice() {
        let arena = Arena::with_capacity(2);
        for i in 0..15 {
            let slice = arena.alloc_extend(0..i);
            for (j, &value) in (0..i).zip(slice.iter()) {
                assert_eq!(j, value)
            }
        }
    }

    #[test]
    fn alloc_extend_allocates_and_owns_values() {
        let drop_counter = Cell::new(0);
        {
            let arena = Arena::with_capacity(2);
            let iter = (0..100).map(|i| Node::new(None, i, DropCounter(&drop_counter)));
            let root = &arena.alloc_extend(iter)[0];
            let iter = (0..100).map(|i| Node::new(Some(root), i, DropCounter(&drop_counter)));
            arena.alloc_extend(iter);
            assert_eq!(drop_counter.get(), 0);
        }
        assert_eq!(drop_counter.get(), 200);
    }

    #[test]
    fn alloc_extend_uses_size_hint() {
        struct Iter<I>(I);
        impl<I> Iterator for Iter<I>
        where
            I: Iterator,
        {
            type Item = I::Item;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (16, None)
            }
        }

        let arena = Arena::with_capacity(10);
        arena.alloc(123);
        // This iterator provides a size hint larger than the current capacity, forcing it into a
        // new block.
        let slice = arena.alloc_extend(Iter(0..4));
        assert_eq!(commited_blocks(&arena), 1);
        assert_eq!(slice.len(), 4);
    }

    #[test]
    fn alloc_extend_ignores_size_hint() {
        struct Iter<I>(I);
        impl<I> Iterator for Iter<I>
        where
            I: Iterator,
        {
            type Item = I::Item;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (2, None)
            }
        }

        let arena = Arena::with_capacity(50);
        arena.alloc(123);
        // This iterator provides a size hint that does not require a new block, but the iterator
        // will exceeds the current block's capacity.
        //
        // Validate that our arena doesn't blindly follow the size hint in this case.
        let slice = arena.alloc_extend(Iter(0..100));
        assert_eq!(commited_blocks(&arena), 1);
        assert_eq!(slice.len(), 100);
    }

    #[test]
    fn alloc_respects_initial_capacity() {
        let arena = Arena::with_capacity(1000);
        arena.alloc_extend(0..1000);
        assert_eq!(commited_blocks(&arena), 0);
    }

    #[test]
    fn reserve_large_block() {
        let arena = Arena::with_capacity(2);
        // Commit the first block and start the next.
        arena.alloc_extend(0..1);
        arena.alloc_extend(0..100);
        // Since the current block has elements in it, a new block is created.
        arena.reserve(1000);
        assert_eq!(commited_blocks(&arena), 2);
        // These should fit in the same block.
        arena.alloc_extend(0..500);
        arena.alloc_extend(501..1000);
        assert_eq!(commited_blocks(&arena), 2);
    }

    #[test]
    fn into_vec_reflects_insertion_order() {
        let arena = Arena::with_capacity(1);
        for &s in &["a", "b", "c", "d"] {
            arena.alloc(s);
        }
        let vec = arena.into_vec();
        assert_eq!(vec, vec!["a", "b", "c", "d"])
    }

    #[test]
    fn iter_mut_itereates_in_order() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoCopy(usize);

        let mut arena = Arena::new();
        for i in 0..10 {
            arena.alloc(NoCopy(i));
        }
        assert!(arena
            .iter_mut()
            .zip((0..10).map(|i| NoCopy(i)))
            .all(|(a, b)| a == &b));
    }

    #[test]
    fn iter_mut_allows_mutable_access() {
        let mut arena = Arena::new();
        for i in 0..10 {
            arena.alloc(i);
        }
        for i in arena.iter_mut() {
            *i += 1
        }
        assert!(arena.iter_mut().zip(1..11).all(|(a, b)| a == &b));
    }

    #[test]
    fn iter_mut_over_multiple_blocks() {
        const LENGTH: usize = 1000;
        const CAPACITY: usize = 4;

        let mut arena = Arena::with_capacity(CAPACITY);
        for i in 0..LENGTH {
            arena.alloc(i);
        }

        assert!(commited_blocks(&arena) > 1);
        assert_eq!(arena.len(), LENGTH);
        assert!(arena.iter_mut().zip(0..LENGTH).all(|(a, b)| a == &b));
    }

    #[test]
    fn iter_mut_over_one_block() {
        const LENGTH: usize = 1000;
        const CAPACITY: usize = 10000;

        let mut arena = Arena::with_capacity(CAPACITY);
        for i in 0..LENGTH {
            arena.alloc(i);
        }

        assert_eq!(commited_blocks(&arena), 0);
        assert_eq!(arena.len(), LENGTH);
        assert!(arena.iter_mut().zip(0..LENGTH).all(|(a, b)| a == &b));
    }

    #[test]
    fn iter_mut_size_hint_is_always_bounded_correctly() {
        const LENGTH: usize = 1000;

        let mut arena = Arena::with_capacity(0);
        for i in 0..LENGTH {
            arena.alloc(i);
        }
        let mut iter = arena.iter_mut().zip((0..LENGTH).rev());
        while let Some((_, remaining)) = iter.next() {
            let (min, max) = iter.size_hint();
            assert!(min <= remaining);
            if let Some(max) = max {
                assert!(max >= remaining)
            }
        }
    }

    #[test]
    fn constructible_from_iterator() {
        let arena: Arena<i32> = (0..100).collect();
        assert_eq!(arena.len(), 100);
    }
}
