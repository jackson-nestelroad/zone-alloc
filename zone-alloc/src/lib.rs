//! Data types for zone-based (also known as region-based or arena-based) data allocation.
//!
//! # Examples
//!
//! ## Linked List Nodes with [`Arena<T>`]
//! ```
//! use zone_alloc::Arena;
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct Node<'a, T> {
//!     parent: Option<&'a Node<'a, T>>,
//!     value: T,
//! }
//!
//! impl<'a, T> Node<'a, T> {
//!     pub fn new(parent: Option<&'a Node<'a, T>>, value: T) -> Self {
//!         Self { parent, value }
//!     }
//! }
//!
//! fn main() {
//!     let arena = Arena::new();
//!     let node = arena.alloc(Node::new(None, 1));
//!     let node = arena.alloc(Node::new(Some(node), 2));
//!     let node = arena.alloc(Node::new(Some(node), 3));
//!
//!     assert_eq!(node.value, 3);
//!     assert_eq!(node.parent.unwrap().value, 2);
//!     assert_eq!(node.parent.unwrap().parent.unwrap().value, 1);
//!     assert_eq!(node.parent.unwrap().parent.unwrap().parent, None);
//! }
//! ```
//!
//! ## Circular References with [`Registry<T>`]
//! ```
//! use zone_alloc::{
//!     Handle,
//!     Registry,
//! };
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct Node<T> {
//!     parent: Option<Handle>,
//!     value: T,
//! }
//!
//! impl<T> Node<T> {
//!     pub fn new(parent: Option<Handle>, value: T) -> Self {
//!         Self { parent, value }
//!     }
//! }
//!
//! fn main() {
//!     let registry = Registry::new();
//!     let root_handle = registry.register(Node::new(None, "first"));
//!     let handle = registry.register(Node::new(Some(root_handle), "second"));
//!     let handle = registry.register(Node::new(Some(handle), "third"));
//!     registry.get_mut(root_handle).unwrap().parent = Some(handle);
//!
//!     let node = registry.get(handle).unwrap();
//!     assert_eq!(node.value, "third");
//!     let node = registry.get(node.parent.unwrap()).unwrap();
//!     assert_eq!(node.value, "second");
//!     let node = registry.get(node.parent.unwrap()).unwrap();
//!     assert_eq!(node.value, "first");
//!     let node = registry.get(node.parent.unwrap()).unwrap();
//!     assert_eq!(node.value, "third");
//! }
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#![feature(trait_alias)]

pub mod arena;
mod keyed_arena;
pub mod registry;
mod strong_registry;

pub use arena::Arena;
pub use keyed_arena::{
    Key,
    KeyMap,
    KeyMapIter,
    KeyedArena,
};
pub use registry::{
    Handle,
    Registry,
};
pub use strong_registry::{
    StrongHandle,
    StrongRegistry,
};
