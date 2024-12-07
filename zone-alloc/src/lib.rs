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
//!     registry.get_mut_unchecked(root_handle).parent = Some(handle);
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
//!
//! ## Circular References with [`KeyedRegistry<T>`]
//! ```
//! #[cfg(not(feature = "std"))]
//! extern crate alloc;
//!
//! #[cfg(not(feature = "std"))]
//! use alloc::borrow::ToOwned;
//!
//! use zone_alloc::KeyedRegistry;
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct Node<K, V> {
//!     parent: Option<K>,
//!     value: V,
//! }
//!
//! impl<K, V> Node<K, V> {
//!     pub fn new(parent: Option<K>, value: V) -> Self {
//!         Self { parent, value }
//!     }
//! }
//!
//! fn main() {
//!     let registry = KeyedRegistry::new();
//!     registry.register("node-1".to_owned(), Node::new(None, "first"));
//!     registry.register(
//!         "node-2".to_owned(),
//!         Node::new(Some("node-1".to_owned()), "second"),
//!     );
//!     registry.register(
//!         "node-3".to_owned(),
//!         Node::new(Some("node-2".to_owned()), "third"),
//!     );
//!     registry.get_mut_unchecked("node-1").parent = Some("node-3".to_owned());
//!
//!     let node = registry.get("node-3").unwrap();
//!     assert_eq!(node.value, "third");
//!     let node = registry.get(node.parent.as_ref().unwrap()).unwrap();
//!     assert_eq!(node.value, "second");
//!     let node = registry.get(node.parent.as_ref().unwrap()).unwrap();
//!     assert_eq!(node.value, "first");
//!     let node = registry.get(node.parent.as_ref().unwrap()).unwrap();
//!     assert_eq!(node.value, "third");
//! }
//! ```
//!
//! ## Runtime Borrow Checking
//! ```
//! use zone_alloc::{
//!     BorrowError,
//!     Registry,
//! };
//!
//! fn main() {
//!     let registry = Registry::new();
//!     registry.register_extend(100..200);
//!
//!     // Multiple immutable borrows on the same element.
//!     let borrow_1 = registry.get(16);
//!     let borrow_2 = registry.get(16);
//!     let borrow_3 = registry.get(16);
//!     assert!(borrow_1.as_ref().is_ok_and(|i| i.eq(&116)));
//!     assert!(borrow_2.as_ref().is_ok_and(|i| i.eq(&116)));
//!     assert!(borrow_3.as_ref().is_ok_and(|i| i.eq(&116)));
//!
//!     // Mutable borrow fails.
//!     assert_eq!(
//!         registry.get_mut(16).err(),
//!         Some(BorrowError::AlreadyBorrowed)
//!     );
//!
//!     // Another element can be borrowed independently.
//!     let borrow_4 = registry.get(32);
//!     assert!(borrow_4.as_ref().is_ok_and(|i| i.eq(&132)));
//!     assert!(borrow_1.as_ref().is_ok_and(|i| i.eq(&116)));
//!
//!     // Only one mutable borrow allowed.
//!     let mut borrow_5 = registry.get_mut(64).unwrap();
//!     assert!(borrow_5.eq(&164));
//!     *borrow_5 *= 2;
//!     assert!(borrow_5.eq(&328));
//!     assert_eq!(
//!         registry.get_mut(64).err(),
//!         Some(BorrowError::AlreadyBorrowed)
//!     );
//!     assert_eq!(registry.get(64).err(), Some(BorrowError::AlreadyBorrowed));
//!
//!     // Refetch to show updated value, and show that previous borrows are still valid.
//!     drop(borrow_5);
//!     let borrow_5 = registry.get(64);
//!     assert!(borrow_5.as_ref().is_ok_and(|i| i.eq(&328)));
//!     assert!(borrow_4.as_ref().is_ok_and(|i| i.eq(&132)));
//!     assert!(borrow_1.as_ref().is_ok_and(|i| i.eq(&116)));
//! }
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#![feature(dropck_eyepatch)]
#![feature(sync_unsafe_cell)]
#![feature(trait_alias)]

pub mod arena;
mod base_registry;
mod borrow_error;
pub mod element;
pub mod keyed_registry;
pub mod registry;
mod registry_container;
pub mod strong_registry;

pub use arena::Arena;
pub use borrow_error::BorrowError;
pub use element::{
    ElementRef,
    ElementRefMut,
};
pub use keyed_registry::KeyedRegistry;
pub use registry::{
    Handle,
    Registry,
};
pub use registry_container::Key;
pub use strong_registry::{
    StrongHandle,
    StrongRegistry,
};
