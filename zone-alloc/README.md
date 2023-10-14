# zone-alloc

[![Latest Version]][crates.io]

[Latest Version]: https://img.shields.io/crates/v/zone_alloc.svg
[crates.io]: https://crates.io/crates/zone_alloc

This crate provides data types for zone-based (also known as region-based or arena-based) data allocation. Zone-based allocation is a type of memory management in which allocated objects are assigned to a specific zone. Data in the zone remain valid and usable for the lifetime of the zone, and all data in the zone are deallocated together after use.

```toml
[dependencies]
zone-alloc = "0.1"
```

## Usage

This crate defines three containers:

- `Arena<T>` - A container that can be used for arena allocation of values of a given type.
- `Registry<T>` - An extension of `Arena<T>` that provides integer handles for allocated data.
- `StrongRegistry<H, T>` - An extension of `Registry<T>` that provides strongly-typed handles for allocated data.

## Additional Crates

- [`zone-alloc-strong-handle-derive`](https://crates.io/crates/zone_alloc_strong_handle_derive) - Procedural macro for deriving the `StrongHandle` interface on simple wrappers around the `Handle` type when working with `StrongRegistry`.

## Features

While the crate is by default built with the Rust standard library, this feature can be removed for no-std environments.

- `default` - `std`
- `std` - Depend on the Rust standard library.

## Examples

### Linked List Nodes with `Arena<T>`

```
use zone_alloc::Arena;

#[derive(Debug, PartialEq, Eq)]
struct Node<'a, T> {
    parent: Option<&'a Node<'a, T>>,
    value: T,
}

impl<'a, T> Node<'a, T> {
    pub fn new(parent: Option<&'a Node<'a, T>>, value: T) -> Self {
        Self { parent, value }
    }
}

fn main() {
    let arena = Arena::new();
    let node = arena.alloc(Node::new(None, 1));
    let node = arena.alloc(Node::new(Some(node), 2));
    let node = arena.alloc(Node::new(Some(node), 3));

    assert_eq!(node.value, 3);
    assert_eq!(node.parent.unwrap().value, 2);
    assert_eq!(node.parent.unwrap().parent.unwrap().value, 1);
    assert_eq!(node.parent.unwrap().parent.unwrap().parent, None);
}
```

### Circular References with `Registry<T>`

```
use zone_alloc::{
    Handle,
    Registry,
};

#[derive(Debug, PartialEq, Eq)]
struct Node<T> {
    parent: Option<Handle>,
    value: T,
}

impl<T> Node<T> {
    pub fn new(parent: Option<Handle>, value: T) -> Self {
        Self { parent, value }
    }
}

fn main() {
    let registry = Registry::new();
    let root_handle = registry.register(Node::new(None, "first"));
    let handle = registry.register(Node::new(Some(root_handle), "second"));
    let handle = registry.register(Node::new(Some(handle), "third"));
    registry.get_mut(root_handle).unwrap().parent = Some(handle);

    let node = registry.get(handle).unwrap();
    assert_eq!(node.value, "third");
    let node = registry.get(node.parent.unwrap()).unwrap();
    assert_eq!(node.value, "second");
    let node = registry.get(node.parent.unwrap()).unwrap();
    assert_eq!(node.value, "first");
    let node = registry.get(node.parent.unwrap()).unwrap();
    assert_eq!(node.value, "third");
}
```
