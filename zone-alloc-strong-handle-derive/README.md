# zone-alloc-strong-handle-derive

[![Latest Version]][crates.io]

[Latest Version]: https://img.shields.io/crates/v/zone_alloc_strong_handle_derive.svg
[crates.io]: https://crates.io/crates/zone_alloc_strong_handle_derive

This crate provides a procedural macro for deriving the `StrongHandle` interface on simple wrappers around the `Handle` type when working with the `StrongRegistry` container in the [`zone-alloc`](https://crates.io/crates/zone_alloc) crate.

```toml
[dependencies]
zone-alloc = "0.1"
zone-alloc-strong-handle-derive = "0.1"
```

## Usage

This crate defines one procedural macro:

- `StrongHandle` - Automatically derives the `StrongHandle` interface for simple wrappers around the `Handle` type.

## Example

### Linked List Nodes with [`Arena<T>`]

```
use zone_alloc::{
    Handle,
    StrongRegistry,
};
use zone_alloc_strong_handle_derive::StrongHandle;

#[derive(Clone, Copy, Debug, PartialEq, Eq, StrongHandle)]
struct NodeHandle(Handle);

#[derive(Debug, PartialEq, Eq)]
struct Node<T> {
    parent: Option<NodeHandle>,
    value: T,
}

impl<T> Node<T> {
    pub fn new(parent: Option<NodeHandle>, value: T) -> Self {
        Self { parent, value }
    }
}

fn main() {
    let registry = StrongRegistry::<NodeHandle, Node<&str>>::new();
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
