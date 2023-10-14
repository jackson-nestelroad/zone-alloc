//! Procedural macro for deriving the [`zone_alloc::StrongHandle`] interface on simple wrappers
//! around [`zone_alloc::Handle`].
//!
//! # Example
//! ```
//! use zone_alloc::{
//!     Handle,
//!     StrongRegistry,
//! };
//! use zone_alloc_strong_handle_derive::StrongHandle;
//!
//! #[derive(Clone, Copy, Debug, PartialEq, Eq, StrongHandle)]
//! struct NodeHandle(Handle);
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct Node<T> {
//!     parent: Option<NodeHandle>,
//!     value: T,
//! }
//!
//! impl<T> Node<T> {
//!     pub fn new(parent: Option<NodeHandle>, value: T) -> Self {
//!         Self { parent, value }
//!     }
//! }
//!
//! fn main() {
//!     let registry = StrongRegistry::<NodeHandle, Node<&str>>::new();
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

#![no_std]

extern crate proc_macro;

mod parse;

use parse::Input;
use proc_macro::TokenStream;
use proc_macro2::{
    Ident,
    Span,
};
use proc_macro_crate::{
    crate_name,
    FoundCrate,
};
use quote::quote;
use syn::parse_macro_input;

#[proc_macro_derive(StrongHandle)]
pub fn derive_strong_handle(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as Input);
    let ident = input.ident;

    let call_site = Span::call_site();
    let found_crate = crate_name("zone-alloc").expect("zone-alloc is present in `Cargo.toml`");
    let crate_token = match found_crate {
        FoundCrate::Itself => quote!(crate),
        FoundCrate::Name(name) => {
            let ident = Ident::new(&name, call_site);
            quote!(#ident)
        }
    };
    let handle_type = quote! {
        #crate_token::Handle
    };
    let strong_handle = quote! {
        #crate_token::StrongHandle
    };

    TokenStream::from(quote! {
        impl core::convert::From<#handle_type> for #ident {
            fn from(value: #handle_type) -> Self {
                Self(value.into())
            }
        }
        impl #strong_handle for #ident {
            fn handle(&self) -> #handle_type {
                self.0
            }
        }
    })
}
