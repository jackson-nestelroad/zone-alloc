#![no_std]

#[cfg(test)]
mod strong_handle_test {
    use zone_alloc::{
        Handle,
        StrongHandle,
        StrongRegistry,
    };
    use zone_alloc_strong_handle_derive::StrongHandle;

    #[derive(Debug, PartialEq, Eq, StrongHandle)]
    struct IntegerHandle(Handle);

    type IntegerRegistry = StrongRegistry<IntegerHandle, u64>;

    #[test]
    fn derives_from_handle() {
        assert_eq!(IntegerHandle::from(0), IntegerHandle(0));
        assert_eq!(IntegerHandle::from(123), IntegerHandle(123));
    }

    #[test]
    fn derives_strong_handle() {
        assert_eq!(IntegerHandle(0).handle(), 0);
        assert_eq!(IntegerHandle(123).handle(), 123);
    }

    #[test]
    fn can_be_used_in_strong_registry() {
        let registry = IntegerRegistry::new();
        let handle = registry.register(123);
        assert_eq!(registry.get(handle).cloned(), Some(123));
        let handle = registry.register(456);
        assert_eq!(registry.get(handle).cloned(), Some(456));
    }
}
