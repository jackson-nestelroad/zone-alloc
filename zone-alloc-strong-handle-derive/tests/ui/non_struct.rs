use zone_alloc_strong_handle_derive::StrongHandle;

#[derive(StrongHandle)]
enum IntegerHandle {
    Handle(u64),
}

fn main() {}
