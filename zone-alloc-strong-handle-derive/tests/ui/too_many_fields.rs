use zone_alloc::Handle;
use zone_alloc_strong_handle_derive::StrongHandle;

#[derive(StrongHandle)]
struct IntegerHandle(Handle, bool);

fn main() {}
