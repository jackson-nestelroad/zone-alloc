# zone-alloc

This repository features Rust crates for zone-based (also known as region-based or arena-based) data allocaiton. Zone-based allocation is a type of memory management in which allocated objects are assigned to a specific zone. Data in the zone remain valid and usable for the lifetime of the zone, and all data in the zone are deallocated together after use.

- [`zone-alloc`](./zone-alloc) - Containers for zone-based data allocation.
- [`zone-alloc-strong-handle-derive`](./zone-alloc-strong-handle-derive) - Procedural macro for zone-alloc StrongHandle types.
