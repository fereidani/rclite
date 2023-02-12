# RcLite: The small reference counting solution for Rust

[![Crates.io][crates-badge]][crates-url]
[![Documentation][doc-badge]][doc-url]
[![MIT licensed][mit-badge]][mit-url]
[![Apache 2 licensed][apache-badge]][apache-url]

[crates-badge]: https://img.shields.io/crates/v/rclite.svg?style=for-the-badge
[crates-url]: https://crates.io/crates/rclite
[mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg?style=for-the-badge
[apache-badge]: https://img.shields.io/badge/license-Apache2-orange.svg?style=for-the-badge
[mit-url]: https://github.com/fereidani/rclite/blob/master/LICENSE-MIT
[apache-url]: https://github.com/fereidani/rclite/blob/master/LICENSE-APACHE
[doc-badge]: https://img.shields.io/docsrs/rclite?style=for-the-badge
[doc-url]: https://docs.rs/rclite

RcLite is a lightweight reference-counting solution for Rust that serves as an alternative to the standard library's reference-counting. It offers both multi-threaded and single-threaded reference counting options with improved performance and reduced memory overhead, boasting a 75% decrease in memory usage compared to the standard reference counting method. RcLite is a suitable option when weak references are not necessary and optimizing for performance and memory usage is a priority.

## Why use RcLite?

- It's faster and smaller
- Uses less memory
- It is a drop-in replacement for standard library Arc and Rc without weak reference feature
- It supports `no_std` with extern alloc

## Why not use RcLite?

- It does not provide weak references
- With RcLite in 64-bit systems, you only can have `4,294,967,296 - 256` live references to an object. if you need to have `18,446,744,073,709,551,616` live references to an object, use the standard library. In other systems with smaller pointer sizes like 32-bit, you will have `usize::MAX` live references limitation that is the same as the standard library.

## Comparison

|                            | rclite::Arc | std::sync::Arc |
| -------------------------- | :---------: | :------------: |
| Overhead in 64-bit systems |   4 bytes   |    16 bytes    |
| Overhead in 32-bit systems |   4 bytes   |    8 bytes     |
| Overhead in 16-bit systems |   2 bytes   |    4 bytes     |
| Weak References            |     ❌      |       ✅       |
