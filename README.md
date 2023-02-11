# RCLite: Simple reference counting for rust

[![Crates.io][crates-badge]][crates-url]
[![Documentation][doc-badge]][doc-url]
[![MIT licensed][mit-badge]][mit-url]
[![Apache 2 licensed][apache-badge]][apache-url]

[crates-badge]: https://img.shields.io/crates/v/rclite.svg
[crates-url]: https://crates.io/crates/rclite
[mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[apache-badge]: https://img.shields.io/badge/license-Apache2-orange.svg
[mit-url]: https://github.com/fereidani/rclite/blob/master/LICENSE-MIT
[apache-url]: https://github.com/fereidani/rclite/blob/master/LICENSE-APACHE
[doc-badge]: https://docs.rs/rclite/badge.svg
[doc-url]: https://docs.rs/rclite

RCLite is a lightweight reference-counting solution for Rust that serves as an alternative to the standard library's reference-counting. It offers both multi-threaded and single-threaded reference counting options with improved performance and reduced memory overhead, boasting a 75% decrease in memory usage compared to the standard reference counting method. RCLite is a suitable option when weak references are not necessary and optimizing for performance and memory usage is a priority.

## Why use RCLite?

- It's faster and smaller
- Uses less memory
- It is a drop-in replacement for standard library Arc and Rc without weak reference feature
- It supports `no_std`

## Why not use RCLite?

- It does not provide weak references
- With RCLite in 64-bit systems, you only can have 4,294,967,296 live references to an object. if you need to have 18,446,744,073,709,551,616 live references to an object, use the standard library. In other systems with smaller pointer sizes like 32-bit, you will have usize::MAX live references limitation that is the same as the standard library.
