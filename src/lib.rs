#![no_std]
//! # RcLite: small, fast, and memory-friendly reference counting
//!
//! [![Crates.io][crates-badge]][crates-url]
//! [![Documentation][doc-badge]][doc-url]
//! [![MIT licensed][mit-badge]][mit-url]
//! [![Apache 2 licensed][apache-badge]][apache-url]
//!
//! [crates-badge]: https://img.shields.io/crates/v/rclite.svg?style=for-the-badge
//! [crates-url]: https://crates.io/crates/rclite
//! [mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg?style=for-the-badge
//! [apache-badge]: https://img.shields.io/badge/license-Apache2-orange.svg?style=for-the-badge
//! [mit-url]: https://github.com/fereidani/rclite/blob/master/LICENSE-MIT
//! [apache-url]: https://github.com/fereidani/rclite/blob/master/LICENSE-APACHE
//! [doc-badge]: https://img.shields.io/docsrs/rclite?style=for-the-badge
//! [doc-url]: https://docs.rs/rclite
//!
//! RcLite is a lightweight reference-counting solution for Rust that serves as
//! an alternative to the standard library's reference-counting. It offers both
//! multi-threaded and single-threaded reference counting options with improved
//! performance and reduced memory overhead, boasting at least 50% and up to
//! 100% decrease in memory overhead compared to the standard library reference
//! counting. RcLite is a suitable option when weak references are not necessary
//! and optimizing for performance and memory usage is a priority.
//!
//! ## Why use RcLite?
//!
//! - It's faster and smaller
//! - Uses less memory
//! - It provides a lightweight drop-in replacements for standard library
//!   `std::sync::Arc` and `std::rc::Rc`
//! - It supports `no_std` with extern alloc
//!
//! ## Why not use RcLite?
//!
//! - It does not provide weak references
//! - It does not support data as DSTs
//! - With RcLite in 64-bit systems, you only can have `4,294,967,296 - 256`
//!   live references to an object which requires about 32GBs of ram for holding
//!   all these references to this single object location. if you need to have
//!   `18,446,744,073,709,551,616` live references to an object, use the
//!   standard library. In other systems with smaller pointer sizes like 32-bit,
//!   you will have `usize::MAX` live references limitation that is the same as
//!   the standard library.
//!
//! ## Comparison
//!
//! |                            | rclite::{Arc,Rc} | std::\*::{Arc,Rc} |
//! | -------------------------- | :--------------: | :---------------: |
//! | Overhead in 64-bit systems |     4 bytes      |     16 bytes      |
//! | Overhead in 32-bit systems |   4 or 2 bytes   |      8 bytes      |
//! | Overhead in 16-bit systems |   2 or 1 bytes   |      4 bytes      |
//! | Weak References            |        ❌        |        ✅         |
//! | DST Support                |        ❌        |        ✅         |
//!
//! In 64-bit systems, RcLite has an advantage over the standard library's Arc
//! as it can utilize the memory padding area, using only 4 bytes to store the
//! counter. This results in a reduction in memory usage, as there is less
//! memory waste on padding. However, in situations where there is not enough
//! padding available in the structure, RcLite will have an overhead of 8 bytes,
//! which is still half of the standard library's overhead.
//!
//! For instance, in 64-bit systems, `Rc<u32>` and `Arc<u32>` allocate the same
//! amount of memory as `Box<u32>`, since the `Box<u32>` allocation will be
//! padded to `u64` by the allocator.
//!
//! In 32-bit and 16-bit systems, the memory overhead of the RcLite will be 50%
//! of the standard library.
//!
//! ### Features
//!
//! By default, RcLite uses a counter size of half the word size for 64-bit
//! systems, with the `usize-for-small-platforms` feature enabled. This is
//! because overflowing a 32-bit counter is harder compared to overflowing
//! 16-bit counters. If you wish to use the half register size on other
//! platforms, you can disable the default features by setting
//! `default-features = false`. This will result in the use of 16-bit counters
//! on 32-bit platforms and 8-bit counters on 16-bit platforms.

#![warn(missing_docs, missing_debug_implementations)]
extern crate alloc;

// Arc counter definition

#[cfg(target_pointer_width = "64")]
pub(crate) use core::sync::atomic::AtomicU32 as AtomicCounter;

#[cfg(all(
    not(target_pointer_width = "64"),
    not(target_pointer_width = "16"),
    not(target_pointer_width = "8"),
    feature = "usize-for-small-platforms",
))]
pub(crate) use core::sync::atomic::AtomicUsize as AtomicCounter;

#[cfg(all(
    target_pointer_width = "32",
    not(feature = "usize-for-small-platforms")
))]
pub(crate) use core::sync::atomic::AtomicU16 as AtomicCounter;

// Rc counter definition

#[cfg(target_pointer_width = "64")]
pub(crate) use u32 as ucount;

#[cfg(all(
    not(target_pointer_width = "64"),
    feature = "usize-for-small-platforms"
))]
pub(crate) use usize as ucount;

#[cfg(all(
    target_pointer_width = "32",
    not(feature = "usize-for-small-platforms")
))]
pub(crate) use u16 as ucount;

#[cfg(all(
    target_pointer_width = "16",
    not(feature = "usize-for-small-platforms")
))]
pub(crate) use u8 as ucount;

#[cfg(all(target_pointer_width = "8", not(feature = "usize-for-small-platforms")))]
pub(crate) use usize as ucount;

#[cfg(all(not(target_pointer_width = "16"), not(target_pointer_width = "8")))]
mod arc;
mod rc;
#[cfg(all(not(target_pointer_width = "16"), not(target_pointer_width = "8")))]
pub use arc::*;
pub use rc::*;
