#![no_std]
#![doc = include_str!("../README.md")]
#![warn(missing_docs, missing_debug_implementations)]

extern crate alloc;

#[cfg(target_pointer_width = "64")]
pub(crate) use core::sync::atomic::AtomicU32 as AtomicCounter;
#[cfg(target_pointer_width = "64")]
pub(crate) use u32 as ucount;

#[cfg(not(target_pointer_width = "64"))]
pub(crate) use core::sync::atomic::AtomicUsize as AtomicCounter;
#[cfg(not(target_pointer_width = "64"))]
pub(crate) use usize as ucount;

mod arc;
mod rc;
pub use arc::*;
pub use rc::*;
