# rclite Changelog

## [0.4.1] - 2025-12-17

- Update branches to 0.4

## [0.4.0] - 2025-11-05

- Rust std API compatibility fix for `assume_init`.

## [0.3.0] - 2025-09-24

- Added `new_uninit` and `assume_init` API.

## [0.2.8] - 2025-09-01

- Update branches to fix nightly builds.

## [0.2.7] - 2025-03-27

- Removed branches std feature.
- Upgraded branches crate for nightly optimization support.
- Fixed target_pointer_width 8 unexpected cfg condition warning.

## [0.2.4] - 2023-06-02

- Fixed and improved `into_inner`.
- Added `into_inner` to `Rc` and `Arc`.

## [0.2.3] - 2023-05-17

- Refactoring and documentation improvements.
- Implemented `AsRef`.
- Added benchmarks.
- Added `drop_slow` to possibly avoid inlining type T drop.

## [0.2.2] - 2023-03-04

- Added `branches` as a dependency.
- Branch and memory optimizations.

## [0.2.1] - 2023-02-23

- Readme word correction.
- Reduced miri test time.
- Reduced inlining for performance optimization.
- Added Cargo/Miri Test Pipeline for Debug/Release.
- Fixed clippy warnings.

## [0.2.0] - 2023-02-22

- Added `usize-for-small-platforms` default feature.
- Improved standard library compatibility.
- Used C layout for `ArcInner` and `RcInner`.

## [0.1.5] - 2023-02-18

- Added small feature and improved platform compatibility.
