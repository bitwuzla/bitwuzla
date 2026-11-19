//! Port of the C++ API unit tests (`test/unit/api/test_api.cpp`) to the Rust
//! API.
//!
//! Each module corresponds to a section of `test_api.cpp`; test names match
//! the C++ tests (with a trailing `_` where the name would clash with an
//! imported function). Checks on null sorts and terms are not ported since
//! the Rust API cannot represent them.

#[macro_use]
mod common;

mod enums;
mod misc;
mod mk_sort;
mod mk_term;
mod options;
mod parser;
mod printing;
mod solver;
mod sort;
mod term;
mod terminate;
