//! # bitwuzla
//!
//! Safe, high-level Rust bindings for the [Bitwuzla](https://bitwuzla.github.io)
//! SMT solver, built on its C API (crate `libbitwuzla-sys`).
//!
//! ```
//! use bitwuzla::{Bitwuzla, Kind, Opt, Options, SatResult, TermManager};
//!
//! let tm = TermManager::new();
//! let mut options = Options::new();
//! options.set(Opt::ProduceModels, true)?;
//! let mut bitwuzla = Bitwuzla::new(&tm, &options)?;
//!
//! let bv8 = tm.mk_bv_sort(8);
//! let x = tm.mk_const(&bv8, "x");
//! let y = tm.mk_const(&bv8, "y");
//! // x + y = 3 and x > y (unsigned)
//! let three = tm.mk_bv_value_u64(&bv8, 3);
//! let sum = tm.mk_term(Kind::BvAdd, &[&x, &y], &[]);
//! bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&sum, &three], &[]));
//! bitwuzla.assert_formula(&tm.mk_term(Kind::BvUgt, &[&x, &y], &[]));
//!
//! assert_eq!(bitwuzla.check_sat()?, SatResult::Sat);
//! let x_value = bitwuzla.get_value(&x).value_str(10);
//! let y_value = bitwuzla.get_value(&y).value_str(10);
//! println!("x = {x_value}, y = {y_value}");
//! # Ok::<(), bitwuzla::Error>(())
//! ```
//!
//! # Overview
//!
//! * [`TermManager`] creates [`Sort`]s and [`Term`]s.
//! * [`Options`] configure a [`Bitwuzla`] solver instance.
//! * [`Parser`] parses SMT-LIB v2 and BTOR2 input.
//! * [`Kind`], [`RoundingMode`], [`Opt`] (the C/C++ API's `Option`) and
//!   [`SatResult`] (the C/C++ API's `Result`) are generated from the C API
//!   headers; [`sys`] gives access to the raw C API. Kinds, rounding modes
//!   and results display with Bitwuzla's names (e.g., `BV_ADD`, `RNE`,
//!   `sat`).
//!
//! # Errors and panics
//!
//! As usual in Rust, a call returns [`Result`] only if it can fail for
//! reasons the caller cannot rule out in advance; the [`Error`] carries
//! Bitwuzla's error message. These are calls that
//!
//! * interpret text: [`Parser`], values given as strings
//!   ([`TermManager::mk_bv_value`], [`TermManager::mk_fp_from_real`],
//!   [`TermManager::mk_fp_from_rational`]), and option values
//!   ([`Options::set`]: an invalid mode, a number out of range, or a SAT
//!   solver that is not compiled in),
//! * depend on how Bitwuzla was built or configured: [`Bitwuzla::new`]
//!   (e.g., a SAT solver that is not compiled in) and
//!   [`Bitwuzla::configure_terminator`] (not every SAT solver supports
//!   terminators),
//! * solve: [`Bitwuzla::check_sat`], [`Bitwuzla::check_sat_assuming`],
//!   [`Bitwuzla::simplify`], [`Bitwuzla::simplify_term`], and the
//!   interpolation queries, which fail if Bitwuzla does not support the
//!   formula. Bitwuzla reports this like any other error, so these calls
//!   return `Err` for all errors except terms of different term managers,
//!   including invalid arguments and calls in the wrong state (e.g.,
//!   [`Bitwuzla::get_interpolants`] without [`Opt::ProduceInterpolants`]),
//! * open files ([`Options::set_diagnostic_output_stream`]).
//!
//! All other errors are contract violations: invalid arguments (e.g., a
//! bit-vector sort of size 0, an argument of the wrong sort, terms of
//! different term managers, or an option value of the wrong type) or calls
//! in the wrong state (e.g., [`Bitwuzla::get_value`] without
//! [`Opt::ProduceModels`] or after an unsat result, or calls from a
//! [`Terminator`]). These panic with Bitwuzla's error message, reported at
//! the location of the offending call, like an out-of-bounds index. The
//! objects involved remain usable if the panic is caught.
//!
//! # Ownership
//!
//! Sorts and terms keep their term manager alive, and a solver or parser
//! keeps the term manager alive, so none of these types carry lifetimes.
//! Term managers, sorts, terms, options, solvers and parsers are neither
//! `Send` nor `Sync`: they share unsynchronized state, e.g., the sorts and
//! terms of a term manager, so each must stay on the thread that created it.
//! Separate term managers, each with its own options, solvers and parsers,
//! can be used on separate threads.

mod enums;
mod error;
mod ffi;
mod options;
mod parser;
mod solver;
mod sort;
mod term;
mod term_manager;

pub use enums::{Kind, Opt, RoundingMode, SatResult};
pub use libbitwuzla_sys as sys;

pub use error::{Error, Result};
pub use options::{OptionInfo, OptionKind, OptionValue, Options};
pub use parser::Parser;
pub use solver::{Bitwuzla, Terminator};
pub use sort::Sort;
pub use term::Term;
pub use term_manager::TermManager;

use std::fmt;

use error::call_reentrant;
use ffi::to_string;

/// Get copyright information.
pub fn copyright() -> String {
    call_reentrant(|| unsafe { to_string(sys::bitwuzla_copyright()) })
}

/// Get version information.
pub fn version() -> String {
    call_reentrant(|| unsafe { to_string(sys::bitwuzla_version()) })
}

/// Get git information.
pub fn git_id() -> String {
    call_reentrant(|| unsafe { to_string(sys::bitwuzla_git_id()) })
}

/// Bitwuzla's name of the kind, e.g., `BV_ADD` (as in the C++ API, the C API
/// includes the `BITWUZLA_KIND_` prefix).
impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name =
            call_reentrant(|| unsafe { to_string(sys::bitwuzla_kind_to_string((*self).into())) });
        f.pad(name.strip_prefix("BITWUZLA_KIND_").unwrap_or(&name))
    }
}

/// Bitwuzla's name of the rounding mode, e.g., `RNE` (as in the C++ API, the
/// C API includes the `BITWUZLA_RM_` prefix).
impl fmt::Display for RoundingMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name =
            call_reentrant(|| unsafe { to_string(sys::bitwuzla_rm_to_string((*self).into())) });
        f.pad(name.strip_prefix("BITWUZLA_RM_").unwrap_or(&name))
    }
}

/// The result as printed by Bitwuzla, e.g., `sat`.
impl fmt::Display for SatResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name =
            call_reentrant(|| unsafe { to_string(sys::bitwuzla_result_to_string((*self).into())) });
        f.pad(&name)
    }
}

/// Compiles and runs the examples of the README as doctests.
#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;
