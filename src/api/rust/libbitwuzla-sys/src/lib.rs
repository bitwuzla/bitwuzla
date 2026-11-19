//! # libbitwuzla-sys
//!
//! Low-level FFI bindings for the [Bitwuzla](https://bitwuzla.github.io) SMT
//! solver, generated with bindgen from the C API headers
//! (`bitwuzla/c/bitwuzla.h`, `bitwuzla/c/parser.h`).
//!
//! All items have their C names, see the [C API documentation]. C enums are
//! integer type aliases with one constant per value, e.g., [`BitwuzlaKind`]
//! and [`BITWUZLA_KIND_BV_ADD`].
//!
//! For a safe, idiomatic API, use the `bitwuzla` crate.
//!
//! [C API documentation]: https://bitwuzla.github.io/docs/c/api.html
//!
//! # Errors
//!
//! The C API reports errors by calling the abort callback configured via
//! [`bitwuzla_set_abort_callback`], which by default prints the error and
//! exits. All functions are declared with the `"C-unwind"` ABI, so a callback
//! that unwinds (e.g., via [`std::panic::resume_unwind`]) returns control to
//! the Rust caller of the failing function.
//!
//! # Example
//!
//! ```
//! use libbitwuzla_sys::*;
//!
//! unsafe {
//!     let tm = bitwuzla_term_manager_new();
//!     let options = bitwuzla_options_new();
//!     bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
//!     let bitwuzla = bitwuzla_new(tm, options);
//!
//!     let bv8 = bitwuzla_mk_bv_sort(tm, 8);
//!     let x = bitwuzla_mk_const(tm, bv8, c"x".as_ptr());
//!     let one = bitwuzla_mk_bv_one(tm, bv8);
//!     bitwuzla_assert(bitwuzla, bitwuzla_mk_term2(tm, BITWUZLA_KIND_EQUAL, x, one));
//!     assert_eq!(bitwuzla_check_sat(bitwuzla), BITWUZLA_SAT);
//!
//!     bitwuzla_delete(bitwuzla);
//!     bitwuzla_options_delete(options);
//!     bitwuzla_term_manager_delete(tm);
//! }
//! ```
//!
//! # Supported Bitwuzla versions
//!
//! The bindings require Bitwuzla [`MIN_BITWUZLA_VERSION`], the version of this
//! crate, or newer. The build script rejects older libraries where their
//! version is known.
//!
//! The bindings are generated from the headers of the library found at build
//! time ([`BUILT_BITWUZLA_VERSION`]), and releases may renumber C enum values
//! or change struct layouts. All releases have the same soname, so the
//! dynamic loader may pick up the library of another release than the one
//! built against: [`is_compatible_version`] checks the version reported by
//! [`bitwuzla_version`] at run time.
//!
//! # Rust enums
//!
//! The build script also generates Rust enums for the `bitwuzla` crate, which
//! includes them from the file exported as `DEP_BITWUZLA_RUST_ENUMS`. Deriving
//! them from the same headers keeps them in sync with the linked library.

#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]
#![allow(clippy::all)]
// The generated docs are the C API's Doxygen comments (e.g., "<stdout>").
#![allow(rustdoc::invalid_html_tags)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

mod version;
pub use version::{
    BUILT_BITWUZLA_VERSION, MIN_BITWUZLA_VERSION, is_compatible_version, is_supported_version,
};

unsafe extern "C-unwind" {
    /// Configure an abort callback function, which is called instead of exit
    /// on abort conditions.
    ///
    /// The callback must not return: it either terminates the program or
    /// unwinds, which propagates out of the aborting API call to its caller.
    /// The abort callback is configured per thread.
    pub fn bitwuzla_set_abort_callback(
        fun: ::std::option::Option<unsafe extern "C-unwind" fn(msg: *const ::std::os::raw::c_char)>,
    );
}

#[cfg(test)]
mod tests {
    /// The licence files of the crates are copies of the source tree's.
    #[test]
    fn licenses_match_copying() {
        let Some(root) = option_env!("LIBBITWUZLA_SYS_SOURCE_ROOT") else {
            return;
        };
        let copying = std::fs::read_to_string(std::path::Path::new(root).join("COPYING")).unwrap();
        let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        for license in [manifest.join("LICENSE"), manifest.join("../LICENSE")] {
            assert!(
                std::fs::read_to_string(&license).unwrap() == copying,
                "{} differs from COPYING, copy it again",
                license.display()
            );
        }
    }

    /// The build script accepted the library, so it must report a compatible
    /// version at run time.
    #[test]
    fn linked_version_compatible() {
        // SAFETY: returns a static NUL-terminated string.
        let version = unsafe { std::ffi::CStr::from_ptr(super::bitwuzla_version()) };
        let version = version.to_str().unwrap();
        assert!(super::is_compatible_version(version), "{version}");
    }

    /// The prebuilt bindings (used on docs.rs) must match the generated ones.
    ///
    /// Run with `UPDATE_PREBUILT=1` to update them.
    #[cfg(libbitwuzla_sys_in_tree)]
    #[test]
    fn prebuilt_up_to_date() {
        let out = std::path::Path::new(env!("OUT_DIR"));
        let prebuilt = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("prebuilt");
        let update = std::env::var_os("UPDATE_PREBUILT").is_some();
        for file in ["bindings.rs", "rust_enums.rs"] {
            let generated = std::fs::read_to_string(out.join(file)).unwrap();
            if update {
                std::fs::create_dir_all(&prebuilt).unwrap();
                std::fs::write(prebuilt.join(file), &generated).unwrap();
            } else {
                let checked_in = std::fs::read_to_string(prebuilt.join(file)).unwrap_or_default();
                if checked_in == generated {
                    continue;
                }
                // Show where they differ, e.g., when CI uses another libclang.
                let (line, old, new) = checked_in
                    .lines()
                    .map(Some)
                    .chain(std::iter::repeat(None))
                    .zip(generated.lines().map(Some).chain(std::iter::repeat(None)))
                    .enumerate()
                    .find(|(_, (old, new))| old != new)
                    .map(|(i, (old, new))| (i + 1, old.unwrap_or("<eof>"), new.unwrap_or("<eof>")))
                    .unwrap();
                panic!(
                    "prebuilt/{file} is out of date, run \
                     `UPDATE_PREBUILT=1 cargo test -p libbitwuzla-sys`\n\
                     first difference at line {line}:\n  \
                     prebuilt:  {old}\n  generated: {new}"
                );
            }
        }
    }
}
