//! Helpers for converting between Rust and C API values.

use std::collections::BTreeMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::path::Path;

use crate::error::{Error, Result, try_call, unwrap};

/// Convert a C enum value returned by the C API to its Rust enum.
///
/// The Rust enums are generated from the headers of the linked library, so
/// an unknown value means the headers and the library do not match.
///
/// Generic over the C type, whose signedness depends on the platform.
pub(crate) fn from_c<C: std::fmt::Display, E: TryFrom<C, Error = C>>(value: C) -> E {
    E::try_from(value).unwrap_or_else(|v| {
        panic!(
            "unknown {} value {v}: Bitwuzla headers and library do not match",
            std::any::type_name::<E>()
        )
    })
}

/// Copy a C string into a `String`, mapping `NULL` to `""`.
///
/// # Safety
///
/// If non-`NULL`, `ptr` must point to a NUL-terminated string. The C API
/// returns most strings in thread-local buffers that the next call overwrites,
/// so this must be called before the next C API call.
pub(crate) unsafe fn to_string(ptr: *const c_char) -> String {
    if ptr.is_null() {
        String::new()
    } else {
        unsafe { CStr::from_ptr(ptr) }
            .to_string_lossy()
            .into_owned()
    }
}

/// Copy a C string into a `String`, mapping `NULL` to `None`.
///
/// # Safety
///
/// See [`to_string`].
pub(crate) unsafe fn to_opt_string(ptr: *const c_char) -> Option<String> {
    (!ptr.is_null()).then(|| unsafe { to_string(ptr) })
}

/// Convert input to a C string; interior NUL bytes are an error.
pub(crate) fn try_cstring(s: &str) -> Result<CString> {
    CString::new(s).map_err(|_| Error::new(format!("string contains a NUL byte: {s:?}")))
}

/// Convert a path to a C string. Fails on interior NUL bytes and, except on
/// Unix, where paths are bytes, on paths that are not valid UTF-8.
pub(crate) fn try_path_cstring(path: &Path) -> Result<CString> {
    #[cfg(unix)]
    let bytes = std::os::unix::ffi::OsStrExt::as_bytes(path.as_os_str());
    #[cfg(not(unix))]
    let bytes = path
        .to_str()
        .ok_or_else(|| Error::new(format!("path is not valid UTF-8: {path:?}")))?
        .as_bytes();
    CString::new(bytes).map_err(|_| Error::new(format!("path contains a NUL byte: {path:?}")))
}

/// Convert to a C string; panics on interior NUL bytes.
#[track_caller]
pub(crate) fn cstring(s: &str) -> CString {
    match try_cstring(s) {
        Ok(c) => c,
        Err(e) => panic!("{e}"),
    }
}

/// Convert an optional symbol to a C string (`None` stays `None`).
#[track_caller]
pub(crate) fn opt_cstring(s: Option<&str>) -> Option<CString> {
    s.map(cstring)
}

/// Pointer for an optional C string, `NULL` for `None`.
pub(crate) fn opt_ptr(s: &Option<CString>) -> *const c_char {
    s.as_ref().map_or(std::ptr::null(), |c| c.as_ptr())
}

/// View a C-owned array as a slice, treating `NULL` as empty.
///
/// # Safety
///
/// If non-`NULL` and `len > 0`, `ptr` must point to `len` initialized values
/// that stay valid for `'a`. The C API returns arrays in thread-local buffers
/// that the next call overwrites.
pub(crate) unsafe fn slice<'a, T>(ptr: *const T, len: usize) -> &'a [T] {
    if ptr.is_null() || len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }
}

/// Copy statistics returned as parallel key/value arrays.
///
/// # Safety
///
/// `keys` and `values` must point to `size` C strings each.
pub(crate) unsafe fn statistics(
    keys: *const *const c_char,
    values: *const *const c_char,
    size: usize,
) -> BTreeMap<String, String> {
    let keys = unsafe { slice(keys, size) };
    let values = unsafe { slice(values, size) };
    keys.iter()
        .zip(values)
        .map(|(&k, &v)| unsafe { (to_string(k), to_string(v)) })
        .collect()
}

/// Run `f` with a temporary C `FILE` and return what it wrote, panicking if
/// Bitwuzla reports an error.
#[track_caller]
pub(crate) fn capture_output(f: impl FnOnce(*mut libc::FILE)) -> String {
    unwrap(try_capture_output(f))
}

/// Run `f` with a temporary C `FILE` and return what it wrote.
#[track_caller]
pub(crate) fn try_capture_output(f: impl FnOnce(*mut libc::FILE)) -> Result<String> {
    struct File(*mut libc::FILE);
    impl Drop for File {
        fn drop(&mut self) {
            unsafe { libc::fclose(self.0) };
        }
    }

    let file = unsafe { libc::tmpfile() };
    assert!(
        !file.is_null(),
        "failed to create temporary file: {}",
        std::io::Error::last_os_error()
    );
    let file = File(file);
    try_call(|| f(file.0))?;
    let mut out = Vec::new();
    unsafe {
        libc::fflush(file.0);
        libc::rewind(file.0);
        let mut buf = [0u8; 4096];
        loop {
            let n = libc::fread(buf.as_mut_ptr().cast(), 1, buf.len(), file.0);
            if n == 0 {
                break;
            }
            out.extend_from_slice(&buf[..n]);
        }
    }
    Ok(String::from_utf8_lossy(&out).into_owned())
}
