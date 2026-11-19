//! Error reporting.
//!
//! The Bitwuzla C API reports errors through an abort callback, which by
//! default prints the error and exits. These bindings install a callback (per
//! thread, on first use) that unwinds back into Rust with the error message,
//! where it is caught at the API boundary. All `libbitwuzla-sys` functions use
//! the `"C-unwind"` ABI, so this unwinding is well-defined.
//!
//! Errors that depend on input ([`try_call`]) are returned as an [`Error`],
//! all others ([`call`]) are contract violations and panic with the error
//! message at the caller's location (see the crate documentation).
//!
//! If the crate is built with `panic = "abort"`, errors cannot be recovered:
//! the error is printed and the process aborts.

use std::cell::Cell;
use std::ffi::CStr;
use std::fmt;
use std::os::raw::c_char;
use std::panic::{self, AssertUnwindSafe};

use libbitwuzla_sys as sys;

/// A failed Bitwuzla call, carrying the error message Bitwuzla reported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    message: String,
}

impl Error {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    /// The error message.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

/// Result of a fallible Bitwuzla call.
///
/// The result of a satisfiability check is [`crate::SatResult`].
pub type Result<T> = std::result::Result<T, Error>;

/// Panic payload that carries an abort out of the C API.
struct Abort(Error);

/// Strip the prefix the C API adds to every abort message.
fn clean_message(msg: &str) -> &str {
    let msg = msg.trim();
    msg.strip_prefix("bitwuzla: error:")
        .map(str::trim_start)
        .unwrap_or(msg)
}

unsafe extern "C-unwind" fn abort_callback(msg: *const c_char) {
    let msg = if msg.is_null() {
        String::new()
    } else {
        // SAFETY: the C API passes a NUL-terminated message.
        clean_message(&unsafe { CStr::from_ptr(msg) }.to_string_lossy()).to_owned()
    };
    #[cfg(panic = "abort")]
    {
        eprintln!("bitwuzla: error: {msg}");
        std::process::abort();
    }
    // Does not invoke the panic hook, so nothing is printed.
    #[cfg(not(panic = "abort"))]
    panic::resume_unwind(Box::new(Abort(Error::new(msg))));
}

thread_local! {
    static ABORT_CALLBACK_INSTALLED: Cell<bool> = const { Cell::new(false) };
    /// Whether a terminator runs on this thread, see [`run_terminator`].
    static IN_TERMINATOR: Cell<bool> = const { Cell::new(false) };
}

#[inline]
fn install_abort_callback() {
    ABORT_CALLBACK_INSTALLED.with(|installed| {
        if !installed.get() {
            check_version();
            // SAFETY: the callback never returns, as the C API requires.
            unsafe { sys::bitwuzla_set_abort_callback(Some(abort_callback)) };
            installed.set(true);
        }
    });
}

/// Panic if the library loaded at run time cannot be used with these
/// bindings: it must not be older than them (they rely on its abort callback
/// being allowed to unwind) and must be of the release the bindings were
/// generated for. All Bitwuzla releases have the same soname, so the dynamic
/// loader may pick up another library than the one built against.
#[cold]
fn check_version() {
    // SAFETY: returns a static NUL-terminated string.
    let version = unsafe { CStr::from_ptr(sys::bitwuzla_version()) }.to_string_lossy();
    assert!(
        sys::is_compatible_version(&version),
        "Bitwuzla {version} cannot be used with these bindings, which require {}",
        match sys::BUILT_BITWUZLA_VERSION {
            Some(built) => format!("the release they were built for, Bitwuzla {built}"),
            None => format!("Bitwuzla {} or newer", sys::MIN_BITWUZLA_VERSION),
        }
    );
}

/// Run a terminator, which the solver calls in the middle of a solver call.
///
/// Calls into Bitwuzla from the terminator panic (see [`try_call`]): solver
/// calls are not reentrant (e.g., replacing the terminator of the solver
/// would free it while it runs), and the C API shares its result buffers
/// across the instances of a thread. Only [`call_reentrant`] calls are
/// allowed.
pub(crate) fn run_terminator<T>(f: impl FnOnce() -> T) -> T {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            IN_TERMINATOR.set(false);
        }
    }
    IN_TERMINATOR.set(true);
    let _reset = Reset;
    f()
}

/// Run a C API call and return an abort as `Err`.
///
/// Every call into the C API goes through this function, [`call`], or
/// [`call_reentrant`]: it installs the abort callback for the current thread
/// and catches the unwind. Only for calls whose errors depend on input, see
/// [`call`]. Panics in a terminator (see [`run_terminator`]).
#[inline]
#[track_caller]
pub(crate) fn try_call<T>(f: impl FnOnce() -> T) -> Result<T> {
    assert!(
        !IN_TERMINATOR.get(),
        "a terminator must not use Bitwuzla objects other than to clone or drop them"
    );
    catch_abort(f)
}

/// [`call`] for the calls allowed in a terminator: copying and releasing
/// sorts and terms, deleting objects (the solver call in progress keeps its
/// own objects alive), and functions that do not use any object.
#[inline]
#[track_caller]
pub(crate) fn call_reentrant<T>(f: impl FnOnce() -> T) -> T {
    unwrap(catch_abort(f))
}

#[inline]
fn catch_abort<T>(f: impl FnOnce() -> T) -> Result<T> {
    install_abort_callback();
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => Ok(value),
        Err(payload) => match payload.downcast::<Abort>() {
            Ok(abort) => Err(abort.0),
            Err(payload) => panic::resume_unwind(payload),
        },
    }
}

/// Run a C API call whose errors are contract violations (invalid arguments
/// or calls in the wrong state) and panic on an abort.
#[inline]
#[track_caller]
pub(crate) fn call<T>(f: impl FnOnce() -> T) -> T {
    unwrap(try_call(f))
}

/// Panic with the message of an error that is a contract violation.
///
/// With `#[track_caller]` on every function up to the public API, the panic
/// is reported at the location of the offending call in user code.
#[inline]
#[track_caller]
pub(crate) fn unwrap<T>(res: Result<T>) -> T {
    match res {
        Ok(value) => value,
        Err(e) => panic!("{e}"),
    }
}

#[cfg(test)]
mod tests {
    use super::clean_message;

    #[test]
    fn strips_prefix() {
        assert_eq!(
            clean_message("bitwuzla: error:  invalid call to 'f', bad\n"),
            "invalid call to 'f', bad"
        );
        assert_eq!(clean_message("other\n"), "other");
    }
}
