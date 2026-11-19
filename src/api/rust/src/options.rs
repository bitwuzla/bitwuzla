use std::rc::Rc;

use libbitwuzla_sys as sys;

use crate::Opt;
use crate::error::{Error, Result, call, call_reentrant, try_call};
use crate::ffi::{from_c, slice, to_opt_string, to_string, try_cstring};

/// The configuration options of a [`Bitwuzla`](crate::Bitwuzla) instance.
///
/// Options are copied into a solver (or parser) on construction; changing
/// them afterwards does not affect existing instances, except for redirecting
/// diagnostic output from one file to another (see
/// [`Options::set_diagnostic_output_stream`]). A parser copies them again
/// when it creates a new solver on `(reset)`. A solver (or parser) keeps its
/// options alive since it writes to their diagnostic output stream.
///
/// ```
/// use bitwuzla::{Opt, Options};
///
/// let mut options = Options::new();
/// options.set(Opt::ProduceModels, true)?;
/// options.set(Opt::BvSolver, "prop")?;
/// assert_eq!(options.get(Opt::ProduceModels), 1);
/// assert_eq!(options.get_mode(Opt::BvSolver), "prop");
/// # Ok::<(), bitwuzla::Error>(())
/// ```
pub struct Options {
    handle: Rc<OptionsHandle>,
}

/// Owning handle of C options; deleted when the last reference (held by
/// `Options`, `Bitwuzla`, and `Parser` values) is dropped.
pub(crate) struct OptionsHandle(*mut sys::BitwuzlaOptions);

impl Drop for OptionsHandle {
    fn drop(&mut self) {
        call_reentrant(|| unsafe { sys::bitwuzla_options_delete(self.0) });
    }
}

impl Default for Options {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for Options {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Options({:p})", self.handle.0)
    }
}

impl Options {
    /// Create a new set of options with default values.
    pub fn new() -> Self {
        Self {
            handle: Rc::new(OptionsHandle(call(|| unsafe {
                sys::bitwuzla_options_new()
            }))),
        }
    }

    /// The raw C API handle (not owned).
    pub fn as_raw(&self) -> *mut sys::BitwuzlaOptions {
        self.handle.0
    }

    pub(crate) fn handle(&self) -> Rc<OptionsHandle> {
        Rc::clone(&self.handle)
    }

    /// Redirect diagnostic output (e.g., verbose output) to the given file.
    /// `"<stdout>"` and `"<stderr>"` denote stdout and stderr.
    ///
    /// Solvers and parsers created with these options while they wrote to a
    /// file write to the new file as well: the file is replaced in place.
    pub fn set_diagnostic_output_stream(&mut self, filename: &str) -> Result<()> {
        let filename = try_cstring(filename)?;
        try_call(|| unsafe {
            sys::bitwuzla_options_set_diagnostic_output_stream(self.handle.0, filename.as_ptr())
        })
    }

    /// Determine if `name` is a valid short or long option name.
    pub fn is_valid(&self, name: &str) -> bool {
        match try_cstring(name) {
            Ok(name) => {
                call(|| unsafe { sys::bitwuzla_option_is_valid(self.handle.0, name.as_ptr()) })
            }
            Err(_) => false,
        }
    }

    /// Determine if the option is a Boolean option.
    pub fn is_bool(&self, opt: Opt) -> bool {
        call(|| unsafe { sys::bitwuzla_option_is_bool(self.handle.0, opt.into()) })
    }

    /// Determine if the option is a numeric option (and not a Boolean one,
    /// unlike `bitwuzla_option_is_numeric` of the C API).
    pub fn is_numeric(&self, opt: Opt) -> bool {
        !self.is_bool(opt)
            && call(|| unsafe { sys::bitwuzla_option_is_numeric(self.handle.0, opt.into()) })
    }

    /// Determine if the option is an option with modes.
    pub fn is_mode(&self, opt: Opt) -> bool {
        call(|| unsafe { sys::bitwuzla_option_is_mode(self.handle.0, opt.into()) })
    }

    /// Determine if the option is an option with a string value.
    pub fn is_str(&self, opt: Opt) -> bool {
        call(|| unsafe { sys::bitwuzla_option_is_string(self.handle.0, opt.into()) })
    }

    /// The short name of the option, if any.
    pub fn shrt(&self, opt: Opt) -> Option<String> {
        self.info(opt).shrt
    }

    /// The long name of the option.
    pub fn lng(&self, opt: Opt) -> String {
        self.info(opt).lng
    }

    /// The description of the option.
    pub fn description(&self, opt: Opt) -> String {
        self.info(opt).description
    }

    /// The available modes of an option with modes (empty otherwise).
    pub fn modes(&self, opt: Opt) -> Vec<String> {
        match self.info(opt).kind {
            OptionKind::Mode { modes, .. } => modes,
            _ => Vec::new(),
        }
    }

    /// Get the option with the given short or long name, or `None` if there
    /// is no such option.
    pub fn option(&self, name: &str) -> Option<Opt> {
        if !self.is_valid(name) {
            return None;
        }
        // A valid name has no interior NUL.
        let name = try_cstring(name).ok()?;
        Some(from_c(call(|| unsafe {
            sys::bitwuzla_option_from_name(self.handle.0, name.as_ptr())
        })))
    }

    /// Set the value of an option.
    ///
    /// Boolean options take a `bool`, numeric options an integer, options
    /// with modes and string options a string. Returns an error if Bitwuzla
    /// rejects the value (e.g., an invalid mode, a number out of range, or a
    /// SAT solver that is not compiled in), and panics if the value has the
    /// wrong type for the option.
    #[track_caller]
    pub fn set<V: OptionValue>(&mut self, opt: Opt, value: V) -> Result<()> {
        // The type of an option is fixed, a mismatch is a contract violation.
        let (valid, expected) = match V::KIND {
            ValueKind::Bool => (self.is_bool(opt), "Boolean option"),
            ValueKind::Numeric => (self.is_numeric(opt), "numeric option"),
            ValueKind::Str => (
                self.is_mode(opt) || self.is_str(opt),
                "option with option modes or strings",
            ),
        };
        if !valid {
            let takes = if self.is_bool(opt) {
                "a Boolean"
            } else if self.is_numeric(opt) {
                "a number"
            } else if self.is_mode(opt) {
                "an option mode"
            } else {
                "a string"
            };
            panic!("expected {expected}, --{} takes {takes}", self.lng(opt));
        }
        value.set(self, opt)
    }

    /// Set the option with the given short or long name (without leading
    /// dashes) to a value given as a string: `"true"`, `"false"`, `"1"`, or
    /// `"0"` for Boolean options, a decimal number for numeric options, and
    /// the mode or string for options with modes and string options.
    ///
    /// ```
    /// use bitwuzla::{Opt, Options};
    ///
    /// let mut options = Options::new();
    /// options.set_by_name("produce-models", "true")?;
    /// options.set_by_name("v", "2")?;
    /// assert_eq!(options.get(Opt::ProduceModels), 1);
    /// assert_eq!(options.get(Opt::Verbosity), 2);
    /// # Ok::<(), bitwuzla::Error>(())
    /// ```
    ///
    /// Returns an error if there is no such option or Bitwuzla rejects the
    /// value.
    pub fn set_by_name(&mut self, name: &str, value: &str) -> Result<()> {
        let name = try_cstring(name)?;
        let value = try_cstring(value)?;
        try_call(|| unsafe {
            sys::bitwuzla_set_option_by_name(self.handle.0, name.as_ptr(), value.as_ptr())
        })
    }

    /// Set options from command line arguments (without the program name),
    /// in the following forms:
    ///
    /// ```text
    /// -short    -short=val    -short val
    /// --long    --long=val    --long val
    /// ```
    ///
    /// Boolean options are enabled if no value is given, and disabled via
    /// prefix `--no-` of their long name. Numeric options that allow
    /// increments (e.g., `-v`) are incremented by one if no value is given.
    ///
    /// ```
    /// use bitwuzla::{Opt, Options};
    ///
    /// let mut options = Options::new();
    /// options.set_args(["-v", "-v", "--bv-solver=prop", "--no-produce-models"])?;
    /// assert_eq!(options.get(Opt::Verbosity), 2);
    /// assert_eq!(options.get_mode(Opt::BvSolver), "prop");
    /// # Ok::<(), bitwuzla::Error>(())
    /// ```
    ///
    /// Returns an error for an unknown option or a value Bitwuzla rejects.
    /// The arguments before it are applied.
    pub fn set_args<I, S>(&mut self, args: I) -> Result<()>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let args = args
            .into_iter()
            .map(|arg| try_cstring(arg.as_ref()))
            .collect::<Result<Vec<_>>>()?;
        let mut ptrs: Vec<_> = args.iter().map(|arg| arg.as_ptr()).collect();
        let argc = u32::try_from(ptrs.len()).expect("too many arguments");
        try_call(|| unsafe {
            sys::bitwuzla_options_set_args(self.handle.0, argc, ptrs.as_mut_ptr())
        })
    }

    fn set_numeric(&mut self, opt: Opt, value: u64) -> Result<()> {
        try_call(|| unsafe { sys::bitwuzla_set_option(self.handle.0, opt.into(), value) })
    }

    fn set_str(&mut self, opt: Opt, value: &str) -> Result<()> {
        let value = try_cstring(value)?;
        if self.is_mode(opt) {
            try_call(|| unsafe {
                sys::bitwuzla_set_option_mode(self.handle.0, opt.into(), value.as_ptr())
            })
        } else {
            try_call(|| unsafe {
                sys::bitwuzla_set_option_string(self.handle.0, opt.into(), value.as_ptr())
            })
        }
    }

    /// Get the current value of a Boolean (0 or 1) or numeric option.
    #[track_caller]
    pub fn get(&self, opt: Opt) -> u64 {
        call(|| unsafe { sys::bitwuzla_get_option(self.handle.0, opt.into()) })
    }

    /// Get the current mode of an option with modes.
    #[track_caller]
    pub fn get_mode(&self, opt: Opt) -> String {
        call(|| unsafe { to_string(sys::bitwuzla_get_option_mode(self.handle.0, opt.into())) })
    }

    /// Get the current value of a string option.
    #[track_caller]
    pub fn get_str(&self, opt: Opt) -> String {
        call(|| unsafe { to_string(sys::bitwuzla_get_option_string(self.handle.0, opt.into())) })
    }

    /// Get the details of an option.
    pub fn info(&self, opt: Opt) -> OptionInfo {
        // The C API reports Boolean options as numeric options.
        let is_bool = self.is_bool(opt);
        call(|| unsafe {
            let mut info = std::mem::MaybeUninit::<sys::BitwuzlaOptionInfo>::zeroed();
            sys::bitwuzla_get_option_info(self.handle.0, opt.into(), info.as_mut_ptr());
            OptionInfo::from_raw(&info.assume_init(), is_bool)
        })
    }
}

/// The kind and values of an option.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OptionKind {
    /// A Boolean option.
    Bool { cur: bool, dflt: bool },
    /// A numeric option.
    Numeric {
        cur: u64,
        dflt: u64,
        min: u64,
        max: u64,
    },
    /// An option with modes.
    Mode {
        cur: String,
        dflt: String,
        modes: Vec<String>,
    },
    /// An option with a string value.
    String { cur: String, dflt: String },
}

/// The details of an option, see [`Options::info`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptionInfo {
    /// The option.
    pub opt: Opt,
    /// The short option name, if any.
    pub shrt: Option<String>,
    /// The long option name.
    pub lng: String,
    /// The option description.
    pub description: String,
    /// The kind and values of the option.
    pub kind: OptionKind,
}

impl OptionInfo {
    /// Copy out of the C struct (its strings live in thread-local buffers).
    unsafe fn from_raw(raw: &sys::BitwuzlaOptionInfo, is_bool: bool) -> Self {
        let kind = unsafe {
            if is_bool {
                OptionKind::Bool {
                    cur: raw.numeric.cur != 0,
                    dflt: raw.numeric.dflt != 0,
                }
            } else if raw.is_mode {
                OptionKind::Mode {
                    cur: to_string(raw.mode.cur),
                    dflt: to_string(raw.mode.dflt),
                    modes: slice(raw.mode.modes, raw.mode.num_modes)
                        .iter()
                        .map(|&m| to_string(m))
                        .collect(),
                }
            } else if raw.is_string {
                OptionKind::String {
                    cur: to_string(raw.string.cur),
                    dflt: to_string(raw.string.dflt),
                }
            } else {
                OptionKind::Numeric {
                    cur: raw.numeric.cur,
                    dflt: raw.numeric.dflt,
                    min: raw.numeric.min,
                    max: raw.numeric.max,
                }
            }
        };
        unsafe {
            Self {
                opt: from_c(raw.opt),
                shrt: to_opt_string(raw.shrt),
                lng: to_string(raw.lng),
                description: to_string(raw.description),
                kind,
            }
        }
    }
}

mod sealed {
    pub trait Sealed {}

    /// The kind of options a value type is for.
    pub enum ValueKind {
        Bool,
        Numeric,
        Str,
    }
}
use sealed::ValueKind;

/// A value that [`Options::set`] accepts: a `bool` for Boolean options, an
/// integer for numeric options, and a string for options with modes and
/// string options.
pub trait OptionValue: sealed::Sealed {
    #[doc(hidden)]
    const KIND: ValueKind;
    #[doc(hidden)]
    fn set(self, options: &mut Options, opt: Opt) -> Result<()>;
}

impl sealed::Sealed for bool {}
impl OptionValue for bool {
    const KIND: ValueKind = ValueKind::Bool;
    fn set(self, options: &mut Options, opt: Opt) -> Result<()> {
        options.set_numeric(opt, self as u64)
    }
}

macro_rules! impl_option_value_int {
    ($($ty:ty),*) => {$(
        impl sealed::Sealed for $ty {}
        impl OptionValue for $ty {
            const KIND: ValueKind = ValueKind::Numeric;
            fn set(self, options: &mut Options, opt: Opt) -> Result<()> {
                let value = u64::try_from(self).map_err(|_| {
                    Error::new(format!("invalid option value {self}, expected value >= 0"))
                })?;
                options.set_numeric(opt, value)
            }
        }
    )*};
}
impl_option_value_int!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

impl sealed::Sealed for &str {}
impl OptionValue for &str {
    const KIND: ValueKind = ValueKind::Str;
    fn set(self, options: &mut Options, opt: Opt) -> Result<()> {
        options.set_str(opt, self)
    }
}

impl sealed::Sealed for &String {}
impl OptionValue for &String {
    const KIND: ValueKind = ValueKind::Str;
    fn set(self, options: &mut Options, opt: Opt) -> Result<()> {
        options.set_str(opt, self)
    }
}

impl sealed::Sealed for String {}
impl OptionValue for String {
    const KIND: ValueKind = ValueKind::Str;
    fn set(self, options: &mut Options, opt: Opt) -> Result<()> {
        options.set_str(opt, &self)
    }
}
