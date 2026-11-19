use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ffi::CStr;
use std::os::raw::c_char;
use std::path::Path;
use std::rc::Rc;

use libbitwuzla_sys as sys;

use crate::error::{Error, Result, call, call_reentrant, try_call};
use crate::ffi::{statistics, to_string, try_cstring, try_path_cstring};
use crate::options::OptionsHandle;
use crate::solver::{Terminator, TerminatorSlot, terminator_trampoline};
use crate::{Bitwuzla, Options, Sort, Term, TermManager};

/// A parser for SMT-LIB v2 and BTOR2 input.
///
/// The parser creates and owns its [`Bitwuzla`] instance, available via
/// [`Parser::bitwuzla`] once the input initialized it (e.g., after a
/// `set-logic` command).
///
/// ```
/// use bitwuzla::{Options, Parser, SatResult, TermManager};
///
/// let tm = TermManager::new();
/// let options = Options::new();
/// let mut parser = Parser::new(&tm, &options, "smt2", 2, "<stdout>")?;
/// parser.parse_str("(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b0001))")?;
/// let bitwuzla = parser.bitwuzla().expect("set-logic initializes the solver");
/// assert_eq!(bitwuzla.check_sat()?, SatResult::Sat);
/// # Ok::<(), bitwuzla::Error>(())
/// ```
pub struct Parser {
    handle: Rc<ParserHandle>,
    /// Wrapper of the parser-owned solver, created on first access.
    bitwuzla: Option<Bitwuzla>,
    /// Passed to each parse call, the C API has no setting for it.
    parse_only: bool,
}

/// Owning handle of a C parser, shared with the wrapper of its solver: the
/// wrapper may be moved out of the [`Parser`] and outlive it.
pub(crate) struct ParserHandle {
    raw: *mut sys::BitwuzlaParser,
    tm: TermManager,
    /// The parser and its solver log to the diagnostic output stream owned by
    /// the options the parser was created with, and the parser copies the
    /// options again on `(reset)`.
    _options: Rc<OptionsHandle>,
    /// The terminators configured on the parser and on its solver. Both are
    /// attached to the same solver, so either may be queried during any
    /// parser or solver call.
    terminators: RefCell<Terminators>,
}

#[derive(Default)]
struct Terminators {
    parser: Option<TerminatorSlot>,
    solver: Option<TerminatorSlot>,
}

impl ParserHandle {
    pub(crate) fn tm(&self) -> &TermManager {
        &self.tm
    }

    pub(crate) fn set_solver_terminator(&self, slot: Option<TerminatorSlot>) {
        self.terminators.borrow_mut().solver = slot;
    }

    /// Resume a panic raised by either terminator, if any.
    pub(crate) fn resume_terminator_panic(&self) {
        let terminators = self.terminators.borrow();
        for slot in [&terminators.parser, &terminators.solver]
            .into_iter()
            .flatten()
        {
            slot.resume_panic();
        }
    }
}

impl Drop for ParserHandle {
    fn drop(&mut self) {
        call_reentrant(|| unsafe { sys::bitwuzla_parser_delete(self.raw) });
        // The term manager, options, and terminators are dropped after the C
        // parser (and its solver) are gone.
    }
}

impl std::fmt::Debug for Parser {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parser({:p})", self.handle.raw)
    }
}

/// Convert the `error_msg` out-parameter of the C parser API.
unsafe fn parse_error(msg: *const c_char) -> Result<()> {
    if msg.is_null() {
        Ok(())
    } else {
        let msg = unsafe { to_string(msg) };
        let msg = msg.trim();
        Err(Error::new(msg.strip_prefix("bitwuzla: ").unwrap_or(msg)))
    }
}

impl Parser {
    /// Create a new parser.
    ///
    /// * `language`: the input format, `"smt2"` or `"btor2"`.
    /// * `base`: the base of bit-vector values in output (2, 10, or 16).
    /// * `outfile`: the output file, `"<stdout>"` for stdout.
    ///
    /// The options are copied, and copied again on `(reset)`: changes made in
    /// the meantime take effect then.
    pub fn new(
        tm: &TermManager,
        options: &Options,
        language: &str,
        base: u8,
        outfile: &str,
    ) -> Result<Self> {
        let language = try_cstring(language)?;
        let outfile = try_cstring(outfile)?;
        let raw = try_call(|| unsafe {
            sys::bitwuzla_parser_new(
                tm.as_raw(),
                options.as_raw(),
                language.as_ptr(),
                base,
                outfile.as_ptr(),
            )
        })?;
        Ok(Self {
            handle: Rc::new(ParserHandle {
                raw,
                tm: tm.clone(),
                _options: options.handle(),
                terminators: RefCell::default(),
            }),
            bitwuzla: None,
            parse_only: false,
        })
    }

    /// The raw C API handle (not owned).
    pub fn as_raw(&self) -> *mut sys::BitwuzlaParser {
        self.handle.raw
    }

    /// Configure a terminator, replacing the current one.
    ///
    /// Fails if the configured SAT solver does not support terminators, see
    /// [`Bitwuzla::configure_terminator`], and keeps the current terminator
    /// then.
    pub fn configure_terminator(&mut self, terminator: impl Terminator + 'static) -> Result<()> {
        let slot = TerminatorSlot::new(terminator);
        try_call(|| unsafe {
            sys::bitwuzla_parser_set_termination_callback(
                self.handle.raw,
                Some(terminator_trampoline),
                slot.as_ptr(),
            )
        })?;
        // A failed configuration keeps the previous callback and its state.
        self.handle.terminators.borrow_mut().parser = Some(slot);
        Ok(())
    }

    /// Remove the terminator configured via
    /// [`configure_terminator`](Self::configure_terminator), if any. The
    /// solver of the parser has a single terminator, the one configured last
    /// on the parser or the solver, so this may also remove the solver's.
    #[track_caller]
    pub fn clear_terminator(&mut self) {
        // As for the solver, do not touch a terminator configured elsewhere.
        if self.handle.terminators.borrow().parser.is_none() {
            return;
        }
        call(|| unsafe {
            sys::bitwuzla_parser_set_termination_callback(
                self.handle.raw,
                None,
                std::ptr::null_mut(),
            )
        });
        self.handle.terminators.borrow_mut().parser = None;
    }

    /// Enable or disable printing the model after each satisfiable query.
    ///
    /// Must be enabled to print models for BTOR2 input, which has no
    /// command to print the model.
    #[track_caller]
    pub fn configure_auto_print_model(&mut self, value: bool) {
        call(|| unsafe { sys::bitwuzla_parser_configure_auto_print_model(self.handle.raw, value) })
    }

    /// Run a call that may query the terminators, then resume a panic they
    /// raised. `f` wraps returned handles, so that they are released if a
    /// panic is resumed.
    fn run<T>(&mut self, f: impl FnOnce(*mut sys::BitwuzlaParser) -> T) -> Result<T> {
        let raw = self.handle.raw;
        let res = try_call(|| f(raw));
        self.handle.resume_terminator_panic();
        res
    }

    /// Enable or disable parse-only mode for subsequent calls to
    /// [`parse_str`](Self::parse_str) and [`parse_file`](Self::parse_file).
    ///
    /// In parse-only mode, the solver is not called for `check-sat`,
    /// `check-sat-assuming`, `get-interpolant` and `get-interpolants`
    /// commands, nor for the check after parsing BTOR2 input. All other
    /// commands are executed. Disabled by default.
    pub fn configure_parse_only(&mut self, value: bool) {
        self.parse_only = value;
    }

    /// Parse input from a string.
    pub fn parse_str(&mut self, input: &str) -> Result<()> {
        let input = try_cstring(input)?;
        self.parse(&input, false)
    }

    /// Parse input from a file.
    pub fn parse_file(&mut self, path: impl AsRef<Path>) -> Result<()> {
        let path = try_path_cstring(path.as_ref())?;
        self.parse(&path, true)
    }

    fn parse(&mut self, input: &CStr, parse_file: bool) -> Result<()> {
        let parse_only = self.parse_only;
        let mut msg = std::ptr::null();
        self.run(|raw| unsafe {
            sys::bitwuzla_parser_parse(raw, input.as_ptr(), parse_only, parse_file, &mut msg)
        })?;
        unsafe { parse_error(msg) }
    }

    /// Parse a term from a string.
    pub fn parse_term(&mut self, input: &str) -> Result<Term> {
        let input = try_cstring(input)?;
        let mut msg = std::ptr::null();
        let tm = self.handle.tm.tm.clone();
        let term = self.run(|raw| unsafe {
            let term = sys::bitwuzla_parser_parse_term(raw, input.as_ptr(), &mut msg);
            (!term.is_null()).then(|| Term::from_raw(term, &tm))
        })?;
        unsafe { parse_error(msg) }?;
        Ok(term.expect("Bitwuzla returned a null term without an error"))
    }

    /// Parse a sort from a string.
    pub fn parse_sort(&mut self, input: &str) -> Result<Sort> {
        let input = try_cstring(input)?;
        let mut msg = std::ptr::null();
        let tm = self.handle.tm.tm.clone();
        let sort = self.run(|raw| unsafe {
            let sort = sys::bitwuzla_parser_parse_sort(raw, input.as_ptr(), &mut msg);
            (!sort.is_null()).then(|| Sort::from_raw(sort, &tm))
        })?;
        unsafe { parse_error(msg) }?;
        Ok(sort.expect("Bitwuzla returned a null sort without an error"))
    }

    /// Get the sorts declared via `declare-sort` (empty for BTOR2 input).
    #[track_caller]
    pub fn get_declared_sorts(&mut self) -> Vec<Sort> {
        let tm = self.handle.tm.tm.clone();
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_parser_get_declared_sorts(self.handle.raw, &mut size);
            Sort::vec_from_raw(ptr, size, &tm)
        })
    }

    /// Get the function symbols declared via `declare-const` and
    /// `declare-fun`.
    #[track_caller]
    pub fn get_declared_funs(&mut self) -> Vec<Term> {
        let tm = self.handle.tm.tm.clone();
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_parser_get_declared_funs(self.handle.raw, &mut size);
            Term::vec_from_raw(ptr, size, &tm)
        })
    }

    /// Get the message of the last parse error (empty if none).
    pub fn error_msg(&self) -> String {
        call(|| unsafe { to_string(sys::bitwuzla_parser_get_error_msg(self.handle.raw)) })
    }

    /// Get the Bitwuzla instance of this parser, `None` if the input did not
    /// initialize it yet.
    ///
    /// The instance keeps the parser alive, so it remains valid even if it
    /// is moved out (e.g., with [`std::mem::replace`]).
    pub fn bitwuzla(&mut self) -> Option<&mut Bitwuzla> {
        // The only error is a missing instance.
        let raw =
            try_call(|| unsafe { sys::bitwuzla_parser_get_bitwuzla(self.handle.raw) }).ok()?;
        if self.bitwuzla.as_ref().is_none_or(|b| b.as_raw() != raw) {
            self.bitwuzla = Some(Bitwuzla::borrowed(raw, Rc::clone(&self.handle)));
        }
        self.bitwuzla.as_mut()
    }

    /// Get the current parser statistics.
    #[track_caller]
    pub fn statistics(&self) -> BTreeMap<String, String> {
        call(|| unsafe {
            let mut keys = std::ptr::null_mut();
            let mut values = std::ptr::null_mut();
            let mut size = 0;
            sys::bitwuzla_parser_get_statistics(self.handle.raw, &mut keys, &mut values, &mut size);
            statistics(keys, values, size)
        })
    }
}
