use std::any::Any;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::ffi::c_void;
use std::panic::{self, AssertUnwindSafe};
use std::rc::Rc;

use libbitwuzla_sys as sys;

use crate::error::{Result, call, call_reentrant, run_terminator, try_call};
use crate::ffi::{capture_output, cstring, from_c, statistics, try_capture_output, try_cstring};
use crate::options::OptionsHandle;
use crate::parser::ParserHandle;
use crate::{Options, SatResult, Term, TermManager};

/// A terminator, queried periodically during solving to determine whether
/// solving should be terminated early.
///
/// Implemented for closures `FnMut() -> bool`.
///
/// A terminator runs in the middle of a solver call, so it must not use
/// Bitwuzla objects other than to clone or drop them (e.g., terms captured by
/// a closure): any other call into Bitwuzla panics.
///
/// A panic in [`terminate`](Terminator::terminate) terminates the current
/// solver call and is resumed when that call returns to Rust.
pub trait Terminator {
    /// Return `true` to terminate the current solver call.
    fn terminate(&mut self) -> bool;
}

impl<F: FnMut() -> bool> Terminator for F {
    fn terminate(&mut self) -> bool {
        self()
    }
}

/// The state passed to the C termination callback.
pub(crate) struct TerminatorState {
    terminator: Box<dyn Terminator>,
    panic: Option<Box<dyn Any + Send>>,
}

pub(crate) unsafe extern "C" fn terminator_trampoline(state: *mut c_void) -> i32 {
    // SAFETY: `state` is the `TerminatorState` registered with the callback.
    // It is freed when the callback is replaced or removed, or the solver (or
    // parser) is deleted, and accessed only by the solver call in progress,
    // which the terminator cannot reenter (see `run_terminator`).
    let state = unsafe { &mut *state.cast::<TerminatorState>() };
    if state.panic.is_some() {
        return 1;
    }
    // Never unwind through the solver: stash the panic and terminate.
    let query = AssertUnwindSafe(|| state.terminator.terminate());
    match run_terminator(|| panic::catch_unwind(query)) {
        Ok(terminate) => terminate as i32,
        Err(payload) => {
            state.panic = Some(payload);
            1
        }
    }
}

/// An owned, heap-allocated terminator state, registered with the C API by
/// address.
pub(crate) struct TerminatorSlot(*mut TerminatorState);

impl TerminatorSlot {
    pub(crate) fn new(terminator: impl Terminator + 'static) -> Self {
        Self(Box::into_raw(Box::new(TerminatorState {
            terminator: Box::new(terminator),
            panic: None,
        })))
    }

    pub(crate) fn as_ptr(&self) -> *mut c_void {
        self.0.cast()
    }

    /// Resume a panic raised by the terminator, if any.
    pub(crate) fn resume_panic(&self) {
        // SAFETY: no C call is in progress, so nothing else accesses the state.
        if let Some(payload) = unsafe { (*self.0).panic.take() } {
            panic::resume_unwind(payload);
        }
    }
}

impl Drop for TerminatorSlot {
    fn drop(&mut self) {
        drop(unsafe { Box::from_raw(self.0) });
    }
}

/// A Bitwuzla solver instance.
///
/// ```
/// use bitwuzla::{Bitwuzla, Kind, Opt, Options, SatResult, TermManager};
///
/// let tm = TermManager::new();
/// let mut options = Options::new();
/// options.set(Opt::ProduceModels, true)?;
/// let mut bitwuzla = Bitwuzla::new(&tm, &options)?;
///
/// let bv8 = tm.mk_bv_sort(8);
/// let x = tm.mk_const(&bv8, "x");
/// let two = tm.mk_bv_value_u64(&bv8, 2);
/// let x_times_two = tm.mk_term(Kind::BvMul, &[&x, &two], &[]);
/// bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&x_times_two, &two], &[]));
/// assert_eq!(bitwuzla.check_sat()?, SatResult::Sat);
///
/// let value = bitwuzla.get_value(&x);
/// assert!(value.is_bv_value());
/// # Ok::<(), bitwuzla::Error>(())
/// ```
pub struct Bitwuzla {
    raw: *mut sys::Bitwuzla,
    tm: TermManager,
    owner: Owner,
}

enum Owner {
    /// Created by [`Bitwuzla::new`] and deleted on drop. The C++ solver logs
    /// to the diagnostic output stream owned by the options it was created
    /// with.
    Solver {
        _options: Rc<OptionsHandle>,
        terminator: Option<TerminatorSlot>,
    },
    /// The instance of a [`Parser`](crate::Parser), which owns it and keeps
    /// its terminators.
    Parser(Rc<ParserHandle>),
}

impl Drop for Bitwuzla {
    fn drop(&mut self) {
        if let Owner::Solver { .. } = self.owner {
            call_reentrant(|| unsafe { sys::bitwuzla_delete(self.raw) });
        }
        // The options and terminator (or the parser) are dropped after the C
        // instance is gone.
    }
}

impl std::fmt::Debug for Bitwuzla {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bitwuzla({:p})", self.raw)
    }
}

impl Bitwuzla {
    /// Create a new Bitwuzla instance for the given term manager and options.
    ///
    /// The options are copied: later changes do not affect this instance,
    /// except for redirecting diagnostic output from one file to another (see
    /// [`Options::set_diagnostic_output_stream`]).
    pub fn new(tm: &TermManager, options: &Options) -> Result<Self> {
        let raw = try_call(|| unsafe { sys::bitwuzla_new(tm.as_raw(), options.as_raw()) })?;
        Ok(Self {
            raw,
            tm: tm.clone(),
            owner: Owner::Solver {
                _options: options.handle(),
                terminator: None,
            },
        })
    }

    /// Wrap the instance owned by a parser.
    pub(crate) fn borrowed(raw: *mut sys::Bitwuzla, parser: Rc<ParserHandle>) -> Self {
        Self {
            raw,
            tm: parser.tm().clone(),
            owner: Owner::Parser(parser),
        }
    }

    /// The raw C API handle (not owned).
    pub fn as_raw(&self) -> *mut sys::Bitwuzla {
        self.raw
    }

    /// The term manager of this instance.
    pub fn term_manager(&self) -> &TermManager {
        &self.tm
    }

    fn term(&self, raw: sys::BitwuzlaTerm) -> Term {
        Term::from_raw(raw, &self.tm.tm)
    }

    /// Wrap terms returned in a thread-local buffer.
    unsafe fn terms(&self, ptr: *const sys::BitwuzlaTerm, size: usize) -> Vec<Term> {
        unsafe { Term::vec_from_raw(ptr, size, &self.tm.tm) }
    }

    /// Run a call that may query the terminator, then resume a panic the
    /// terminator raised. `f` wraps returned handles, so that they are
    /// released if a panic is resumed.
    fn solve<T>(&mut self, f: impl FnOnce(*mut sys::Bitwuzla) -> T) -> Result<T> {
        let raw = self.raw;
        let res = try_call(|| f(raw));
        match &self.owner {
            Owner::Solver { terminator, .. } => {
                if let Some(slot) = terminator {
                    slot.resume_panic();
                }
            }
            // The terminator of the parser is attached to this instance too.
            Owner::Parser(parser) => parser.resume_terminator_panic(),
        }
        res
    }

    /// Keep the state of a terminator alive while it is registered.
    fn set_terminator(&mut self, slot: Option<TerminatorSlot>) {
        match &mut self.owner {
            Owner::Solver { terminator, .. } => *terminator = slot,
            Owner::Parser(parser) => parser.set_solver_terminator(slot),
        }
    }

    /// Configure a terminator, replacing the current one.
    ///
    /// ```
    /// # use bitwuzla::{Bitwuzla, Options, SatResult, TermManager};
    /// # let tm = TermManager::new();
    /// # let mut bitwuzla = Bitwuzla::new(&tm, &Options::new())?;
    /// let start = std::time::Instant::now();
    /// bitwuzla.configure_terminator(move || start.elapsed().as_secs() >= 10)?;
    /// # Ok::<(), bitwuzla::Error>(())
    /// ```
    ///
    /// Fails if the configured SAT solver does not support terminators, and
    /// keeps the current terminator then. For the instance of a
    /// [`Parser`](crate::Parser), this replaces the terminator of the parser
    /// on this instance, until the parser creates a new instance on `(reset)`
    /// or `(reset-assertions)`.
    pub fn configure_terminator(&mut self, terminator: impl Terminator + 'static) -> Result<()> {
        let slot = TerminatorSlot::new(terminator);
        try_call(|| unsafe {
            sys::bitwuzla_set_termination_callback(
                self.raw,
                Some(terminator_trampoline),
                slot.as_ptr(),
            )
        })?;
        // A failed configuration keeps the previous callback and its state.
        self.set_terminator(Some(slot));
        Ok(())
    }

    /// Remove the terminator configured via
    /// [`configure_terminator`](Self::configure_terminator), if any. The
    /// instance of a [`Parser`](crate::Parser) has a single terminator, the
    /// one configured last on the instance or the parser, so this may also
    /// remove the parser's.
    #[track_caller]
    pub fn clear_terminator(&mut self) {
        call(|| unsafe {
            sys::bitwuzla_set_termination_callback(self.raw, None, std::ptr::null_mut())
        });
        self.set_terminator(None);
    }

    /// Push context levels.
    #[track_caller]
    pub fn push(&mut self, nlevels: u32) {
        call(|| unsafe { sys::bitwuzla_push(self.raw, nlevels) })
    }

    /// Pop context levels.
    #[track_caller]
    pub fn pop(&mut self, nlevels: u32) {
        call(|| unsafe { sys::bitwuzla_pop(self.raw, nlevels) })
    }

    /// Assert a formula.
    #[track_caller]
    pub fn assert_formula(&mut self, term: &Term) {
        call(|| unsafe { sys::bitwuzla_assert(self.raw, term.raw) })
    }

    /// Get the current set of assertions.
    #[track_caller]
    pub fn get_assertions(&mut self) -> Vec<Term> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_get_assertions(self.raw, &mut size);
            self.terms(ptr, size)
        })
    }

    /// Determine if an assumption is an unsat assumption.
    ///
    /// Requires [`Opt::ProduceUnsatAssumptions`](crate::Opt::ProduceUnsatAssumptions)
    /// and that the last `check_sat_assuming` call returned unsat.
    #[track_caller]
    pub fn is_unsat_assumption(&mut self, term: &Term) -> bool {
        call(|| unsafe { sys::bitwuzla_is_unsat_assumption(self.raw, term.raw) })
    }

    /// Get the set of unsat assumptions of the last unsat query.
    #[track_caller]
    pub fn get_unsat_assumptions(&mut self) -> Vec<Term> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_get_unsat_assumptions(self.raw, &mut size);
            self.terms(ptr, size)
        })
    }

    /// Get the unsat core (unsat assertions) of the last unsat query.
    ///
    /// Requires [`Opt::ProduceUnsatCores`](crate::Opt::ProduceUnsatCores).
    #[track_caller]
    pub fn get_unsat_core(&mut self) -> Vec<Term> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_get_unsat_core(self.raw, &mut size);
            self.terms(ptr, size)
        })
    }

    /// Simplify the current input formula.
    pub fn simplify(&mut self) -> Result<()> {
        self.solve(|raw| unsafe { sys::bitwuzla_simplify(raw) })
    }

    /// Simplify the given term with respect to the current set of assertions.
    #[track_caller]
    pub fn simplify_term(&mut self, term: &Term) -> Result<Term> {
        self.tm.check_terms(&[term]);
        let tm = self.tm.tm.clone();
        self.solve(|raw| unsafe { Term::from_raw(sys::bitwuzla_simplify_term(raw, term.raw), &tm) })
    }

    /// Check satisfiability of the current input formula.
    pub fn check_sat(&mut self) -> Result<SatResult> {
        self.solve(|raw| unsafe { sys::bitwuzla_check_sat(raw) })
            .map(from_c)
    }

    /// Check satisfiability of the current input formula, under the given
    /// assumptions.
    #[track_caller]
    pub fn check_sat_assuming<T: Borrow<Term>>(&mut self, assumptions: &[T]) -> Result<SatResult> {
        self.tm.check_terms(assumptions);
        let mut args: Vec<sys::BitwuzlaTerm> = assumptions.iter().map(|t| t.borrow().raw).collect();
        self.solve(|raw| unsafe {
            sys::bitwuzla_check_sat_assuming(raw, args.len() as u32, args.as_mut_ptr())
        })
        .map(from_c)
    }

    /// Get a value of the given term in the current model.
    ///
    /// Requires [`Opt::ProduceModels`](crate::Opt::ProduceModels) and that the
    /// last query returned sat.
    #[track_caller]
    pub fn get_value(&mut self, term: &Term) -> Term {
        let raw = call(|| unsafe { sys::bitwuzla_get_value(self.raw, term.raw) });
        self.term(raw)
    }

    /// Get an interpolant `I` for the conjunction `A` of the given formulas
    /// and the conjunction `B` of the remaining assertions, i.e., `A -> I`
    /// and `I -> not B`.
    ///
    /// Requires [`Opt::ProduceInterpolants`](crate::Opt::ProduceInterpolants)
    /// and that the last query returned unsat.
    #[track_caller]
    pub fn get_interpolant<T: Borrow<Term>>(&mut self, a: &[T]) -> Result<Term> {
        self.tm.check_terms(a);
        let mut args: Vec<sys::BitwuzlaTerm> = a.iter().map(|t| t.borrow().raw).collect();
        let tm = self.tm.tm.clone();
        self.solve(|raw| unsafe {
            let raw = sys::bitwuzla_get_interpolant(raw, args.len() as u32, args.as_mut_ptr());
            Term::from_raw(raw, &tm)
        })
    }

    /// Get a sequence of interpolants, one for each partition `A` of the
    /// assertions given by increasing prefixes of `a`.
    #[track_caller]
    pub fn get_interpolants<P, T>(&mut self, a: &[P]) -> Result<Vec<Term>>
    where
        P: AsRef<[T]>,
        T: Borrow<Term>,
    {
        for part in a {
            self.tm.check_terms(part.as_ref());
        }
        let mut parts: Vec<Vec<sys::BitwuzlaTerm>> = a
            .iter()
            .map(|p| p.as_ref().iter().map(|t| t.borrow().raw).collect())
            .collect();
        let mut sizes: Vec<u32> = parts.iter().map(|p| p.len() as u32).collect();
        let mut ptrs: Vec<*mut sys::BitwuzlaTerm> =
            parts.iter_mut().map(|p| p.as_mut_ptr()).collect();
        let tm = self.tm.tm.clone();
        self.solve(|raw| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_get_interpolants(
                raw,
                ptrs.len() as u32,
                sizes.as_mut_ptr(),
                ptrs.as_mut_ptr(),
                &mut size,
            );
            Term::vec_from_raw(ptr, size, &tm)
        })
    }

    /// Print the current input formula in the given format (`"smt2"` or
    /// `"btor2"`), with bit-vector values in `base` 2, 10, or 16.
    ///
    /// Fails if the formula cannot be expressed in the format (e.g.,
    /// floating-point formulas in BTOR2), and for invalid arguments.
    pub fn print_formula(&self, format: &str, base: u8) -> Result<String> {
        let format = try_cstring(format)?;
        try_capture_output(|file| unsafe {
            sys::bitwuzla_print_formula(self.raw, format.as_ptr(), file, base)
        })
    }

    /// Print the unsat core of the last unsat query in the given format
    /// (`"smt2"`), with bit-vector values in `base` 2, 10, or 16.
    #[track_caller]
    pub fn print_unsat_core(&self, format: &str, base: u8) -> String {
        let format = cstring(format);
        capture_output(|file| unsafe {
            sys::bitwuzla_print_unsat_core(self.raw, format.as_ptr(), file, base)
        })
    }

    /// Get the current statistics as a map from statistic names to values.
    #[track_caller]
    pub fn statistics(&self) -> BTreeMap<String, String> {
        call(|| unsafe {
            let mut keys = std::ptr::null_mut();
            let mut values = std::ptr::null_mut();
            let mut size = 0;
            sys::bitwuzla_get_statistics(self.raw, &mut keys, &mut values, &mut size);
            statistics(keys, values, size)
        })
    }
}
