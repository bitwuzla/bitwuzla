use std::borrow::Borrow;
use std::rc::Rc;

use libbitwuzla_sys as sys;

use crate::error::{Result, call, call_reentrant, try_call};
use crate::ffi::{opt_cstring, opt_ptr, try_cstring};
use crate::{Kind, RoundingMode, Sort, Term};

/// Owning handle of a C term manager; deleted when the last reference (held
/// by `TermManager`, `Sort`, `Term`, `Bitwuzla`, and `Parser` values) is
/// dropped.
pub(crate) struct TmHandle(pub(crate) *mut sys::BitwuzlaTermManager);

impl Drop for TmHandle {
    fn drop(&mut self) {
        call_reentrant(|| unsafe { sys::bitwuzla_term_manager_delete(self.0) });
    }
}

/// The term manager creates and owns all sorts and terms.
///
/// `TermManager` is a reference-counted handle: cloning it yields another
/// handle to the same term manager, and every [`Sort`] and [`Term`] keeps the
/// term manager alive. Sorts and terms of different term managers must not be
/// mixed (this panics).
///
/// ```
/// use bitwuzla::{Kind, TermManager};
///
/// let tm = TermManager::new();
/// let bv8 = tm.mk_bv_sort(8);
/// let x = tm.mk_const(&bv8, "x");
/// let one = tm.mk_bv_one(&bv8);
/// let sum = tm.mk_term(Kind::BvAdd, &[&x, &one], &[]);
/// assert_eq!(sum.to_string(), "(bvadd x #b00000001)");
/// # Ok::<(), bitwuzla::Error>(())
/// ```
#[derive(Clone)]
pub struct TermManager {
    pub(crate) tm: Rc<TmHandle>,
}

impl Default for TermManager {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for TermManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TermManager({:p})", self.tm.0)
    }
}

/// Raw handles of a slice of terms (borrowed, not copied).
fn raw_terms<T: Borrow<Term>>(terms: &[T]) -> Vec<sys::BitwuzlaTerm> {
    terms.iter().map(|t| t.borrow().raw).collect()
}

impl TermManager {
    /// Create a new term manager.
    pub fn new() -> Self {
        Self {
            tm: Rc::new(TmHandle(call(|| unsafe {
                sys::bitwuzla_term_manager_new()
            }))),
        }
    }

    /// The raw C API handle (not owned).
    pub fn as_raw(&self) -> *mut sys::BitwuzlaTermManager {
        self.tm.0
    }

    #[track_caller]
    fn sort(&self, f: impl FnOnce(*mut sys::BitwuzlaTermManager) -> sys::BitwuzlaSort) -> Sort {
        let tm = self.tm.0;
        Sort::from_raw(call(|| f(tm)), &self.tm)
    }

    #[track_caller]
    fn term(&self, f: impl FnOnce(*mut sys::BitwuzlaTermManager) -> sys::BitwuzlaTerm) -> Term {
        let tm = self.tm.0;
        Term::from_raw(call(|| f(tm)), &self.tm)
    }

    /// Panic if a term belongs to another term manager.
    ///
    /// Calls that return `Result` check this before calling Bitwuzla, which
    /// would report it as an error.
    #[track_caller]
    pub(crate) fn check_terms<T: Borrow<Term>>(&self, terms: &[T]) {
        if let Some(i) = terms
            .iter()
            .position(|t| !Rc::ptr_eq(&t.borrow().tm, &self.tm))
        {
            panic!("mismatching term manager for term at index {i}");
        }
    }

    /// Panic if a sort belongs to another term manager or is not of the
    /// expected kind (see [`check_terms`](Self::check_terms)).
    #[track_caller]
    fn check_sort(&self, sort: &Sort, is_kind: fn(&Sort) -> bool, expected: &str) {
        assert!(
            Rc::ptr_eq(&sort.tm, &self.tm),
            "mismatching term manager for sort"
        );
        assert!(is_kind(sort), "expected {expected} sort");
    }

    /// Panic if `rm` is not a rounding mode term of this term manager.
    #[track_caller]
    fn check_rm(&self, rm: &Term) {
        self.check_terms(&[rm]);
        assert!(rm.sort().is_rm(), "expected rounding mode term");
    }

    /// Like [`term`](Self::term), for terms created from input strings.
    fn try_term(
        &self,
        f: impl FnOnce(*mut sys::BitwuzlaTermManager) -> sys::BitwuzlaTerm,
    ) -> Result<Term> {
        let tm = self.tm.0;
        try_call(|| f(tm)).map(|raw| Term::from_raw(raw, &self.tm))
    }

    // ── Sorts ───────────────────────────────────────────────────────

    /// Create an array sort with the given index and element sorts.
    #[track_caller]
    pub fn mk_array_sort(&self, index: &Sort, element: &Sort) -> Sort {
        self.sort(|tm| unsafe { sys::bitwuzla_mk_array_sort(tm, index.raw, element.raw) })
    }

    /// Create a Boolean sort.
    pub fn mk_bool_sort(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_mk_bool_sort(self.tm.0) }),
            &self.tm,
        )
    }

    /// Create a bit-vector sort of the given size (`> 0`).
    #[track_caller]
    pub fn mk_bv_sort(&self, size: u64) -> Sort {
        self.sort(|tm| unsafe { sys::bitwuzla_mk_bv_sort(tm, size) })
    }

    /// Create a floating-point sort of the given exponent and significand
    /// size (including the hidden bit).
    #[track_caller]
    pub fn mk_fp_sort(&self, exp_size: u64, sig_size: u64) -> Sort {
        self.sort(|tm| unsafe { sys::bitwuzla_mk_fp_sort(tm, exp_size, sig_size) })
    }

    /// Create a function sort with the given domain and codomain sorts.
    #[track_caller]
    pub fn mk_fun_sort<S: Borrow<Sort>>(&self, domain: &[S], codomain: &Sort) -> Sort {
        let mut raw: Vec<sys::BitwuzlaSort> = domain.iter().map(|s| s.borrow().raw).collect();
        self.sort(|tm| unsafe {
            sys::bitwuzla_mk_fun_sort(tm, raw.len() as u64, raw.as_mut_ptr(), codomain.raw)
        })
    }

    /// Create a rounding mode sort.
    pub fn mk_rm_sort(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_mk_rm_sort(self.tm.0) }),
            &self.tm,
        )
    }

    /// Create an uninterpreted sort with an optional symbol.
    ///
    /// ```
    /// # let tm = bitwuzla::TermManager::new();
    /// let u = tm.mk_uninterpreted_sort("U");
    /// let anonymous = tm.mk_uninterpreted_sort(None);
    /// assert_ne!(u, anonymous);
    /// # Ok::<(), bitwuzla::Error>(())
    /// ```
    #[track_caller]
    pub fn mk_uninterpreted_sort<'a>(&self, symbol: impl Into<Option<&'a str>>) -> Sort {
        let symbol = opt_cstring(symbol.into());
        self.sort(|tm| unsafe { sys::bitwuzla_mk_uninterpreted_sort(tm, opt_ptr(&symbol)) })
    }

    // ── Values ──────────────────────────────────────────────────────

    /// Create a true value.
    pub fn mk_true(&self) -> Term {
        Term::from_raw(
            call(|| unsafe { sys::bitwuzla_mk_true(self.tm.0) }),
            &self.tm,
        )
    }

    /// Create a false value.
    pub fn mk_false(&self) -> Term {
        Term::from_raw(
            call(|| unsafe { sys::bitwuzla_mk_false(self.tm.0) }),
            &self.tm,
        )
    }

    /// Create a bit-vector value zero.
    #[track_caller]
    pub fn mk_bv_zero(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_zero(tm, sort.raw) })
    }

    /// Create a bit-vector value one.
    #[track_caller]
    pub fn mk_bv_one(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_one(tm, sort.raw) })
    }

    /// Create a bit-vector value where all bits are set to 1.
    #[track_caller]
    pub fn mk_bv_ones(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_ones(tm, sort.raw) })
    }

    /// Create a bit-vector minimum signed value.
    #[track_caller]
    pub fn mk_bv_min_signed(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_min_signed(tm, sort.raw) })
    }

    /// Create a bit-vector maximum signed value.
    #[track_caller]
    pub fn mk_bv_max_signed(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_max_signed(tm, sort.raw) })
    }

    /// Create a bit-vector value from its string representation in `base`
    /// 2, 10, or 16 (decimal values may be negative).
    #[track_caller]
    pub fn mk_bv_value(&self, sort: &Sort, value: &str, base: u8) -> Result<Term> {
        self.check_sort(sort, Sort::is_bv, "bit-vector");
        assert!(
            matches!(base, 2 | 10 | 16),
            "invalid base {base}, expected 2, 10, or 16"
        );
        let value = try_cstring(value)?;
        self.try_term(|tm| unsafe { sys::bitwuzla_mk_bv_value(tm, sort.raw, value.as_ptr(), base) })
    }

    /// Create a bit-vector value from an unsigned integer.
    #[track_caller]
    pub fn mk_bv_value_u64(&self, sort: &Sort, value: u64) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_value_uint64(tm, sort.raw, value) })
    }

    /// Create a bit-vector value from a signed integer.
    #[track_caller]
    pub fn mk_bv_value_i64(&self, sort: &Sort, value: i64) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_bv_value_int64(tm, sort.raw, value) })
    }

    /// Create a floating-point positive zero value (SMT-LIB: `+zero`).
    #[track_caller]
    pub fn mk_fp_pos_zero(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_fp_pos_zero(tm, sort.raw) })
    }

    /// Create a floating-point negative zero value (SMT-LIB: `-zero`).
    #[track_caller]
    pub fn mk_fp_neg_zero(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_fp_neg_zero(tm, sort.raw) })
    }

    /// Create a floating-point positive infinity value (SMT-LIB: `+oo`).
    #[track_caller]
    pub fn mk_fp_pos_inf(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_fp_pos_inf(tm, sort.raw) })
    }

    /// Create a floating-point negative infinity value (SMT-LIB: `-oo`).
    #[track_caller]
    pub fn mk_fp_neg_inf(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_fp_neg_inf(tm, sort.raw) })
    }

    /// Create a floating-point NaN value.
    #[track_caller]
    pub fn mk_fp_nan(&self, sort: &Sort) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_fp_nan(tm, sort.raw) })
    }

    /// Create a floating-point value from its IEEE-754 bit-vector components
    /// (sign, exponent, significand without the hidden bit).
    #[track_caller]
    pub fn mk_fp_value(&self, sign: &Term, exponent: &Term, significand: &Term) -> Term {
        self.term(|tm| unsafe {
            sys::bitwuzla_mk_fp_value(tm, sign.raw, exponent.raw, significand.raw)
        })
    }

    /// Create a floating-point value from a real, given as a decimal string,
    /// rounded with rounding mode `rm`.
    #[track_caller]
    pub fn mk_fp_from_real(&self, sort: &Sort, rm: &Term, real: &str) -> Result<Term> {
        self.check_sort(sort, Sort::is_fp, "floating-point");
        self.check_rm(rm);
        let real = try_cstring(real)?;
        self.try_term(|tm| unsafe {
            sys::bitwuzla_mk_fp_from_real(tm, sort.raw, rm.raw, real.as_ptr())
        })
    }

    /// Create a floating-point value from a rational `num / den`, given as
    /// decimal strings, rounded with rounding mode `rm`.
    #[track_caller]
    pub fn mk_fp_from_rational(
        &self,
        sort: &Sort,
        rm: &Term,
        num: &str,
        den: &str,
    ) -> Result<Term> {
        self.check_sort(sort, Sort::is_fp, "floating-point");
        self.check_rm(rm);
        let num = try_cstring(num)?;
        let den = try_cstring(den)?;
        self.try_term(|tm| unsafe {
            sys::bitwuzla_mk_fp_from_rational(tm, sort.raw, rm.raw, num.as_ptr(), den.as_ptr())
        })
    }

    /// Create a rounding mode value.
    pub fn mk_rm_value(&self, rm: RoundingMode) -> Term {
        Term::from_raw(
            call(|| unsafe { sys::bitwuzla_mk_rm_value(self.tm.0, rm.into()) }),
            &self.tm,
        )
    }

    // ── Terms ───────────────────────────────────────────────────────

    /// Create a term of the given kind with the given arguments and indices.
    ///
    /// Arguments may be given as `&[Term]` or `&[&Term]`.
    ///
    /// ```
    /// use bitwuzla::{Kind, TermManager};
    ///
    /// let tm = TermManager::new();
    /// let bv8 = tm.mk_bv_sort(8);
    /// let x = tm.mk_const(&bv8, "x");
    /// let lo = tm.mk_term(Kind::BvExtract, &[&x], &[3, 0]);
    /// assert_eq!(lo.sort().bv_size(), 4);
    /// # Ok::<(), bitwuzla::Error>(())
    /// ```
    #[track_caller]
    pub fn mk_term<T: Borrow<Term>>(&self, kind: Kind, args: &[T], indices: &[u64]) -> Term {
        let mut args = raw_terms(args);
        self.term(|tm| unsafe {
            sys::bitwuzla_mk_term_indexed(
                tm,
                kind.into(),
                args.len() as u32,
                args.as_mut_ptr(),
                indices.len() as u32,
                indices.as_ptr(),
            )
        })
    }

    /// Create a (first-order) constant of the given sort with an optional
    /// symbol.
    #[track_caller]
    pub fn mk_const<'a>(&self, sort: &Sort, symbol: impl Into<Option<&'a str>>) -> Term {
        let symbol = opt_cstring(symbol.into());
        self.term(|tm| unsafe { sys::bitwuzla_mk_const(tm, sort.raw, opt_ptr(&symbol)) })
    }

    /// Create a one-dimensional constant array of the given array sort, where
    /// all elements are `value`.
    #[track_caller]
    pub fn mk_const_array(&self, sort: &Sort, value: &Term) -> Term {
        self.term(|tm| unsafe { sys::bitwuzla_mk_const_array(tm, sort.raw, value.raw) })
    }

    /// Create a variable (to be bound by a quantifier or lambda) of the given
    /// sort with an optional symbol.
    #[track_caller]
    pub fn mk_var<'a>(&self, sort: &Sort, symbol: impl Into<Option<&'a str>>) -> Term {
        let symbol = opt_cstring(symbol.into());
        self.term(|tm| unsafe { sys::bitwuzla_mk_var(tm, sort.raw, opt_ptr(&symbol)) })
    }

    // ── Substitution ────────────────────────────────────────────────

    /// Substitute a set of keys with their corresponding values in `term`.
    ///
    /// `map` may be any iterator of `(key, value)` pairs, e.g., a
    /// `&HashMap<Term, Term>` or `[(&key, &value)]`. Substitutions are
    /// simultaneous, i.e., not applied to the substituted values. An empty
    /// map yields `term`.
    #[track_caller]
    pub fn substitute_term<'a>(
        &self,
        term: &Term,
        map: impl IntoIterator<Item = (&'a Term, &'a Term)>,
    ) -> Term {
        let mut terms = [term.clone()];
        self.substitute_terms(&mut terms, map);
        let [res] = terms;
        res
    }

    /// Substitute a set of keys with their corresponding values in each of
    /// the given terms, in place.
    ///
    /// See [`substitute_term`](Self::substitute_term). An empty map or an
    /// empty set of terms is a no-op.
    #[track_caller]
    pub fn substitute_terms<'a>(
        &self,
        terms: &mut [Term],
        map: impl IntoIterator<Item = (&'a Term, &'a Term)>,
    ) {
        let (mut keys, mut values): (Vec<_>, Vec<_>) =
            map.into_iter().map(|(k, v)| (k.raw, v.raw)).unzip();
        // As in the C++ API (the C API rejects empty arrays).
        if terms.is_empty() || keys.is_empty() {
            return;
        }
        // The C API checks the keys and values against the term manager of
        // the terms, but has no term manager argument to check the terms
        // against.
        self.check_terms(terms);
        let mut raw = raw_terms(terms);
        call(|| unsafe {
            sys::bitwuzla_substitute_terms(
                raw.len(),
                raw.as_mut_ptr(),
                keys.len(),
                keys.as_mut_ptr(),
                values.as_mut_ptr(),
            )
        });
        // The C API overwrote each entry with a new reference to the result.
        for (term, raw) in terms.iter_mut().zip(raw) {
            *term = Term::from_raw(raw, &self.tm);
        }
    }
}
