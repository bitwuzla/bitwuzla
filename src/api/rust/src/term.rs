use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use libbitwuzla_sys as sys;

use crate::error::{call, call_reentrant};
use crate::ffi::{from_c, slice, to_opt_string, to_string};
use crate::term_manager::TmHandle;
use crate::{Kind, RoundingMode, Sort};

/// A Bitwuzla term.
///
/// Terms are created via [`TermManager`](crate::TermManager). A `Term` keeps
/// its term manager alive, so it may outlive the `TermManager` value that
/// created it. Two terms are equal if they denote the same term of the same
/// term manager.
pub struct Term {
    pub(crate) raw: sys::BitwuzlaTerm,
    pub(crate) tm: Rc<TmHandle>,
}

impl Term {
    /// Take ownership of a term returned by the C API.
    pub(crate) fn from_raw(raw: sys::BitwuzlaTerm, tm: &Rc<TmHandle>) -> Self {
        assert!(!raw.is_null(), "Bitwuzla returned a null term");
        Self {
            raw,
            tm: Rc::clone(tm),
        }
    }

    /// Take ownership of an array of terms returned by the C API.
    ///
    /// # Safety
    ///
    /// `ptr` must point to `size` terms (or be `NULL`).
    pub(crate) unsafe fn vec_from_raw(
        ptr: *const sys::BitwuzlaTerm,
        size: usize,
        tm: &Rc<TmHandle>,
    ) -> Vec<Term> {
        unsafe { slice(ptr, size) }
            .iter()
            .map(|&raw| Term::from_raw(raw, tm))
            .collect()
    }

    /// Get the kind of this term.
    pub fn kind(&self) -> Kind {
        from_c(call(|| unsafe { sys::bitwuzla_term_get_kind(self.raw) }))
    }

    /// Get the sort of this term.
    pub fn sort(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_term_get_sort(self.raw) }),
            &self.tm,
        )
    }

    /// Get the number of child terms of this term.
    pub fn num_children(&self) -> usize {
        self.children().len()
    }

    /// Get the child terms of this term.
    pub fn children(&self) -> Vec<Term> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_term_get_children(self.raw, &mut size);
            Term::vec_from_raw(ptr, size, &self.tm)
        })
    }

    /// Get the number of indices of this term.
    pub fn num_indices(&self) -> usize {
        self.indices().len()
    }

    /// Get the indices of an indexed term (empty if the term is not indexed).
    pub fn indices(&self) -> Vec<u64> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_term_get_indices(self.raw, &mut size);
            slice(ptr, size).to_vec()
        })
    }

    /// Determine if this term is an indexed term.
    pub fn is_indexed(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_indexed(self.raw) })
    }

    /// Get the symbol of this term, `None` if it has none.
    pub fn symbol(&self) -> Option<String> {
        call(|| unsafe { to_opt_string(sys::bitwuzla_term_get_symbol(self.raw)) })
    }

    /// Determine if this term is of the same sort as `other`.
    pub fn is_equal_sort(&self, other: &Term) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_equal_sort(self.raw, other.raw) })
    }

    // ── Sort shortcuts ──────────────────────────────────────────────

    /// Get the index sort of an array term.
    #[track_caller]
    pub fn array_index_sort(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_term_array_get_index_sort(self.raw) }),
            &self.tm,
        )
    }

    /// Get the element sort of an array term.
    #[track_caller]
    pub fn array_element_sort(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_term_array_get_element_sort(self.raw) }),
            &self.tm,
        )
    }

    /// Get the domain sorts of a function term.
    #[track_caller]
    pub fn fun_domain_sorts(&self) -> Vec<Sort> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_term_fun_get_domain_sorts(self.raw, &mut size);
            Sort::vec_from_raw(ptr, size, &self.tm)
        })
    }

    /// Get the codomain sort of a function term.
    #[track_caller]
    pub fn fun_codomain_sort(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_term_fun_get_codomain_sort(self.raw) }),
            &self.tm,
        )
    }

    /// Get the bit-width of a bit-vector term.
    #[track_caller]
    pub fn bv_size(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_term_bv_get_size(self.raw) })
    }

    /// Get the exponent size of a floating-point term.
    #[track_caller]
    pub fn fp_exp_size(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_term_fp_get_exp_size(self.raw) })
    }

    /// Get the significand size of a floating-point term.
    #[track_caller]
    pub fn fp_sig_size(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_term_fp_get_sig_size(self.raw) })
    }

    /// Get the arity of a function term.
    #[track_caller]
    pub fn fun_arity(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_term_fun_get_arity(self.raw) })
    }

    // ── Predicates ──────────────────────────────────────────────────

    /// Determine if this term is an array term.
    pub fn is_array(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_array(self.raw) })
    }

    /// Determine if this term is a constant.
    pub fn is_const(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_const(self.raw) })
    }

    /// Determine if this term is a function.
    pub fn is_fun(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fun(self.raw) })
    }

    /// Determine if this term is a variable.
    pub fn is_variable(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_var(self.raw) })
    }

    /// Determine if this term is a value.
    pub fn is_value(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_value(self.raw) })
    }

    /// Determine if this term is a bit-vector value.
    pub fn is_bv_value(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv_value(self.raw) })
    }

    /// Determine if this term is a floating-point value.
    pub fn is_fp_value(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp_value(self.raw) })
    }

    /// Determine if this term is a rounding mode value.
    pub fn is_rm_value(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm_value(self.raw) })
    }

    /// Determine if this term is a Boolean term.
    pub fn is_bool(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bool(self.raw) })
    }

    /// Determine if this term is a bit-vector term.
    pub fn is_bv(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv(self.raw) })
    }

    /// Determine if this term is a floating-point term.
    pub fn is_fp(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp(self.raw) })
    }

    /// Determine if this term is a rounding mode term.
    pub fn is_rm(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm(self.raw) })
    }

    /// Determine if this term is a term of uninterpreted sort.
    pub fn is_uninterpreted(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_uninterpreted(self.raw) })
    }

    /// Determine if this term is Boolean value true.
    pub fn is_true(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_true(self.raw) })
    }

    /// Determine if this term is Boolean value false.
    pub fn is_false(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_false(self.raw) })
    }

    /// Determine if this term is a bit-vector value representing zero.
    pub fn is_bv_value_zero(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv_value_zero(self.raw) })
    }

    /// Determine if this term is a bit-vector value representing one.
    pub fn is_bv_value_one(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv_value_one(self.raw) })
    }

    /// Determine if this term is a bit-vector value with all bits set to one.
    pub fn is_bv_value_ones(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv_value_ones(self.raw) })
    }

    /// Determine if this term is a bit-vector minimum signed value.
    pub fn is_bv_value_min_signed(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv_value_min_signed(self.raw) })
    }

    /// Determine if this term is a bit-vector maximum signed value.
    pub fn is_bv_value_max_signed(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_bv_value_max_signed(self.raw) })
    }

    /// Determine if this term is a floating-point positive zero (+zero) value.
    pub fn is_fp_value_pos_zero(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp_value_pos_zero(self.raw) })
    }

    /// Determine if this term is a floating-point negative zero (-zero) value.
    pub fn is_fp_value_neg_zero(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp_value_neg_zero(self.raw) })
    }

    /// Determine if this term is a floating-point positive infinity value.
    pub fn is_fp_value_pos_inf(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp_value_pos_inf(self.raw) })
    }

    /// Determine if this term is a floating-point negative infinity value.
    pub fn is_fp_value_neg_inf(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp_value_neg_inf(self.raw) })
    }

    /// Determine if this term is a floating-point NaN value.
    pub fn is_fp_value_nan(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_fp_value_nan(self.raw) })
    }

    /// Determine if this term is a rounding mode RNA value.
    pub fn is_rm_value_rna(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm_value_rna(self.raw) })
    }

    /// Determine if this term is a rounding mode RNE value.
    pub fn is_rm_value_rne(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm_value_rne(self.raw) })
    }

    /// Determine if this term is a rounding mode RTN value.
    pub fn is_rm_value_rtn(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm_value_rtn(self.raw) })
    }

    /// Determine if this term is a rounding mode RTP value.
    pub fn is_rm_value_rtp(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm_value_rtp(self.raw) })
    }

    /// Determine if this term is a rounding mode RTZ value.
    pub fn is_rm_value_rtz(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_is_rm_value_rtz(self.raw) })
    }

    // ── Values ──────────────────────────────────────────────────────

    /// Get the value of a Boolean value term.
    #[track_caller]
    pub fn value_bool(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_term_value_get_bool(self.raw) })
    }

    /// Get the value of a rounding mode value term.
    #[track_caller]
    pub fn value_rm(&self) -> RoundingMode {
        from_c(call(|| unsafe {
            sys::bitwuzla_term_value_get_rm(self.raw)
        }))
    }

    /// Get the raw string representation of a Boolean, bit-vector,
    /// floating-point, or rounding mode value term.
    ///
    /// Bit-vector values are given in `base` 2, 10, or 16, e.g., `"010"` for
    /// bit-vector value 2 of size 3 in base 2 (whereas
    /// [`to_string`](ToString::to_string) gives `"#b010"`). Floating-point
    /// values are always given as their binary IEEE-754 representation.
    #[track_caller]
    pub fn value_str(&self, base: u8) -> String {
        call(|| unsafe { to_string(sys::bitwuzla_term_value_get_str_fmt(self.raw, base)) })
    }

    /// Get the IEEE-754 representation of a floating-point value term as
    /// `(sign, exponent, significand)` bit-vector value strings in `base` 2,
    /// 10, or 16.
    #[track_caller]
    pub fn value_fp_ieee(&self, base: u8) -> (String, String, String) {
        call(|| unsafe {
            let mut sign = std::ptr::null();
            let mut exp = std::ptr::null();
            let mut sig = std::ptr::null();
            sys::bitwuzla_term_value_get_fp_ieee(self.raw, &mut sign, &mut exp, &mut sig, base);
            (to_string(sign), to_string(exp), to_string(sig))
        })
    }

    /// Get the SMT-LIB v2 representation of a floating-point value term as a
    /// real.
    #[track_caller]
    pub fn fp_value_to_real_string(&self) -> String {
        call(|| unsafe { to_string(sys::bitwuzla_term_fp_value_to_real_string(self.raw)) })
    }

    /// Get the SMT-LIB v2 representation of this term, with bit-vector values
    /// in `base` 2, 10, or 16.
    #[track_caller]
    pub fn to_string_fmt(&self, base: u8) -> String {
        call(|| unsafe { to_string(sys::bitwuzla_term_to_string_fmt(self.raw, base)) })
    }

    /// Get the id of this term, unique among the terms of its term manager.
    pub fn id(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_term_get_id(self.raw) })
    }

    /// Get the hash value of this term.
    pub fn hash_value(&self) -> usize {
        call(|| unsafe { sys::bitwuzla_term_hash(self.raw) })
    }

    /// The raw C API handle (not owned).
    pub fn as_raw(&self) -> sys::BitwuzlaTerm {
        self.raw
    }
}

impl Clone for Term {
    fn clone(&self) -> Self {
        Term::from_raw(
            call_reentrant(|| unsafe { sys::bitwuzla_term_copy(self.raw) }),
            &self.tm,
        )
    }
}

impl Drop for Term {
    fn drop(&mut self) {
        call_reentrant(|| unsafe { sys::bitwuzla_term_release(self.raw) });
    }
}

/// The SMT-LIB v2 representation of the term (bit-vector values in binary).
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = call(|| unsafe { to_string(sys::bitwuzla_term_to_string(self.raw)) });
        f.write_str(&s)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Term({self})")
    }
}

/// The C API exports a term to a unique handle per term manager, so handle
/// identity is term identity.
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl Eq for Term {}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}
