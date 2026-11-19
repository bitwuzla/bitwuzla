use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use libbitwuzla_sys as sys;

use crate::error::{call, call_reentrant};
use crate::ffi::{slice, to_opt_string, to_string};
use crate::term_manager::TmHandle;

/// A Bitwuzla sort (type).
///
/// Sorts are created via [`TermManager`](crate::TermManager). A `Sort` keeps
/// its term manager alive, so it may outlive the `TermManager` value that
/// created it. Two sorts are equal if they denote the same sort of the same
/// term manager.
pub struct Sort {
    pub(crate) raw: sys::BitwuzlaSort,
    pub(crate) tm: Rc<TmHandle>,
}

impl Sort {
    /// Take ownership of a sort returned by the C API.
    pub(crate) fn from_raw(raw: sys::BitwuzlaSort, tm: &Rc<TmHandle>) -> Self {
        assert!(!raw.is_null(), "Bitwuzla returned a null sort");
        Self {
            raw,
            tm: Rc::clone(tm),
        }
    }

    /// Take ownership of an array of sorts returned by the C API.
    ///
    /// # Safety
    ///
    /// `ptr` must point to `size` sorts (or be `NULL`).
    pub(crate) unsafe fn vec_from_raw(
        ptr: *const sys::BitwuzlaSort,
        size: usize,
        tm: &Rc<TmHandle>,
    ) -> Vec<Sort> {
        unsafe { slice(ptr, size) }
            .iter()
            .map(|&raw| Sort::from_raw(raw, tm))
            .collect()
    }

    /// Get the size of a bit-vector sort.
    #[track_caller]
    pub fn bv_size(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_sort_bv_get_size(self.raw) })
    }

    /// Get the exponent size of a floating-point sort.
    #[track_caller]
    pub fn fp_exp_size(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_sort_fp_get_exp_size(self.raw) })
    }

    /// Get the significand size of a floating-point sort (including the
    /// hidden bit).
    #[track_caller]
    pub fn fp_sig_size(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_sort_fp_get_sig_size(self.raw) })
    }

    /// Get the index sort of an array sort.
    #[track_caller]
    pub fn array_index(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_sort_array_get_index(self.raw) }),
            &self.tm,
        )
    }

    /// Get the element sort of an array sort.
    #[track_caller]
    pub fn array_element(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_sort_array_get_element(self.raw) }),
            &self.tm,
        )
    }

    /// Get the domain sorts of a function sort.
    #[track_caller]
    pub fn fun_domain(&self) -> Vec<Sort> {
        call(|| unsafe {
            let mut size = 0;
            let ptr = sys::bitwuzla_sort_fun_get_domain_sorts(self.raw, &mut size);
            Sort::vec_from_raw(ptr, size, &self.tm)
        })
    }

    /// Get the codomain sort of a function sort.
    #[track_caller]
    pub fn fun_codomain(&self) -> Sort {
        Sort::from_raw(
            call(|| unsafe { sys::bitwuzla_sort_fun_get_codomain(self.raw) }),
            &self.tm,
        )
    }

    /// Get the arity of a function sort.
    #[track_caller]
    pub fn fun_arity(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_sort_fun_get_arity(self.raw) })
    }

    /// Get the symbol of an uninterpreted sort, `None` if it has none.
    #[track_caller]
    pub fn uninterpreted_symbol(&self) -> Option<String> {
        call(|| unsafe { to_opt_string(sys::bitwuzla_sort_get_uninterpreted_symbol(self.raw)) })
    }

    /// Determine if this is an array sort.
    pub fn is_array(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_array(self.raw) })
    }

    /// Determine if this is a Boolean sort.
    pub fn is_bool(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_bool(self.raw) })
    }

    /// Determine if this is a bit-vector sort.
    pub fn is_bv(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_bv(self.raw) })
    }

    /// Determine if this is a floating-point sort.
    pub fn is_fp(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_fp(self.raw) })
    }

    /// Determine if this is a function sort.
    pub fn is_fun(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_fun(self.raw) })
    }

    /// Determine if this is a rounding mode sort.
    pub fn is_rm(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_rm(self.raw) })
    }

    /// Determine if this is an uninterpreted sort.
    pub fn is_uninterpreted(&self) -> bool {
        call(|| unsafe { sys::bitwuzla_sort_is_uninterpreted(self.raw) })
    }

    /// Get the id of this sort, unique among the sorts of its term manager.
    pub fn id(&self) -> u64 {
        call(|| unsafe { sys::bitwuzla_sort_get_id(self.raw) })
    }

    /// Get the hash value of this sort.
    pub fn hash_value(&self) -> usize {
        call(|| unsafe { sys::bitwuzla_sort_hash(self.raw) })
    }

    /// The raw C API handle (not owned).
    pub fn as_raw(&self) -> sys::BitwuzlaSort {
        self.raw
    }
}

impl Clone for Sort {
    fn clone(&self) -> Self {
        Sort::from_raw(
            call_reentrant(|| unsafe { sys::bitwuzla_sort_copy(self.raw) }),
            &self.tm,
        )
    }
}

impl Drop for Sort {
    fn drop(&mut self) {
        call_reentrant(|| unsafe { sys::bitwuzla_sort_release(self.raw) });
    }
}

/// The SMT-LIB v2 representation of the sort.
impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = call(|| unsafe { to_string(sys::bitwuzla_sort_to_string(self.raw)) });
        f.write_str(&s)
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Sort({self})")
    }
}

/// The C API exports a sort to a unique handle per term manager, so handle
/// identity is sort identity.
impl PartialEq for Sort {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl Eq for Sort {}

impl Hash for Sort {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}
