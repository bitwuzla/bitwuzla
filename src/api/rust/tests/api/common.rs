//! Shared fixture and helpers, mirroring the `TestApi` fixture of
//! `test/unit/api/test_api.cpp`.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use bitwuzla::{Kind, Opt, Options, Parser, RoundingMode, Sort, Term, TermManager};

/// Assert that a `bitwuzla::Result` is an error (whose message contains the
/// given substring), for calls whose errors depend on input.
///
/// Corresponds to `ASSERT_THROW` / `ASSERT_EXCEPTION` in the C++ tests.
macro_rules! assert_err {
    ($e:expr $(,)?) => {
        match $e {
            Ok(_) => panic!("expected error from `{}`", stringify!($e)),
            Err(_) => {}
        }
    };
    ($e:expr, $msg:expr $(,)?) => {
        match $e {
            Ok(_) => panic!(
                "expected error containing {:?} from `{}`",
                $msg,
                stringify!($e)
            ),
            Err(err) => assert!(
                err.message().contains($msg),
                "expected error containing {:?} from `{}`, got {:?}",
                $msg,
                stringify!($e),
                err.message()
            ),
        }
    };
}

/// Assert that an expression panics (with a message that contains the given
/// substring), i.e., that the call is rejected as a contract violation.
///
/// Corresponds to `ASSERT_THROW` / `ASSERT_EXCEPTION` in the C++ tests.
macro_rules! assert_panics {
    ($e:expr $(,)?) => {
        assert_panics!($e, "")
    };
    ($e:expr, $msg:expr $(,)?) => {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = $e;
        })) {
            Ok(()) => panic!("expected panic from `{}`", stringify!($e)),
            Err(payload) => {
                let msg = payload
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| payload.downcast_ref::<&str>().copied())
                    .unwrap_or_default();
                assert!(
                    msg.contains($msg),
                    "expected panic containing {:?} from `{}`, got {:?}",
                    $msg,
                    stringify!($e),
                    msg
                );
            }
        }
    };
}

/// The `TestApi` fixture: a term manager with commonly used sorts and terms.
pub struct Fixture {
    pub tm: TermManager,

    // sorts
    pub bool_sort: Sort,
    pub bv_sort1: Sort,
    pub bv_sort8: Sort,
    pub bv_sort16: Sort,
    pub bv_sort23: Sort,
    pub bv_sort32: Sort,
    pub fp_sort16: Sort,
    pub fp_sort32: Sort,
    pub arr_sort_bv: Sort,
    pub arr_sort_bvfp: Sort,
    pub arr_sort_fpbv: Sort,
    pub fun_domain_sorts: Vec<Sort>,
    pub fun_sort: Sort,
    pub fun_sort_fp: Sort,
    pub rm_sort: Sort,
    pub un_sort: Sort,

    // terms
    pub true_: Term,
    pub bv_one1: Term,
    pub bv_ones23: Term,
    pub bv_zero8: Term,
    pub bv_mins8: Term,
    pub bv_maxs8: Term,
    pub fp_pzero32: Term,
    pub fp_nzero32: Term,
    pub fp_pinf32: Term,
    pub fp_ninf32: Term,
    pub fp_nan32: Term,

    pub bool_const: Term,
    pub bv_const1: Term,
    pub bv_const8: Term,
    pub fp_const16: Term,
    pub rm_const: Term,
    pub un_const: Term,

    pub rm_rna: Term,
    pub rm_rne: Term,
    pub rm_rtn: Term,
    pub rm_rtp: Term,
    pub rm_rtz: Term,

    pub fun: Term,
    pub fun_fp: Term,
    pub array_fpbv: Term,
    pub array: Term,
    pub store: Term,

    pub var1: Term,
    pub var2: Term,
    pub bound_var: Term,
    pub bool_var: Term,

    pub bv_const1_true: Term,
    pub bv_const1_false: Term,
    pub and_bv_const1: Term,
    pub eq_bv_const8: Term,

    pub lambda: Term,
    pub bool_lambda_body: Term,
    pub bool_lambda: Term,
    pub bool_apply: Term,

    pub exists_var: Term,
    pub exists: Term,
}

/// Create a term (panics on error).
pub fn mk(tm: &TermManager, kind: Kind, args: &[&Term]) -> Term {
    tm.mk_term(kind, args, &[])
}

/// Create an indexed term (panics on error).
pub fn mk_idx(tm: &TermManager, kind: Kind, args: &[&Term], indices: &[u64]) -> Term {
    tm.mk_term(kind, args, indices)
}

impl Fixture {
    pub fn new() -> Self {
        let tm = TermManager::new();

        let bool_sort = tm.mk_bool_sort();
        let bv_sort1 = tm.mk_bv_sort(1);
        let bv_sort8 = tm.mk_bv_sort(8);
        let bv_sort16 = tm.mk_bv_sort(16);
        let bv_sort23 = tm.mk_bv_sort(23);
        let bv_sort32 = tm.mk_bv_sort(32);
        let fp_sort16 = tm.mk_fp_sort(5, 11);
        let fp_sort32 = tm.mk_fp_sort(8, 24);
        let arr_sort_bv = tm.mk_array_sort(&bv_sort32, &bv_sort8);
        let arr_sort_bvfp = tm.mk_array_sort(&bv_sort8, &fp_sort16);
        let arr_sort_fpbv = tm.mk_array_sort(&fp_sort16, &bv_sort8);
        let fun_domain_sorts = vec![bv_sort8.clone(), fp_sort16.clone(), bv_sort32.clone()];
        let fun_sort = tm.mk_fun_sort(&fun_domain_sorts, &bv_sort8);
        let fun_sort_fp = tm.mk_fun_sort(&fun_domain_sorts, &fp_sort16);
        let rm_sort = tm.mk_rm_sort();
        let un_sort = tm.mk_uninterpreted_sort(None);

        let true_ = tm.mk_true();
        let bv_one1 = tm.mk_bv_one(&bv_sort1);
        let bv_ones23 = tm.mk_bv_ones(&bv_sort23);
        let bv_zero8 = tm.mk_bv_zero(&bv_sort8);
        let bv_mins8 = tm.mk_bv_min_signed(&bv_sort8);
        let bv_maxs8 = tm.mk_bv_max_signed(&bv_sort8);
        let fp_pzero32 = tm.mk_fp_pos_zero(&fp_sort32);
        let fp_nzero32 = tm.mk_fp_neg_zero(&fp_sort32);
        let fp_pinf32 = tm.mk_fp_pos_inf(&fp_sort32);
        let fp_ninf32 = tm.mk_fp_neg_inf(&fp_sort32);
        let fp_nan32 = tm.mk_fp_nan(&fp_sort32);

        let bool_const = tm.mk_const(&bool_sort, "b");
        let bv_const1 = tm.mk_const(&bv_sort1, "bv1");
        let bv_const8 = tm.mk_const(&bv_sort8, "bv8");
        let fp_const16 = tm.mk_const(&fp_sort16, "fp16");
        let rm_const = tm.mk_const(&rm_sort, "rm");
        let un_const = tm.mk_const(&un_sort, "u");

        let rm_rna = tm.mk_rm_value(RoundingMode::Rna);
        let rm_rne = tm.mk_rm_value(RoundingMode::Rne);
        let rm_rtn = tm.mk_rm_value(RoundingMode::Rtn);
        let rm_rtp = tm.mk_rm_value(RoundingMode::Rtp);
        let rm_rtz = tm.mk_rm_value(RoundingMode::Rtz);

        let fun = tm.mk_const(&fun_sort, "fun");
        let fun_fp = tm.mk_const(&fun_sort_fp, "fun_fp");
        let array_fpbv = tm.mk_const(&arr_sort_fpbv, None);
        let array = tm.mk_const(&arr_sort_bv, None);
        let store = mk(
            &tm,
            Kind::ArrayStore,
            &[&array, &tm.mk_const(&bv_sort32, None), &bv_zero8],
        );

        let var1 = tm.mk_var(&bv_sort8, "x");
        let var2 = tm.mk_var(&bv_sort8, "y");
        let bound_var = tm.mk_var(&bv_sort8, "z");
        let bool_var = tm.mk_var(&bool_sort, "p");

        let bv_const1_true = mk(&tm, Kind::Equal, &[&bv_one1, &bv_const1]);
        let bv_const1_false = mk(
            &tm,
            Kind::Equal,
            &[&bv_one1, &mk(&tm, Kind::BvNot, &[&bv_const1])],
        );
        let and_bv_const1 = mk(
            &tm,
            Kind::Equal,
            &[&bv_one1, &mk(&tm, Kind::BvAnd, &[&bv_one1, &bv_const1])],
        );
        let eq_bv_const8 = mk(&tm, Kind::Equal, &[&bv_const8, &bv_zero8]);

        let lambda = mk(
            &tm,
            Kind::Lambda,
            &[&bound_var, &mk(&tm, Kind::BvAdd, &[&bound_var, &bv_const8])],
        );
        let bool_lambda_body = mk(&tm, Kind::Equal, &[&bool_var, &true_]);
        let bool_lambda = mk(&tm, Kind::Lambda, &[&bool_var, &bool_lambda_body]);
        let bool_apply = mk(&tm, Kind::Apply, &[&bool_lambda, &true_]);

        let exists_var = tm.mk_var(&bv_sort8, "q");
        let exists = mk(
            &tm,
            Kind::Exists,
            &[
                &exists_var,
                &mk(
                    &tm,
                    Kind::Equal,
                    &[&bv_zero8, &mk(&tm, Kind::BvMul, &[&bv_const8, &exists_var])],
                ),
            ],
        );

        Self {
            tm,
            bool_sort,
            bv_sort1,
            bv_sort8,
            bv_sort16,
            bv_sort23,
            bv_sort32,
            fp_sort16,
            fp_sort32,
            arr_sort_bv,
            arr_sort_bvfp,
            arr_sort_fpbv,
            fun_domain_sorts,
            fun_sort,
            fun_sort_fp,
            rm_sort,
            un_sort,
            true_,
            bv_one1,
            bv_ones23,
            bv_zero8,
            bv_mins8,
            bv_maxs8,
            fp_pzero32,
            fp_nzero32,
            fp_pinf32,
            fp_ninf32,
            fp_nan32,
            bool_const,
            bv_const1,
            bv_const8,
            fp_const16,
            rm_const,
            un_const,
            rm_rna,
            rm_rne,
            rm_rtn,
            rm_rtp,
            rm_rtz,
            fun,
            fun_fp,
            array_fpbv,
            array,
            store,
            var1,
            var2,
            bound_var,
            bool_var,
            bv_const1_true,
            bv_const1_false,
            and_bv_const1,
            eq_bv_const8,
            lambda,
            bool_lambda_body,
            bool_lambda,
            bool_apply,
            exists_var,
            exists,
        }
    }

    /// Create a term (panics on error).
    pub fn mk(&self, kind: Kind, args: &[&Term]) -> Term {
        mk(&self.tm, kind, args)
    }

    /// Create an indexed term (panics on error).
    pub fn mk_idx(&self, kind: Kind, args: &[&Term], indices: &[u64]) -> Term {
        mk_idx(&self.tm, kind, args, indices)
    }
}

/// `bzla::FloatingPoint::max_exp_size()` (C++ internals), i.e.,
/// `mp_bits_per_limb - 2`.
pub const MAX_EXP_SIZE: u64 = usize::BITS as u64 - 2;
/// `bzla::FloatingPoint::max_sig_size()` (C++ internals), i.e.,
/// `MPFR_PREC_MAX`.
pub const MAX_SIG_SIZE: u64 = i64::MAX as u64 - 256;

/// Determine if the given SAT solver is compiled in (replaces the
/// `BZLA_USE_<SOLVER>` guards of the C++ tests).
pub fn has_sat_solver(name: &str) -> bool {
    Options::new().set(Opt::SatSolver, name).is_ok()
}

/// Determine if experimental floating-point formats are enabled (replaces
/// the `BZLA_USE_FPEXP` guard of the C++ tests).
pub fn has_fpexp() -> bool {
    std::panic::catch_unwind(|| TermManager::new().mk_fp_sort(3, 5)).is_ok()
}

/// A fresh path in the temporary directory (the file is not created).
pub fn temp_path(name: &str) -> PathBuf {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("bitwuzla-rs-{}-{n}-{name}", std::process::id()))
}

/// Read and remove a file.
pub fn read_and_remove(path: &std::path::Path) -> String {
    let content = std::fs::read_to_string(path).unwrap();
    let _ = std::fs::remove_file(path);
    content
}

/// A file with the given content in the temporary directory, removed on
/// drop (the input files the C++ tests write to the working directory).
pub struct TempFile(PathBuf);

impl TempFile {
    pub fn new(name: &str, content: &str) -> Self {
        let path = temp_path(name);
        std::fs::write(&path, content).unwrap();
        Self(path)
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Run `f` on a new parser that writes to a temporary output file and return
/// what it printed (the C++ tests capture stdout instead). The parser is
/// dropped before reading back the output, which flushes it.
pub fn parser_output(
    tm: &TermManager,
    options: &Options,
    language: &str,
    f: impl FnOnce(&mut Parser),
) -> String {
    let outfile = temp_path("parser.out");
    {
        let mut parser = Parser::new(tm, options, language, 2, outfile.to_str().unwrap()).unwrap();
        f(&mut parser);
    }
    read_and_remove(&outfile)
}
