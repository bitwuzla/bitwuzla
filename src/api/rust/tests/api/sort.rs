//! Sort (test_api.cpp: Sort).
//!
//! Checks on null sorts are not ported, null sorts are not representable.

use bitwuzla::Kind;

use crate::common::Fixture;

#[test]
fn sort_hash() {
    let f = Fixture::new();
    f.bv_sort8.hash_value();
}

#[test]
fn sort_bv_size() {
    let f = Fixture::new();
    assert_panics!(f.fp_sort16.bv_size());
    assert_eq!(f.bv_sort8.bv_size(), 8);
}

#[test]
fn sort_fp_exp_size() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort8.fp_exp_size());
    assert_eq!(f.fp_sort16.fp_exp_size(), 5);
}

#[test]
fn sort_fp_sig_size() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort8.fp_sig_size());
    assert_eq!(f.fp_sort16.fp_sig_size(), 11);
}

#[test]
fn sort_array_index() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort23.array_index());
    assert!(f.arr_sort_bvfp.array_index().is_bv());
}

#[test]
fn sort_array_element() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort23.array_element());
    assert!(f.arr_sort_bvfp.array_element().is_fp());
}

#[test]
fn sort_fun_domain_sorts() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort8.fun_domain());
    let domain_sorts = f.fun_sort.fun_domain();
    assert_eq!(domain_sorts.len(), 3);
    assert_eq!(f.bv_sort8, domain_sorts[0]);
    assert_eq!(f.fp_sort16, domain_sorts[1]);
    assert_eq!(f.bv_sort32, domain_sorts[2]);
}

#[test]
fn sort_fun_codomain() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort8.fun_codomain());
    assert_eq!(f.fun_sort.fun_codomain(), f.bv_sort8);
}

#[test]
fn sort_fun_arity() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort8.fun_arity());
    assert_eq!(f.fun_sort.fun_arity(), 3);
}

#[test]
fn sort_uninterpreted_symbol() {
    let f = Fixture::new();
    assert_panics!(f.bv_sort8.uninterpreted_symbol());
    let s1 = f.tm.mk_uninterpreted_sort(None);
    let s2 = f.tm.mk_uninterpreted_sort("foo");
    let s3 = f.tm.mk_uninterpreted_sort("foo");
    let s4 = f.tm.mk_uninterpreted_sort("bar");
    assert_eq!(s1.uninterpreted_symbol(), None);
    assert_eq!(s2.uninterpreted_symbol().as_deref(), Some("foo"));
    assert_eq!(s3.uninterpreted_symbol().as_deref(), Some("foo"));
    assert_eq!(s4.uninterpreted_symbol().as_deref(), Some("bar"));
}

#[test]
fn sort_is_equal() {
    let f = Fixture::new();
    assert_eq!(f.bv_sort8, f.tm.mk_bv_sort(8));
    assert_ne!(f.bv_sort8, f.tm.mk_bv_sort(9));
}

#[test]
fn sort_is_array() {
    let f = Fixture::new();
    assert!(f.arr_sort_bv.is_array());
    assert!(f.arr_sort_bvfp.is_array());
    assert!(f.arr_sort_fpbv.is_array());
    assert!(!f.fun_sort.is_array());
    assert!(!f.fun_sort_fp.is_array());
    assert!(!f.bv_sort8.is_array());
    assert!(!f.fp_sort16.is_array());
    assert!(!f.un_sort.is_array());
}

#[test]
fn sort_is_bv() {
    let f = Fixture::new();
    assert!(f.bv_sort1.is_bv());
    assert!(f.bv_sort8.is_bv());
    assert!(f.bv_sort23.is_bv());
    assert!(f.bv_sort32.is_bv());
    assert!(!f.fp_sort16.is_bv());
    assert!(!f.arr_sort_bv.is_bv());
    assert!(!f.arr_sort_bvfp.is_bv());
    assert!(!f.arr_sort_fpbv.is_bv());
    assert!(!f.fun_sort.is_bv());
    assert!(!f.un_sort.is_bv());
}

#[test]
fn sort_is_fp() {
    let f = Fixture::new();
    assert!(f.fp_sort16.is_fp());
    assert!(f.fp_sort32.is_fp());
    assert!(!f.bv_sort8.is_fp());
    assert!(!f.arr_sort_bv.is_fp());
    assert!(!f.arr_sort_bvfp.is_fp());
    assert!(!f.fun_sort_fp.is_fp());
    assert!(!f.un_sort.is_fp());
}

#[test]
fn sort_is_fun() {
    let f = Fixture::new();
    assert!(f.fun_sort.is_fun());
    assert!(f.fun_sort_fp.is_fun());
    assert!(!f.arr_sort_bv.is_fun());
    assert!(!f.arr_sort_bvfp.is_fun());
    assert!(!f.arr_sort_fpbv.is_fun());
    assert!(!f.bv_sort8.is_fun());
    assert!(!f.fp_sort16.is_fun());
    assert!(!f.un_sort.is_fun());
}

#[test]
fn sort_is_rm() {
    let f = Fixture::new();
    assert!(f.rm_sort.is_rm());
    assert!(!f.bv_sort8.is_rm());
    assert!(!f.fp_sort16.is_rm());
    assert!(!f.arr_sort_bv.is_rm());
    assert!(!f.un_sort.is_rm());
}

#[test]
fn sort_is_uninterpreted() {
    let f = Fixture::new();
    assert!(!f.rm_sort.is_uninterpreted());
    assert!(!f.bv_sort8.is_uninterpreted());
    assert!(!f.fp_sort16.is_uninterpreted());
    assert!(!f.arr_sort_bv.is_uninterpreted());
    assert!(f.un_sort.is_uninterpreted());
}

#[test]
fn sort_print() {
    let f = Fixture::new();
    let s = format!("{}{}{}{}", f.bv_sort1, f.bv_sort8, f.rm_sort, f.fp_sort32);
    assert_eq!(
        s,
        "(_ BitVec 1)(_ BitVec 8)RoundingMode(_ FloatingPoint 8 24)"
    );
}

#[test]
fn regr1() {
    let f = Fixture::new();
    let fun_sort = f.tm.mk_fun_sort(&[&f.bv_sort8], &f.bv_sort8);
    f.tm.mk_array_sort(&f.bv_sort8, &f.bv_sort8);
    let args = [
        f.tm.mk_const(&f.bv_sort8, "x"),
        f.tm.mk_const(&fun_sort, "f"),
    ];
    assert_panics!(f.tm.mk_term(Kind::Apply, &args, &[]));
}

#[test]
fn regr2() {
    let f = Fixture::new();
    let fun_sort = f.tm.mk_fun_sort(&[&f.bv_sort8], &f.bv_sort8);
    let array_sort = f.tm.mk_array_sort(&f.bv_sort8, &f.bv_sort8);
    assert_ne!(fun_sort, array_sort);
    let fun = f.tm.mk_const(&fun_sort, None);
    let array = f.tm.mk_const(&array_sort, None);
    assert_eq!(array_sort, array.sort());
    assert_eq!(fun_sort, fun.sort());
    assert_ne!(fun.sort(), array.sort());
    assert!(fun.sort().is_fun());
    assert!(array.sort().is_array());
}
