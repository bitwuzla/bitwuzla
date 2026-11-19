//! Create Sorts (test_api.cpp: Create Sorts).
//!
//! Checks for null sorts are not ported, null sorts are not representable.

use crate::common::{Fixture, MAX_EXP_SIZE, MAX_SIG_SIZE};

#[test]
fn mk_array_sort() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_array_sort(&f.arr_sort_bv, &f.bv_sort8));
    assert_panics!(f.tm.mk_array_sort(&f.fun_sort, &f.bv_sort8));
    assert_panics!(f.tm.mk_array_sort(&f.bv_sort8, &f.fun_sort));

    f.tm.mk_array_sort(&f.bv_sort8, &f.arr_sort_bv);
}

#[test]
fn mk_bv_sort() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_sort(0), "must be > 0");
}

#[test]
fn mk_fp_sort() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_sort(0, 8));
    assert_panics!(f.tm.mk_fp_sort(5, 0));
    assert_panics!(f.tm.mk_fp_sort(1, 2));
    assert_panics!(f.tm.mk_fp_sort(2, 1));
    assert_panics!(f.tm.mk_fp_sort(MAX_EXP_SIZE + 1, 150));
    assert_panics!(f.tm.mk_fp_sort(5, MAX_SIG_SIZE + 1));
    assert_panics!(f.tm.mk_fp_sort(MAX_EXP_SIZE + 1, MAX_SIG_SIZE + 1));
}

#[test]
fn mk_fun_sort() {
    let f = Fixture::new();
    let empty: [&bitwuzla::Sort; 0] = [];
    assert_panics!(f.tm.mk_fun_sort(&empty, &f.bv_sort8));
}

#[test]
fn mk_uninterpreted_sort() {
    let f = Fixture::new();
    let s1 = f.tm.mk_uninterpreted_sort(None);
    let s2 = f.tm.mk_uninterpreted_sort("foo");
    let s3 = f.tm.mk_uninterpreted_sort("foo");
    assert!(s1.is_uninterpreted());
    assert!(s2.is_uninterpreted());
    assert!(s3.is_uninterpreted());
    assert_ne!(s1, s2);
    assert_ne!(s1, s3);
    assert_ne!(s2, s3);
}
