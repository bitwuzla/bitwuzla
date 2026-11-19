//! Create Terms (test_api.cpp: Create Terms).
//!
//! Checks on null sorts and terms are not ported, null sorts and terms are
//! not representable; this drops test `mk_term_check_null` entirely. The
//! limits `bzla::FloatingPoint::max_exp_size()` / `max_sig_size()` (C++
//! internals) are replaced by `MAX_EXP_SIZE` / `MAX_SIG_SIZE`.

use bitwuzla::Kind;

use crate::common::{Fixture, MAX_EXP_SIZE, MAX_SIG_SIZE};

#[test]
fn mk_bv_zero() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_zero(&f.fp_sort16));
}

#[test]
fn mk_bv_one() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_one(&f.fp_sort16));
}

#[test]
fn mk_bv_ones() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_ones(&f.fp_sort16));
}

#[test]
fn mk_bv_min_signed() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_min_signed(&f.fp_sort16));
}

#[test]
fn mk_bv_max_signed() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_max_signed(&f.fp_sort16));
}

#[test]
fn mk_fp_pos_zero() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_pos_zero(&f.bv_sort8));
}

#[test]
fn mk_fp_neg_zero() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_neg_zero(&f.bv_sort8));
}

#[test]
fn mk_fp_pos_inf() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_pos_inf(&f.bv_sort8));
}

#[test]
fn mk_fp_neg_inf() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_neg_inf(&f.bv_sort8));
}

#[test]
fn mk_fp_nan() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_nan(&f.bv_sort8));
}

#[test]
fn mk_bv_value() {
    let f = Fixture::new();
    f.tm.mk_bv_value(&f.bv_sort8, "127", 10).unwrap();
    f.tm.mk_bv_value(&f.bv_sort8, "-128", 10).unwrap();
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "256", 10));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "-129", 10));

    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "", 2));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "", 2));

    assert_panics!(
        f.tm.mk_bv_value(&f.fp_sort16, "010", 2),
        "expected bit-vector sort"
    );

    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "11111111010", 2));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "1234567890", 10));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "1234567890aAbBcCdDeEfF", 16));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "1234567890", 2));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "12z4567890", 10));
    assert_err!(f.tm.mk_bv_value(&f.bv_sort8, "12z4567890", 16));
}

#[test]
fn mk_bv_value_uint64() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_bv_value_u64(&f.fp_sort16, 23));
}

#[test]
fn mk_fp_value() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_fp_value(&f.bv_zero8, &f.bv_zero8, &f.bv_zero8));
    assert_panics!(f.tm.mk_fp_value(&f.fp_const16, &f.bv_zero8, &f.bv_zero8));
    assert_panics!(f.tm.mk_fp_value(&f.bv_one1, &f.fp_const16, &f.bv_zero8));
    assert_panics!(f.tm.mk_fp_value(&f.bv_one1, &f.bv_zero8, &f.fp_const16));

    assert_panics!(f.tm.mk_fp_value(&f.bv_const1, &f.bv_zero8, &f.bv_zero8));
    assert_panics!(f.tm.mk_fp_value(&f.bv_one1, &f.bv_const8, &f.bv_zero8));
    assert_panics!(f.tm.mk_fp_value(&f.bv_one1, &f.bv_zero8, &f.bv_const8));
}

#[test]
fn mk_term_check_fp_format() {
    let f = Fixture::new();
    for kind in [Kind::FpToFpFromFp, Kind::FpToFpFromSbv, Kind::FpToFpFromUbv] {
        let arg = if kind == Kind::FpToFpFromFp {
            &f.fp_const16
        } else {
            &f.bv_const8
        };
        let args = [&f.rm_rne, arg];
        assert_panics!(f.tm.mk_term(kind, &args, &[MAX_EXP_SIZE + 1, 11]));
        assert_panics!(f.tm.mk_term(kind, &args, &[5, MAX_SIG_SIZE + 1]));
        f.mk_idx(kind, &args, &[5, 11]);
    }
    // Note: the exponent and significand size are checked before the
    // (exp_size + sig_size == bv_size) check, thus the size of the given
    // bit-vector is irrelevant here.
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromBv, &[&f.bv_const8], &[MAX_EXP_SIZE + 1, 11]));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromBv, &[&f.bv_const8], &[5, MAX_SIG_SIZE + 1]));
    f.mk_idx(
        Kind::FpToFpFromBv,
        &[&f.tm.mk_const(&f.bv_sort16, "bv16")],
        &[5, 11],
    );
    // The exponent and significand size of the floating-point created via
    // FP_FP are determined by the sizes of the given bit-vectors (+1 for the
    // hidden bit).
    let exp_too_large = f.tm.mk_const(&f.tm.mk_bv_sort(MAX_EXP_SIZE + 1), "e");
    let sig_too_large = f.tm.mk_const(&f.tm.mk_bv_sort(MAX_SIG_SIZE), "m");
    assert_panics!(f.tm.mk_term(
        Kind::FpFp,
        &[
            &f.bv_const1,
            &exp_too_large,
            &f.tm.mk_const(&f.bv_sort8, None)
        ],
        &[]
    ));
    assert_panics!(f.tm.mk_term(
        Kind::FpFp,
        &[
            &f.bv_const1,
            &f.tm.mk_const(&f.bv_sort8, None),
            &sig_too_large
        ],
        &[]
    ));
    // A bit-vector of size UINT64_MAX must not overflow the (size + 1) hidden
    // bit adjustment.
    assert_panics!(f.tm.mk_term(
        Kind::FpFp,
        &[
            &f.bv_const1,
            &f.tm.mk_const(&f.bv_sort8, None),
            &f.tm.mk_const(&f.tm.mk_bv_sort(u64::MAX), None)
        ],
        &[]
    ));
    f.mk(
        Kind::FpFp,
        &[
            &f.bv_const1,
            &f.tm.mk_const(&f.bv_sort8, None),
            &f.tm.mk_const(&f.bv_sort23, "bv23"),
        ],
    );
}

#[test]
fn mk_term_check_cnt() {
    let f = Fixture::new();
    let apply_args1 = [&f.bv_one1];
    let apply_args2 = [&f.fun, &f.bv_const8];
    let array_args1 = [&f.array_fpbv];
    let bool_args1 = [&f.true_];
    let bool_args2 = [&f.true_, &f.true_];
    let bv_args1 = [&f.bv_one1];
    let bv_args1_rm = [&f.rm_const];
    let bv_args2 = [&f.bv_zero8, &f.bv_const8];
    let ite_args2 = [&f.true_, &f.bv_const8];
    let fp_args1 = [&f.fp_const16];
    let fp_args1_rm = [&f.rm_const];
    let fp_args2 = [&f.fp_const16, &f.fp_const16];
    let fp_args3_rm = [&f.rm_const, &f.fp_const16, &f.fp_const16];
    let fun_args1 = [&f.var1];

    let idxs1 = [1];
    let idxs2 = [2, 0];
    let fp_idxs1 = [5, 8];

    // bool
    assert_panics!(f.tm.mk_term(Kind::And, &bool_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Iff, &bool_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Implies, &bool_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Not, &bool_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::Or, &bool_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Xor, &bool_args1, &[]));
    // bit-vectors
    assert_panics!(f.tm.mk_term(Kind::Apply, &apply_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Apply, &apply_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArraySelect, &array_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArrayStore, &array_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAdd, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAnd, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAshr, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvConcat, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvDec, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvInc, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvMul, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNand, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNeg, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNor, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNot, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvOr, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRedand, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRedor, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRedxor, &bv_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvOr, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRol, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRor, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSaddOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSdivOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSdiv, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSge, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSgt, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvShl, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvShr, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSle, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSlt, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSmod, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSmulOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSrem, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSsubOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSub, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUaddOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUdiv, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUge, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUgt, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUle, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUlt, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUmulOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUrem, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUsubOverflow, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvXnor, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvXor, &bv_args1, &[]));
    // floating-point
    assert_panics!(f.tm.mk_term(Kind::FpAbs, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpAdd, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpDiv, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpEqual, &fp_args1_rm, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFma, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFp, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpGeq, &fp_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpGt, &fp_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsInf, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsNan, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsNeg, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsNormal, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsPos, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsSubnormal, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsZero, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpLeq, &fp_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpLt, &fp_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMax, &fp_args3_rm, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMin, &fp_args3_rm, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsZero, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMul, &fp_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRem, &fp_args3_rm, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRti, &fp_args3_rm, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSqrt, &fp_args3_rm, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSub, &fp_args2, &[]));
    // others
    assert_panics!(f.tm.mk_term(Kind::Distinct, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Equal, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Exists, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Forall, &bv_args1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Ite, &ite_args2, &[]));
    assert_panics!(f.tm.mk_term(Kind::Lambda, &fun_args1, &[]));
    // indexed
    assert_panics!(f.tm.mk_term(Kind::BvExtract, &bv_args2, &idxs2));
    assert_panics!(f.tm.mk_term(Kind::BvRepeat, &bv_args2, &idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvRoli, &bv_args2, &idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvRori, &bv_args2, &idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvSignExtend, &bv_args2, &idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvZeroExtend, &bv_args2, &idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromBv, &bv_args2, &fp_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromFp, &fp_args3_rm, &fp_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromSbv, &bv_args1_rm, &fp_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromUbv, &bv_args1_rm, &fp_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToSbv, &fp_args1, &idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToUbv, &fp_args1, &idxs1));
}

#[test]
fn mk_term_check_args() {
    let f = Fixture::new();
    let array_select_args2_invalid_1 = [&f.fp_const16, &f.array_fpbv];
    let array_select_args2_invalid_2 = [&f.array_fpbv, &f.bv_const8];

    let array_store_args3_invalid_1 = [&f.fp_const16, &f.array_fpbv, &f.bv_const8];
    let array_store_args3_invalid_2 = [&f.array_fpbv, &f.bv_const8, &f.bv_const8];
    let array_store_args3_invalid_3 = [&f.array_fpbv, &f.fp_const16, &f.fp_const16];

    let apply_args3_invalid_1 = [&f.fun, &f.bv_const8, &f.fun];
    let apply_args3_invalid_2 = [&f.fun, &f.bv_const8, &f.bv_const8, &f.fp_pzero32];

    let bool_args1_invalid = [&f.bv_const8];
    let bool_args2_invalid = [&f.fp_pzero32, &f.fp_pzero32];
    let bool_args2_mis = [&f.true_, &f.bv_const8];

    let bv_args1 = [&f.bv_const8];
    let bv_args1_invalid = [&f.fp_const16];
    let bv_args2_invalid = [&f.fp_const16, &f.fp_const16];
    let bv_args2_mis = [&f.bv_one1, &f.bv_const8];
    let bv_args2_rm = [&f.rm_const, &f.bv_const8];
    let bv_args2_rm_invalid_1 = [&f.bv_const8, &f.bv_const8];
    let bv_args2_rm_invalid_2 = [&f.rm_const, &f.fp_const16];

    let ite_args3_invalid_1 = [&f.true_, &f.bv_const8, &f.bv_one1];
    let ite_args3_invalid_2 = [&f.bv_const8, &f.bv_const8, &f.bv_const8];

    let lambda_args2_invalid_1 = [&f.bv_const8, &f.bv_const8];
    let lambda_args2 = [&f.bound_var, &f.bv_const8];
    let lambda_args3_invalid_1 = [&f.var1, &f.var1, &f.bv_const8];

    let lambda_body = f.mk_idx(
        Kind::FpToFpFromUbv,
        &[&f.rm_const, &f.mk(Kind::BvAdd, &[&f.var2, &f.bv_const8])],
        &[5, 8],
    );
    let lambda_args3 = [&f.var1, &f.var2, &lambda_body];

    let fp_args2_rm = [&f.rm_const, &f.fp_const16];

    let fp_args1_invalid = [&f.bv_one1];
    let fp_args2_invalid = [&f.bv_zero8, &f.bv_const8];
    let fp_args2_mis = [&f.fp_pzero32, &f.fp_const16];
    let fp_args2_rm_invalid_1 = [&f.bv_const8, &f.fp_const16];
    let fp_args2_rm_invalid_2 = [&f.rm_const, &f.bv_const8];
    let fp_args3_rm_mis = [&f.rm_const, &f.fp_pzero32, &f.fp_const16];
    let fp_args3_rm_invalid_1 = [&f.fp_const16, &f.fp_const16, &f.fp_const16];
    let fp_args3_rm_invalid_2 = [&f.rm_const, &f.bv_zero8, &f.fp_const16];
    let fp_args4_mis = [&f.rm_const, &f.fp_pzero32, &f.fp_const16, &f.fp_const16];
    let fp_args4_rm_invalid_1 = [&f.rm_const, &f.bv_zero8, &f.fp_const16, &f.fp_const16];
    let fp_args4_rm_invalid_2 = [&f.fp_const16, &f.fp_const16, &f.fp_const16, &f.fp_const16];

    let fp_fp_args3_invalid_1 = [&f.bv_const8, &f.bv_zero8, &f.bv_ones23];
    let fp_fp_args3_invalid_2 = [&f.bv_one1, &f.fp_pzero32, &f.bv_ones23];
    let fp_fp_args3_invalid_3 = [&f.bv_one1, &f.bv_zero8, &f.fp_pzero32];
    let fp_fp_args3_invalid_4 = [&f.fp_pzero32, &f.bv_zero8, &f.bv_ones23];

    let quant_args2_invalid_1 = [&f.true_, &f.true_];
    let quant_args2_invalid_2 = [&f.var1, &f.bv_const8];
    let quant_args2_invalid_3 = [&f.bound_var, &f.bv_const8];
    let quant_args3_invalid = [&f.var1, &f.var1, &f.bv_const8];

    let bv_idxs1 = [3];
    let bv_idxs2 = [2, 0];
    let bv_extract_idxs2_invalid_1 = [0, 2];
    let bv_extract_idxs2_invalid_2 = [9, 0];
    let bv_repeat_idxs_invalid_1 = [2305843009213693953];
    let bv_repeat_idxs_invalid_2 = [0];
    let bv_extend_idxs_invalid_1 = [u64::MAX];
    let fp_idxs2 = [5, 8];
    let fp_idxs2_invalid_1 = [1, 8];
    let fp_idxs2_invalid_2 = [5, 1];

    // bool
    assert_panics!(f.tm.mk_term(Kind::And, &bool_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::And, &bool_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::Iff, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::Iff, &bool_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::Implies, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::Implies, &bool_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::Not, &bool_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::Or, &bool_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::Xor, &bool_args2_invalid, &[]));
    // bit-vectors
    assert_panics!(f.tm.mk_term(Kind::BvAdd, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAdd, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAnd, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAnd, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAshr, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvAshr, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvDec, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvInc, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvMul, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvMul, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNand, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNand, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNeg, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNor, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNor, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvNot, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvOr, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvOr, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRedand, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRedor, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRedxor, &bv_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvOr, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvOr, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRol, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRol, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRor, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvRor, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSaddOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSaddOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSdivOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSdivOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSdiv, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSdiv, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSge, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSge, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSgt, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSgt, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvShl, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvShl, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvShr, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvShr, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSle, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSle, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSlt, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSlt, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSmod, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSmod, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSmulOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSmulOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSrem, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSrem, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSsubOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSsubOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSub, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvSub, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUaddOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUaddOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUdiv, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUdiv, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUge, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUge, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUgt, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUgt, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUle, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUle, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUlt, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUlt, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUmulOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUmulOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUrem, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUrem, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUsubOverflow, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvUsubOverflow, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvXnor, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvXnor, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvXor, &bv_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::BvXor, &bv_args2_mis, &[]));
    // floating-point
    assert_panics!(f.tm.mk_term(Kind::FpAbs, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpAdd, &fp_args3_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpAdd, &fp_args3_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpAdd, &fp_args3_rm_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpDiv, &fp_args3_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpDiv, &fp_args3_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpDiv, &fp_args3_rm_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpEqual, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpEqual, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFma, &fp_args4_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFma, &fp_args4_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFma, &fp_args4_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFp, &fp_fp_args3_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFp, &fp_fp_args3_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFp, &fp_fp_args3_invalid_3, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpFp, &fp_fp_args3_invalid_4, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpGeq, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpGeq, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpGt, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpGt, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsInf, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsNan, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsNeg, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsNormal, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsPos, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsSubnormal, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsZero, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpLeq, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpLeq, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpLt, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpLt, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMax, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMax, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMin, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMin, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpIsZero, &fp_args1_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMul, &fp_args3_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMul, &fp_args3_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpMul, &fp_args3_rm_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRem, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRem, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRti, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRti, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRti, &fp_args2_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpRti, &fp_args2_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSqrt, &fp_args2_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSqrt, &fp_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSqrt, &fp_args2_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSqrt, &fp_args2_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSub, &fp_args3_rm_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSub, &fp_args3_rm_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::FpSub, &fp_args3_rm_mis, &[]));
    // others
    assert_panics!(f.tm.mk_term(Kind::Apply, &apply_args3_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Apply, &apply_args3_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArraySelect, &array_select_args2_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArraySelect, &array_select_args2_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArrayStore, &array_store_args3_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArrayStore, &array_store_args3_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::ArrayStore, &array_store_args3_invalid_3, &[]));
    assert_panics!(f.tm.mk_term(Kind::Distinct, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::Equal, &bv_args2_mis, &[]));
    assert_panics!(f.tm.mk_term(Kind::Exists, &quant_args2_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Exists, &quant_args2_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::Exists, &quant_args2_invalid_3, &[]));
    assert_panics!(f.tm.mk_term(Kind::Exists, &quant_args3_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::Forall, &quant_args2_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Forall, &quant_args2_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::Forall, &quant_args2_invalid_3, &[]));
    assert_panics!(f.tm.mk_term(Kind::Forall, &quant_args3_invalid, &[]));
    assert_panics!(f.tm.mk_term(Kind::Ite, &ite_args3_invalid_2, &[]));
    assert_panics!(f.tm.mk_term(Kind::Ite, &ite_args3_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Lambda, &lambda_args2_invalid_1, &[]));
    assert_panics!(f.tm.mk_term(Kind::Lambda, &lambda_args3_invalid_1, &[]));
    f.mk(Kind::Lambda, &lambda_args3);
    f.mk(Kind::Lambda, &lambda_args2);
    // indexed
    assert_panics!(f.tm.mk_term(Kind::BvExtract, &bv_args1_invalid, &bv_idxs2));
    assert_panics!(f.tm.mk_term(Kind::BvExtract, &bv_args1, &bv_extract_idxs2_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::BvExtract, &bv_args1, &bv_extract_idxs2_invalid_2));
    assert_panics!(f.tm.mk_term(Kind::BvRepeat, &bv_args1_invalid, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvRepeat, &bv_args1, &bv_repeat_idxs_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::BvRepeat, &bv_args1, &bv_repeat_idxs_invalid_2));
    assert_panics!(f.tm.mk_term(Kind::BvRoli, &bv_args1_invalid, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvRori, &bv_args1_invalid, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvSignExtend, &bv_args1_invalid, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvSignExtend, &bv_args1, &bv_extend_idxs_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::BvZeroExtend, &bv_args1_invalid, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::BvZeroExtend, &bv_args1, &bv_extend_idxs_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromBv, &bv_args1_invalid, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromBv, &bv_args1, &fp_idxs2_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromBv, &bv_args1, &fp_idxs2_invalid_2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromFp, &fp_args2_rm_invalid_1, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromFp, &fp_args2_rm_invalid_2, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromFp, &fp_args2_rm, &fp_idxs2_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromFp, &fp_args2_rm, &fp_idxs2_invalid_2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromSbv, &bv_args2_rm_invalid_1, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromSbv, &bv_args2_rm_invalid_2, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromSbv, &bv_args2_rm, &fp_idxs2_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromSbv, &bv_args2_rm, &fp_idxs2_invalid_2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromUbv, &bv_args2_rm_invalid_1, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromUbv, &bv_args2_rm_invalid_2, &fp_idxs2));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromUbv, &bv_args2_rm, &fp_idxs2_invalid_1));
    assert_panics!(f.tm.mk_term(Kind::FpToFpFromUbv, &bv_args2_rm, &fp_idxs2_invalid_2));
    assert_panics!(f.tm.mk_term(Kind::FpToSbv, &fp_args2_rm_invalid_1, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToSbv, &fp_args2_rm_invalid_2, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToUbv, &fp_args2_rm_invalid_1, &bv_idxs1));
    assert_panics!(f.tm.mk_term(Kind::FpToUbv, &fp_args2_rm_invalid_2, &bv_idxs1));
}

#[test]
fn mk_const() {
    let f = Fixture::new();
    f.tm.mk_const(&f.bv_sort8, None);
    f.tm.mk_const(&f.bv_sort8, "");
}

#[test]
fn mk_const_array() {
    let f = Fixture::new();
    assert_panics!(f.tm.mk_const_array(&f.bv_sort8, &f.bv_one1));
    assert_panics!(f.tm.mk_const_array(&f.arr_sort_bv, &f.array));
    assert_panics!(f.tm.mk_const_array(&f.arr_sort_bvfp, &f.fp_pzero32));

    f.tm.mk_const_array(&f.arr_sort_bvfp, &f.fp_const16);
}

#[test]
fn mk_var() {
    let f = Fixture::new();
    f.tm.mk_var(&f.bv_sort8, None);
    f.tm.mk_var(&f.bv_sort8, "");
    assert_panics!(f.tm.mk_var(&f.fun_sort, "asdf"));
}
