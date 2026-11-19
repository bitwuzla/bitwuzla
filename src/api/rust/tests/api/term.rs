//! Term (test_api.cpp: Term).
//!
//! Checks on null terms are not ported, null terms are not representable.
//! `Term::operator[]` corresponds to indexing into `Term::children()`. The
//! `mk_fp_value(sort, rm, real)` / `mk_fp_value(sort, rm, num, den)`
//! overloads correspond to `mk_fp_from_real` / `mk_fp_from_rational`.

use std::collections::HashMap;

use bitwuzla::{Kind, RoundingMode, Term, TermManager};

use crate::common::{Fixture, has_fpexp};

#[test]
fn term_hash() {
    let f = Fixture::new();
    f.bv_const8.hash_value();
}

#[test]
fn term_sort() {
    let f = Fixture::new();
    assert_eq!(f.bv_const8.sort(), f.bv_sort8);
}

#[test]
fn term_symbol() {
    let f = Fixture::new();
    let x = f.tm.mk_const(&f.bv_sort8, "x");
    assert_eq!(x.symbol().as_deref(), Some("x"));
    let x = f.tm.mk_const(&f.bv_sort8, None);
    assert_eq!(x.symbol(), None);
}

#[test]
fn term_is_const() {
    let f = Fixture::new();
    assert!(f.array.is_const());
    assert!(f.fun.is_const());
    assert!(f.bv_const1.is_const());
    assert!(f.fp_const16.is_const());
    assert!(f.rm_const.is_const());
    assert!(!f.bv_one1.is_const());
    assert!(!f.store.is_const());
}

#[test]
fn term_is_var() {
    let f = Fixture::new();
    assert!(f.var1.is_variable());
    assert!(f.bound_var.is_variable());
    assert!(!f.fp_pzero32.is_variable());
}

#[test]
fn term_is_value() {
    let f = Fixture::new();
    assert!(f.bv_one1.is_value());
    assert!(f.fp_nan32.is_value());
    assert!(!f.fp_const16.is_value());
    assert!(!f.exists.is_value());
}

#[test]
fn term_is_true() {
    let f = Fixture::new();
    assert!(f.tm.mk_true().is_true());
    assert!(!f.tm.mk_false().is_true());
    assert!(!f.tm.mk_bv_one(&f.bv_sort1).is_true());
}

#[test]
fn term_is_false() {
    let f = Fixture::new();
    assert!(f.tm.mk_false().is_false());
    assert!(!f.tm.mk_true().is_false());
    assert!(!f.tm.mk_bv_zero(&f.bv_sort1).is_false());
}

#[test]
fn term_is_bv_value_zero() {
    let f = Fixture::new();
    assert!(f.bv_zero8.is_bv_value_zero());
    assert!(!f.bv_one1.is_bv_value_zero());
    assert!(!f.bv_ones23.is_bv_value_zero());
    assert!(!f.bv_mins8.is_bv_value_zero());
    assert!(!f.bv_maxs8.is_bv_value_zero());
}

#[test]
fn term_is_bv_value_one() {
    let f = Fixture::new();
    assert!(f.bv_one1.is_bv_value_one());
    assert!(!f.bv_ones23.is_bv_value_one());
    assert!(!f.bv_mins8.is_bv_value_one());
    assert!(!f.bv_maxs8.is_bv_value_one());
    assert!(!f.bv_zero8.is_bv_value_one());
}

#[test]
fn term_is_bv_value_ones() {
    let f = Fixture::new();
    assert!(f.bv_ones23.is_bv_value_ones());
    assert!(f.bv_one1.is_bv_value_ones());
    assert!(!f.bv_mins8.is_bv_value_ones());
    assert!(!f.bv_maxs8.is_bv_value_ones());
    assert!(!f.bv_zero8.is_bv_value_ones());
}

#[test]
fn term_is_bv_value_min_signed() {
    let f = Fixture::new();
    assert!(f.bv_mins8.is_bv_value_min_signed());
    assert!(f.bv_one1.is_bv_value_min_signed());
    assert!(!f.bv_ones23.is_bv_value_min_signed());
    assert!(!f.bv_maxs8.is_bv_value_min_signed());
    assert!(!f.bv_zero8.is_bv_value_min_signed());
}

#[test]
fn term_is_bv_value_max_signed() {
    let f = Fixture::new();
    assert!(f.bv_maxs8.is_bv_value_max_signed());
    assert!(!f.bv_mins8.is_bv_value_max_signed());
    assert!(!f.bv_one1.is_bv_value_max_signed());
    assert!(!f.bv_ones23.is_bv_value_max_signed());
    assert!(!f.bv_zero8.is_bv_value_max_signed());
}

#[test]
fn term_is_fp_value_pos_zero() {
    let f = Fixture::new();
    assert!(f.fp_pzero32.is_fp_value_pos_zero());
    assert!(!f.fp_nzero32.is_fp_value_pos_zero());
    assert!(!f.fp_pinf32.is_fp_value_pos_zero());
    assert!(!f.fp_ninf32.is_fp_value_pos_zero());
    assert!(!f.fp_nan32.is_fp_value_pos_zero());
}

#[test]
fn term_is_fp_value_neg_zero() {
    let f = Fixture::new();
    assert!(f.fp_nzero32.is_fp_value_neg_zero());
    assert!(!f.fp_pzero32.is_fp_value_neg_zero());
    assert!(!f.fp_pinf32.is_fp_value_neg_zero());
    assert!(!f.fp_ninf32.is_fp_value_neg_zero());
    assert!(!f.fp_nan32.is_fp_value_neg_zero());
}

#[test]
fn term_is_fp_value_pos_inf() {
    let f = Fixture::new();
    assert!(f.fp_pinf32.is_fp_value_pos_inf());
    assert!(!f.fp_pzero32.is_fp_value_pos_inf());
    assert!(!f.fp_nzero32.is_fp_value_pos_inf());
    assert!(!f.fp_ninf32.is_fp_value_pos_inf());
    assert!(!f.fp_nan32.is_fp_value_pos_inf());
}

#[test]
fn term_is_fp_value_neg_inf() {
    let f = Fixture::new();
    assert!(f.fp_ninf32.is_fp_value_neg_inf());
    assert!(!f.fp_pzero32.is_fp_value_neg_inf());
    assert!(!f.fp_nzero32.is_fp_value_neg_inf());
    assert!(!f.fp_pinf32.is_fp_value_neg_inf());
    assert!(!f.fp_nan32.is_fp_value_neg_inf());
}

#[test]
fn term_is_fp_value_nan() {
    let f = Fixture::new();
    assert!(f.fp_nan32.is_fp_value_nan());
    assert!(!f.fp_pzero32.is_fp_value_nan());
    assert!(!f.fp_nzero32.is_fp_value_nan());
    assert!(!f.fp_pinf32.is_fp_value_nan());
    assert!(!f.fp_ninf32.is_fp_value_nan());
}

#[test]
fn term_is_rm_value_rna() {
    let f = Fixture::new();
    assert!(f.rm_rna.is_rm_value_rna());
    assert!(!f.fp_pzero32.is_rm_value_rna());
    assert!(!f.rm_rne.is_rm_value_rna());
    assert!(!f.rm_rtn.is_rm_value_rna());
    assert!(!f.rm_rtp.is_rm_value_rna());
    assert!(!f.rm_rtz.is_rm_value_rna());
}

#[test]
fn term_is_rm_value_rne() {
    let f = Fixture::new();
    assert!(f.rm_rne.is_rm_value_rne());
    assert!(!f.fun.is_rm_value_rne());
    assert!(!f.rm_rna.is_rm_value_rne());
    assert!(!f.rm_rtn.is_rm_value_rne());
    assert!(!f.rm_rtp.is_rm_value_rne());
    assert!(!f.rm_rtz.is_rm_value_rne());
}

#[test]
fn term_is_rm_value_rtn() {
    let f = Fixture::new();
    assert!(f.rm_rtn.is_rm_value_rtn());
    assert!(!f.true_.is_rm_value_rtn());
    assert!(!f.rm_rna.is_rm_value_rtn());
    assert!(!f.rm_rne.is_rm_value_rtn());
    assert!(!f.rm_rtp.is_rm_value_rtn());
    assert!(!f.rm_rtz.is_rm_value_rtn());
}

#[test]
fn term_is_rm_value_rtp() {
    let f = Fixture::new();
    assert!(f.rm_rtp.is_rm_value_rtp());
    assert!(!f.var2.is_rm_value_rtp());
    assert!(!f.rm_rna.is_rm_value_rtp());
    assert!(!f.rm_rne.is_rm_value_rtp());
    assert!(!f.rm_rtn.is_rm_value_rtp());
    assert!(!f.rm_rtz.is_rm_value_rtp());
}

#[test]
fn term_is_rm_value_rtz() {
    let f = Fixture::new();
    assert!(f.rm_rtz.is_rm_value_rtz());
    assert!(!f.lambda.is_rm_value_rtz());
    assert!(!f.rm_rna.is_rm_value_rtz());
    assert!(!f.rm_rne.is_rm_value_rtz());
    assert!(!f.rm_rtn.is_rm_value_rtz());
    assert!(!f.rm_rtp.is_rm_value_rtz());
}

/// The terms printed with the default format, then in base 10, then in base
/// 16 (as printed to a stream before and after `set_bv_format(10)` and
/// `set_bv_format(16)`).
fn print_bases(terms: &[&Term]) -> String {
    let mut s: String = terms.iter().map(|t| t.to_string()).collect();
    for base in [10, 16] {
        for t in terms {
            s += &t.to_string_fmt(base);
        }
    }
    s
}

#[test]
fn term_print() {
    let f = Fixture::new();
    assert_eq!(
        print_bases(&[&f.and_bv_const1, &f.exists]),
        "(= #b1 (bvand #b1 bv1))\
         (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q)))\
         (= (_ bv1 1) (bvand (_ bv1 1) bv1))\
         (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q)))\
         (= #b1 (bvand #b1 bv1))\
         (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q)))"
    );

    let bv1 = f.tm.mk_bv_sort(1);
    let bv5 = f.tm.mk_bv_sort(5);
    let bv10 = f.tm.mk_bv_sort(10);
    let bv4 = f.tm.mk_bv_sort(4);
    let bv8 = f.tm.mk_bv_sort(8);

    if has_fpexp() {
        {
            let t = f.tm.mk_fp_value(
                &f.tm.mk_bv_one(&bv1),
                &f.tm.mk_bv_value_u64(&bv5, 3),
                &f.tm.mk_bv_value_u64(&bv10, 23),
            );
            assert_eq!(
                print_bases(&[&t]),
                "(fp #b1 #b00011 #b0000010111)\
                 (fp (_ bv1 1) (_ bv3 5) (_ bv23 10))\
                 (fp #b1 #b00011 #b0000010111)"
            );
        }
        {
            let t = f.tm.mk_fp_value(
                &f.tm.mk_bv_one(&bv1),
                &f.tm.mk_bv_value_u64(&bv4, 3),
                &f.tm.mk_bv_value_u64(&bv8, 23),
            );
            assert_eq!(
                print_bases(&[&t]),
                "(fp #b1 #b0011 #b00010111)\
                 (fp (_ bv1 1) (_ bv3 4) (_ bv23 8))\
                 (fp #b1 #b0011 #b00010111)"
            );
        }
    }
}

#[test]
fn term_print_regr0() {
    let f = Fixture::new();
    let s = format!(
        "{}\n{}\n{}\n{}\n{}",
        f.rm_rne, f.rm_rna, f.rm_rtn, f.rm_rtp, f.rm_rtz
    );
    assert_eq!(s, "RNE\nRNA\nRTN\nRTP\nRTZ");
}

#[test]
fn term_print_regr1() {
    let f = Fixture::new();
    let bv_sort5 = f.tm.mk_bv_sort(5);
    let bv_sort10 = f.tm.mk_bv_sort(10);

    let fp_val = f.tm.mk_fp_value(
        &f.tm.mk_bv_zero(&f.bv_sort1),
        &f.tm.mk_bv_zero(&bv_sort5),
        &f.tm.mk_bv_zero(&bv_sort10),
    );
    assert_eq!(fp_val.to_string(), "(fp #b0 #b00000 #b0000000000)");

    let fp_val = f.tm.mk_fp_value(
        &f.tm.mk_bv_one(&f.bv_sort1),
        &f.tm.mk_bv_zero(&bv_sort5),
        &f.tm.mk_bv_zero(&bv_sort10),
    );
    assert_eq!(fp_val.to_string(), "(fp #b1 #b00000 #b0000000000)");

    let fp_val = f.tm.mk_fp_value(
        &f.tm.mk_bv_zero(&f.bv_sort1),
        &f.tm.mk_bv_zero(&bv_sort5),
        &f.tm.mk_bv_one(&bv_sort10),
    );
    assert_eq!(fp_val.to_string(), "(fp #b0 #b00000 #b0000000001)");

    let fp_val = f.tm.mk_fp_value(
        &f.tm.mk_bv_one(&f.bv_sort1),
        &f.tm.mk_bv_zero(&bv_sort5),
        &f.tm.mk_bv_one(&bv_sort10),
    );
    assert_eq!(fp_val.to_string(), "(fp #b1 #b00000 #b0000000001)");
}

#[test]
fn terms_indexed() {
    let f = Fixture::new();
    let fp_term = f.tm.mk_const(&f.fp_sort16, None);
    let bv_term = f.tm.mk_const(&f.bv_sort8, None);
    let rm = f.tm.mk_rm_value(RoundingMode::Rne);

    let idx = f.mk_idx(Kind::FpToSbv, &[&rm, &fp_term], &[8]);
    assert_eq!(idx.num_indices(), 1);
    assert_eq!(idx.indices(), [8]);

    let idx = f.mk_idx(Kind::FpToUbv, &[&rm, &fp_term], &[9]);
    assert_eq!(idx.num_indices(), 1);
    assert_eq!(idx.indices(), [9]);

    let idx = f.mk_idx(Kind::FpToFpFromBv, &[&bv_term], &[3, 5]);
    assert_eq!(idx.num_indices(), 2);
    assert_eq!(idx.indices(), [3, 5]);

    let idx = f.mk_idx(Kind::FpToFpFromFp, &[&rm, &fp_term], &[7, 18]);
    assert_eq!(idx.num_indices(), 2);
    assert_eq!(idx.indices(), [7, 18]);

    let idx = f.mk_idx(Kind::FpToFpFromSbv, &[&rm, &bv_term], &[8, 24]);
    assert_eq!(idx.num_indices(), 2);
    assert_eq!(idx.indices(), [8, 24]);

    let idx = f.mk_idx(Kind::FpToFpFromUbv, &[&rm, &bv_term], &[5, 11]);
    assert_eq!(idx.num_indices(), 2);
    assert_eq!(idx.indices(), [5, 11]);

    let idx = f.mk_idx(Kind::BvExtract, &[&bv_term], &[6, 0]);
    assert_eq!(idx.num_indices(), 2);
    assert_eq!(idx.indices(), [6, 0]);
}

#[test]
fn terms() {
    let f = Fixture::new();
    let tm = &f.tm;
    let array_sort = tm.mk_array_sort(&f.bv_sort16, &f.bv_sort16);
    let domain = [&f.bv_sort16, &f.bv_sort16, &f.bv_sort16];
    let fun_sort = tm.mk_fun_sort(&domain, &f.bv_sort16);

    let fp_args = [
        f.rm_rna.clone(),
        tm.mk_const(&f.fp_sort16, None),
        tm.mk_const(&f.fp_sort16, None),
        tm.mk_const(&f.fp_sort16, None),
    ];

    let bv_args = [
        tm.mk_const(&f.bv_sort16, None),
        tm.mk_const(&f.bv_sort16, None),
        tm.mk_const(&f.bv_sort16, None),
        tm.mk_const(&f.bv_sort16, None),
    ];

    let bool_args = [
        tm.mk_const(&f.bool_sort, None),
        tm.mk_const(&f.bool_sort, None),
    ];

    let mk_all = |kind: Kind, args: &[Term]| tm.mk_term(kind, args, &[]);

    for &kind in Kind::ALL {
        // Every kind is handled: `Kind` is non-exhaustive, so a new kind
        // reaches the last arm.
        let term = match kind {
            Kind::Constant | Kind::ConstArray | Kind::Value | Kind::Variable => continue,

            // Boolean
            Kind::Not => f.mk(kind, &[&bool_args[0]]),

            Kind::And | Kind::Iff | Kind::Implies | Kind::Or | Kind::Xor => {
                mk_all(kind, &bool_args)
            }

            // BV Unary
            Kind::BvDec
            | Kind::BvInc
            | Kind::BvNeg
            | Kind::BvNegOverflow
            | Kind::BvNot
            | Kind::BvRedand
            | Kind::BvRedor
            | Kind::BvRedxor => f.mk(kind, &[&bv_args[0]]),

            // BV Binary
            Kind::BvAshr
            | Kind::BvComp
            | Kind::BvNand
            | Kind::BvNor
            | Kind::BvRol
            | Kind::BvRor
            | Kind::BvSaddOverflow
            | Kind::BvSdivOverflow
            | Kind::BvSdiv
            | Kind::BvSge
            | Kind::BvSgt
            | Kind::BvShl
            | Kind::BvShr
            | Kind::BvSle
            | Kind::BvSlt
            | Kind::BvSmod
            | Kind::BvSmulOverflow
            | Kind::BvSrem
            | Kind::BvSsubOverflow
            | Kind::BvSub
            | Kind::BvUaddOverflow
            | Kind::BvUdiv
            | Kind::BvUge
            | Kind::BvUgt
            | Kind::BvUle
            | Kind::BvUlt
            | Kind::BvUmulOverflow
            | Kind::BvUrem
            | Kind::BvUsubOverflow
            | Kind::BvXnor => f.mk(kind, &[&bv_args[0], &bv_args[1]]),

            // BV Binary+
            Kind::BvAdd | Kind::BvAnd | Kind::BvConcat | Kind::BvMul | Kind::BvOr | Kind::BvXor => {
                mk_all(kind, &bv_args)
            }

            Kind::Distinct | Kind::Equal => mk_all(kind, &bv_args),

            // BV indexed
            Kind::BvExtract => f.mk_idx(kind, &[&bv_args[0]], &[3, 2]),

            Kind::BvRepeat
            | Kind::BvRoli
            | Kind::BvRori
            | Kind::BvSignExtend
            | Kind::BvZeroExtend => f.mk_idx(kind, &[&bv_args[0]], &[5]),

            // Arrays
            Kind::ArraySelect => f.mk(kind, &[&tm.mk_const(&array_sort, None), &bv_args[0]]),

            Kind::ArrayStore => f.mk(
                kind,
                &[&tm.mk_const(&array_sort, None), &bv_args[0], &bv_args[1]],
            ),

            Kind::Apply => f.mk(
                kind,
                &[
                    &tm.mk_const(&fun_sort, None),
                    &bv_args[0],
                    &bv_args[1],
                    &bv_args[2],
                ],
            ),

            // Binder
            Kind::Exists | Kind::Forall | Kind::Lambda => {
                let vars = [tm.mk_var(&f.bv_sort16, None), tm.mk_var(&f.bv_sort16, None)];
                // body
                f.mk(kind, &[&vars[0], &vars[1], &mk_all(Kind::BvSlt, &vars)])
            }

            // FP Unary
            Kind::FpAbs
            | Kind::FpIsInf
            | Kind::FpIsNan
            | Kind::FpIsNeg
            | Kind::FpIsNormal
            | Kind::FpIsPos
            | Kind::FpIsSubnormal
            | Kind::FpIsZero
            | Kind::FpNeg => f.mk(kind, &[&fp_args[1]]),

            // FP Binary
            Kind::FpEqual
            | Kind::FpGeq
            | Kind::FpGt
            | Kind::FpLeq
            | Kind::FpLt
            | Kind::FpMax
            | Kind::FpMin
            | Kind::FpRem => f.mk(kind, &[&fp_args[1], &fp_args[2]]),

            Kind::FpSqrt | Kind::FpRti => f.mk(kind, &[&fp_args[0], &fp_args[1]]),

            // FP Ternary
            Kind::FpAdd | Kind::FpDiv | Kind::FpMul | Kind::FpSub => {
                mk_all(kind, &fp_args[..fp_args.len() - 1])
            }

            Kind::FpFp => f.mk(
                kind,
                &[
                    &tm.mk_const(&tm.mk_bv_sort(1), None),
                    &tm.mk_const(&tm.mk_bv_sort(5), None),
                    &tm.mk_const(&tm.mk_bv_sort(10), None),
                ],
            ),

            // FP Quaternery
            Kind::FpFma => mk_all(kind, &fp_args),

            // FP indexed
            Kind::FpToFpFromBv => f.mk_idx(kind, &[&bv_args[0]], &[5, 11]),

            Kind::FpToFpFromSbv | Kind::FpToFpFromUbv => {
                f.mk_idx(kind, &[&fp_args[0], &bv_args[0]], &[5, 11])
            }

            Kind::FpToFpFromFp => f.mk_idx(kind, &[&fp_args[0], &fp_args[1]], &[5, 11]),

            Kind::FpToSbv | Kind::FpToUbv => f.mk_idx(kind, &[&fp_args[0], &fp_args[1]], &[16]),

            // Others
            Kind::Ite => f.mk(kind, &[&bool_args[0], &bv_args[0], &bv_args[1]]),

            _ => panic!("unhandled kind {kind:?}"),
        };

        let children = term.children();
        let size = children.len();

        if term.is_const() || term.is_variable() || term.is_value() {
            assert!(children.is_empty());
            continue;
        }

        assert!(size > 0);
        assert_eq!(term.num_children(), size);
        for (i, child) in children.iter().enumerate() {
            assert_eq!(&term.children()[i], child);
        }

        let tterm = if term.kind() == Kind::ConstArray {
            assert_eq!(size, 1);
            tm.mk_const_array(&term.sort(), &children[0])
        } else {
            let kind = term.kind();
            if term.num_indices() > 0 {
                tm.mk_term(kind, &children, &term.indices())
            } else if matches!(kind, Kind::Lambda | Kind::Forall | Kind::Exists) {
                // TODO: variables are already bound and can't be passed to mk_term
                // create new vars and substitute
                term.clone()
            } else {
                assert!(kind != Kind::BvNot || size == 1);
                mk_all(kind, &children)
            }
        };
        assert_eq!(tterm, term);
    }

    assert_eq!(f.bv_const8.kind(), Kind::Constant);
    assert!(f.bv_const8.children().is_empty());

    assert_eq!(f.rm_const.kind(), Kind::Constant);
    assert!(f.rm_const.children().is_empty());

    assert_eq!(f.un_const.kind(), Kind::Constant);
    assert!(f.un_const.children().is_empty());

    let bv_var = tm.mk_var(&f.bv_sort16, None);
    assert_eq!(bv_var.kind(), Kind::Variable);
    assert!(bv_var.children().is_empty());

    let rm_val = tm.mk_rm_value(RoundingMode::Rna);
    assert_eq!(rm_val.kind(), Kind::Value);
    assert!(rm_val.children().is_empty());

    let fp_from_real_val = tm.mk_fp_from_real(&f.fp_sort16, &rm_val, "1.1").unwrap();
    assert_eq!(fp_from_real_val.kind(), Kind::Value);
    assert!(fp_from_real_val.children().is_empty());

    let fp_from_real = tm
        .mk_fp_from_real(&f.fp_sort16, &f.rm_const, "1.1")
        .unwrap();
    assert_eq!(fp_from_real.kind(), Kind::Ite);
    assert!(!fp_from_real.children().is_empty());

    let fp_from_rat_val = tm
        .mk_fp_from_rational(&f.fp_sort16, &rm_val, "1", "2")
        .unwrap();
    assert_eq!(fp_from_rat_val.kind(), Kind::Value);
    assert!(fp_from_rat_val.children().is_empty());

    let fp_from_rat = tm
        .mk_fp_from_rational(&f.fp_sort16, &f.rm_const, "1", "2")
        .unwrap();
    assert_eq!(fp_from_rat.kind(), Kind::Ite);
    assert!(!fp_from_rat.children().is_empty());

    let fp_nan = tm.mk_fp_nan(&f.fp_sort16);
    assert_eq!(fp_nan.kind(), Kind::Value);
    assert!(fp_nan.children().is_empty());

    let bv_one = tm.mk_bv_one(&f.bv_sort16);
    assert_eq!(bv_one.kind(), Kind::Value);
    assert!(bv_one.children().is_empty());

    let bv_val = tm.mk_bv_value(&f.bv_sort16, "43", 10).unwrap();
    assert_eq!(bv_val.kind(), Kind::Value);
    assert!(bv_val.children().is_empty());

    // TODO enable when implemented
    // let const_array = tm.mk_const_array(&array_sort, &bv_val).unwrap();
    // assert_eq!(const_array.kind(), Kind::Value);
    // assert!(const_array.children().is_empty());
}

#[test]
fn substitute() {
    let f = Fixture::new();
    let domain = [&f.bv_sort16, &f.bv_sort16, &f.bv_sort16];
    let fun_sort = f.tm.mk_fun_sort(&domain, &f.bool_sort);
    let array_sort = f.tm.mk_array_sort(&f.bv_sort16, &f.bv_sort16);

    let bv_const = f.tm.mk_const(&f.bv_sort16, None);
    let bv_value = f.tm.mk_bv_value(&f.bv_sort16, "143", 10).unwrap();

    // simple substitution const -> value
    {
        let map = HashMap::from([(bv_const.clone(), bv_value.clone())]);
        let result = f.tm.substitute_term(&bv_const, &map);
        assert_eq!(result, bv_value);
    }

    // (sdiv x y) -> (sdiv value y)
    {
        let x = f.tm.mk_const(&f.bv_sort16, None);
        let y = f.tm.mk_const(&f.bv_sort16, None);

        let map = HashMap::from([(x.clone(), bv_value.clone())]);

        let result = f.tm.substitute_term(&f.mk(Kind::BvSdiv, &[&x, &y]), &map);
        assert_eq!(result, f.mk(Kind::BvSdiv, &[&bv_value, &y]));
    }

    // partial substitution of variables in quantified formula
    {
        let mut args = vec![
            f.tm.mk_const(&fun_sort, None),
            f.tm.mk_var(&f.bv_sort16, "x"),
            f.tm.mk_var(&f.bv_sort16, "y"),
            f.tm.mk_var(&f.bv_sort16, "z"),
        ];
        args.push(f.tm.mk_term(Kind::Apply, &args, &[]));
        let q = f.tm.mk_term(Kind::Forall, &args[1..], &[]);

        let map = HashMap::from([
            (args[1].clone(), f.tm.mk_const(&f.bv_sort16, "cx")),
            (args[2].clone(), f.tm.mk_const(&f.bv_sort16, "cy")),
        ]);

        let apply = f.mk(
            Kind::Apply,
            &[&args[0], &map[&args[1]], &map[&args[2]], &args[3]],
        );
        let expected = f.mk(Kind::Forall, &[&args[3], &apply]);

        let result = f.tm.substitute_term(&q, &map);
        assert_eq!(result, expected);
    }

    // substitute term in constant array
    {
        let term = f.tm.mk_const(&f.bv_sort16, None);
        let const_array = f.tm.mk_const_array(&array_sort, &term);

        let map = HashMap::from([(term.clone(), bv_value.clone())]);

        let result = f.tm.substitute_term(&const_array, &map);

        let expected = f.tm.mk_const_array(&array_sort, &bv_value);
        assert_eq!(result, expected);
        assert_eq!(result.kind(), Kind::ConstArray);
    }
}

#[test]
fn substitute2() {
    let f = Fixture::new();
    let bv8 = f.tm.mk_bv_sort(8);
    let x = f.tm.mk_const(&bv8, "x");
    let one = f.tm.mk_bv_one(&bv8);
    let btrue = f.tm.mk_true();
    let addxx = f.mk(Kind::BvAdd, &[&x, &x]);
    let addoo = f.mk(Kind::BvAdd, &[&one, &one]);

    assert_panics!(f.tm.substitute_term(&addxx, [(&one, &btrue)]));

    assert_eq!(f.tm.substitute_term(&addxx, [(&x, &one)]), addoo);
    assert_eq!(f.tm.substitute_term(&addxx, [(&one, &x)]), addxx);

    // simultaneous substitution
    let y = f.tm.mk_const(&bv8, "y");
    let addxy = f.mk(Kind::BvAdd, &[&x, &y]);
    let addyo = f.mk(Kind::BvAdd, &[&y, &one]);
    assert_panics!(f.tm.substitute_term(&addxy, [(&x, &y), (&y, &btrue)]));
    assert_eq!(f.tm.substitute_term(&addxy, [(&x, &y), (&y, &one)]), addyo);
    // a term substituted with itself is kept as is
    assert_eq!(
        f.tm.substitute_term(
            &f.mk(Kind::BvMul, &[&addxy, &x]),
            [(&addxy, &addxy), (&x, &one)]
        ),
        f.mk(Kind::BvMul, &[&addxy, &one])
    );

    let mut terms = vec![addxx.clone(), addxy.clone()];
    let expected = vec![f.mk(Kind::BvAdd, &[&y, &y]), f.mk(Kind::BvAdd, &[&y, &x])];
    f.tm.substitute_terms(&mut terms, [(&x, &y), (&y, &x)]);
    assert_eq!(terms, expected);

    // terms of another term manager
    let tm = TermManager::new();
    let z = tm.mk_const(&tm.mk_bv_sort(8), None);
    let addzz = tm.mk_term(Kind::BvAdd, &[&z, &z], &[]);
    assert_panics!(f.tm.substitute_term(&addzz, [(&x, &one)]));
    assert_panics!(f.tm.substitute_term(&addxx, [(&z, &z)]));
}

#[test]
fn substitute_quant() {
    let f = Fixture::new();
    let bv8 = f.tm.mk_bv_sort(8);
    let one = f.tm.mk_bv_one(&bv8);
    let a = f.tm.mk_const(&bv8, "a");
    let b = f.tm.mk_const(&bv8, "b");
    let x = f.tm.mk_var(&bv8, "x");
    let y = f.tm.mk_var(&bv8, "y");
    let z = f.tm.mk_var(&bv8, "z");
    let ultxy = f.mk(Kind::BvUlt, &[&x, &y]);

    // instantiate a binder in the middle of the quantifier prefix
    {
        let body = f.mk(Kind::And, &[&ultxy, &f.mk(Kind::BvUlt, &[&y, &z])]);
        let q = f.mk(Kind::Forall, &[&x, &f.mk(Kind::Exists, &[&y, &z, &body])]);
        let expected = f.mk(
            Kind::Forall,
            &[
                &x,
                &f.mk(
                    Kind::Exists,
                    &[&z, &f.tm.substitute_term(&body, [(&y, &a)])],
                ),
            ],
        );
        assert_eq!(f.tm.substitute_term(&q, [(&y, &a)]), expected);
    }

    // a binder whose variable is substituted with itself is not instantiated
    {
        let q = f.mk(Kind::Forall, &[&x, &y, &ultxy]);
        assert_eq!(f.tm.substitute_term(&q, [(&x, &x)]), q);
    }

    // a binder below the top-level quantifier prefix shadows its variable
    {
        let eqxb = f.mk(Kind::Equal, &[&x, &b]);
        let q = f.mk(Kind::Forall, &[&x, &eqxb]);
        let t = f.mk(Kind::And, &[&f.mk(Kind::Equal, &[&x, &a]), &q]);
        let expected = f.mk(Kind::And, &[&f.mk(Kind::Equal, &[&b, &a]), &q]);
        assert_eq!(f.tm.substitute_term(&t, [(&x, &b)]), expected);
        // the term with a top-level binder is instantiated, the other one is not
        let mut terms = vec![q.clone(), t.clone()];
        f.tm.substitute_terms(&mut terms, [(&x, &b)]);
        assert_eq!(terms[0], f.mk(Kind::Equal, &[&b, &b]));
        assert_eq!(terms[1], expected);
    }

    // a binder that would capture a substituted variable is renamed
    {
        let addy1 = f.mk(Kind::BvAdd, &[&y, &one]);
        let q = f.mk(Kind::Forall, &[&y, &ultxy]);
        let result = f.tm.substitute_term(&q, [(&x, &addy1)]);
        assert_eq!(result.kind(), Kind::Forall);
        let children = result.children();
        assert_ne!(children[0], y);
        assert_eq!(children[1], f.mk(Kind::BvUlt, &[&addy1, &children[0]]));
        // also if the binder is kept in the quantifier prefix
        let q = f.mk(Kind::Forall, &[&y, &x, &ultxy]);
        let result = f.tm.substitute_term(&q, [(&x, &addy1)]);
        assert_eq!(result.kind(), Kind::Forall);
        let children = result.children();
        assert_ne!(children[0], y);
        assert_eq!(children[1], f.mk(Kind::BvUlt, &[&addy1, &children[0]]));
    }

    // substituting a constant with a variable is not capture-avoiding
    {
        let q = f.mk(Kind::Forall, &[&x, &f.mk(Kind::BvUlt, &[&x, &a])]);
        let t = f.mk(Kind::And, &[&f.mk(Kind::Equal, &[&a, &b]), &q]);
        let expected = f.mk(
            Kind::And,
            &[
                &f.mk(Kind::Equal, &[&x, &b]),
                &f.mk(Kind::Forall, &[&x, &f.mk(Kind::BvUlt, &[&x, &x])]),
            ],
        );
        assert_eq!(f.tm.substitute_term(&t, [(&a, &x)]), expected);
    }
}

#[test]
fn substitute_lambda() {
    let f = Fixture::new();
    let bv8 = f.tm.mk_bv_sort(8);
    let a = f.tm.mk_const(&bv8, "a");
    let b = f.tm.mk_const(&bv8, "b");
    let x = f.tm.mk_var(&bv8, "x");
    let y = f.tm.mk_var(&bv8, "y");
    let addxa = f.mk(Kind::BvAdd, &[&x, &a]);
    let lam = f.mk(Kind::Lambda, &[&x, &addxa]);

    // a lambda is not instantiated, it shadows its variable
    assert_eq!(f.tm.substitute_term(&lam, [(&x, &b)]), lam);
    assert_eq!(f.tm.substitute_term(&lam, [(&x, &y)]), lam);
    {
        let app = f.mk(Kind::Apply, &[&lam, &b]);
        let t = f.mk(Kind::Equal, &[&app, &x]);
        assert_eq!(
            f.tm.substitute_term(&t, [(&x, &b)]),
            f.mk(Kind::Equal, &[&app, &b])
        );
    }

    // substitution below a lambda
    assert_eq!(
        f.tm.substitute_term(&lam, [(&a, &b)]),
        f.mk(Kind::Lambda, &[&x, &f.mk(Kind::BvAdd, &[&x, &b])])
    );

    // beta-reduction by substituting in the body
    assert_eq!(
        f.tm.substitute_term(&lam.children()[1], [(&x, &b)]),
        f.mk(Kind::BvAdd, &[&b, &a])
    );
    {
        let lam2 = f.mk(Kind::Lambda, &[&x, &y, &f.mk(Kind::BvAdd, &[&x, &y])]);
        assert_eq!(
            f.tm.substitute_term(&lam2.children()[1].children()[1], [(&x, &a), (&y, &b)]),
            f.mk(Kind::BvAdd, &[&a, &b])
        );
    }

    // a lambda that would capture a substituted variable is renamed
    {
        let muly = f.mk(Kind::BvMul, &[&y, &y]);
        let lamy = f.mk(Kind::Lambda, &[&y, &f.mk(Kind::BvAdd, &[&x, &y])]);
        let result = f.tm.substitute_term(&lamy, [(&x, &muly)]);
        assert_eq!(result.kind(), Kind::Lambda);
        let children = result.children();
        assert_ne!(children[0], y);
        assert_eq!(children[1], f.mk(Kind::BvAdd, &[&muly, &children[0]]));
    }
}

#[test]
fn term_print1() {
    let f = Fixture::new();
    let a = f.tm.mk_const(&f.bv_sort1, "a");
    let t = f.mk(Kind::BvNot, &[&a]);
    assert_eq!(t.to_string_fmt(2), "(bvnot a)");
    assert_eq!(t.to_string(), "(bvnot a)");
}

#[test]
fn term_print2() {
    let f = Fixture::new();
    let fn1_1 = f.tm.mk_fun_sort(&[&f.bv_sort1], &f.bv_sort1);
    let t = f.tm.mk_const(&fn1_1, "f");
    assert_eq!(t.to_string_fmt(2), "f");
    assert_eq!(t.to_string(), "f");
}

#[test]
fn term_print3() {
    let f = Fixture::new();
    let ar1_1 = f.tm.mk_array_sort(&f.bv_sort1, &f.bv_sort1);
    let t = f.tm.mk_const(&ar1_1, "a");
    assert_eq!(t.to_string_fmt(2), "a");
    assert_eq!(t.to_string(), "a");
}

#[test]
fn term_arrayfun() {
    let f = Fixture::new();
    let bvsort = f.tm.mk_bv_sort(4);
    let funsort = f.tm.mk_fun_sort(&[&bvsort], &bvsort);
    let arrsort = f.tm.mk_array_sort(&bvsort, &bvsort);
    let fun = f.tm.mk_const(&funsort, "f");
    let a = f.tm.mk_const(&arrsort, "a");
    assert!(fun.sort() != a.sort());
    assert!(fun.sort().is_fun());
    assert!(!a.sort().is_fun());
    assert!(!fun.sort().is_array());
    assert!(a.sort().is_array());
}

#[test]
fn term_fp_val_to_real_str() {
    let f = Fixture::new();
    let fp_from_real =
        f.tm.mk_fp_from_real(&f.fp_sort16, &f.rm_const, "1.1")
            .unwrap();
    assert_panics!(fp_from_real.fp_value_to_real_string());

    let rm_val = f.tm.mk_rm_value(RoundingMode::Rna);
    let fp_val = f.tm.mk_fp_from_real(&f.fp_sort16, &rm_val, "1.1").unwrap();
    assert_eq!(fp_val.fp_value_to_real_string(), "563/512");

    let fp_val =
        f.tm.mk_fp_from_rational(&f.fp_sort16, &rm_val, "1", "2")
            .unwrap();
    assert_eq!(fp_val.fp_value_to_real_string(), "1/2");

    let fp_val =
        f.tm.mk_fp_from_rational(&f.fp_sort16, &rm_val, "6", "3")
            .unwrap();
    assert_eq!(fp_val.fp_value_to_real_string(), "2.0");

    let fp_val = f.tm.mk_fp_from_real(&f.fp_sort16, &rm_val, "-4.3").unwrap();
    assert_eq!(fp_val.fp_value_to_real_string(), "-1101/256");

    let fp_val = f.tm.mk_fp_from_real(&f.fp_sort16, &rm_val, "-3.0").unwrap();
    assert_eq!(fp_val.fp_value_to_real_string(), "-3.0");

    let fp_val = f.tm.mk_fp_pos_zero(&f.fp_sort16);
    assert_eq!(fp_val.fp_value_to_real_string(), "0.0");

    let fp_val = f.tm.mk_fp_neg_zero(&f.fp_sort16);
    assert_eq!(fp_val.fp_value_to_real_string(), "0.0");

    let fp_val = f.tm.mk_fp_pos_inf(&f.fp_sort16);
    assert_eq!(
        fp_val.fp_value_to_real_string(),
        "(fp.to_real (_ +oo 5 11))"
    );

    let fp_val = f.tm.mk_fp_neg_inf(&f.fp_sort16);
    assert_eq!(
        fp_val.fp_value_to_real_string(),
        "(fp.to_real (_ -oo 5 11))"
    );

    let fp_val = f.tm.mk_fp_nan(&f.fp_sort16);
    assert_eq!(
        fp_val.fp_value_to_real_string(),
        "(fp.to_real (_ NaN 5 11))"
    );
}
