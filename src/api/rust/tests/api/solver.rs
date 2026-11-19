//! Bitwuzla (test_api.cpp: Bitwuzla).
//!
//! Checks on null terms are not ported, null terms are not representable;
//! this drops the "null node in assertions" block of `get_interpolant`.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, RoundingMode, SatResult};

use crate::common::{Fixture, has_sat_solver};

/// The unsat assumption and unsat core tests require an incremental SAT
/// solver (`BZLA_USE_CADICAL || BZLA_USE_CMS` in the C++ tests).
fn has_incremental_sat_solver() -> bool {
    has_sat_solver("cadical") || has_sat_solver("cms")
}

#[test]
fn push() {
    let f = Fixture::new();
    {
        let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
        bitwuzla.push(0);
        bitwuzla.push(2);
    }
}

#[test]
fn pop() {
    let f = Fixture::new();
    {
        let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
        assert_panics!(bitwuzla.pop(2));
        bitwuzla.pop(0);
        bitwuzla.push(2);
        bitwuzla.pop(2);
    }
}

#[test]
fn assert_formula() {
    let f = Fixture::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    assert_panics!(bitwuzla.assert_formula(&f.bv_const8));

    assert_panics!(bitwuzla.assert_formula(&f.bv_one1));
    assert_panics!(bitwuzla.assert_formula(&f.bool_var));
    // TODO: this should throw, not implemented yet
    // assert_err!(bitwuzla.assert_formula(&f.bool_lambda));
    // assert_err!(bitwuzla.assert_formula(&f.bool_lambda_body));

    bitwuzla.assert_formula(&f.bool_apply);
    bitwuzla.assert_formula(&f.bool_const);
}

#[test]
fn get_assertions() {
    let f = Fixture::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    bitwuzla.assert_formula(&f.tm.mk_true());
    bitwuzla.assert_formula(&f.tm.mk_false());
    let expected = vec![f.tm.mk_true(), f.tm.mk_false()];
    assert_eq!(bitwuzla.get_assertions(), expected);
}

#[test]
fn is_unsat_assumption() {
    if !has_incremental_sat_solver() {
        return;
    }
    let f = Fixture::new();
    {
        let mut options = Options::new();
        options.set(Opt::ProduceUnsatAssumptions, false).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
        assert_panics!(bitwuzla.is_unsat_assumption(&f.bool_const));
    }
    {
        let mut options = Options::new();
        options.set(Opt::ProduceUnsatAssumptions, true).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();

        bitwuzla.assert_formula(&f.true_);
        bitwuzla.check_sat_assuming(&[&f.bool_const]).unwrap();
        assert_panics!(bitwuzla.is_unsat_assumption(&f.bool_const));

        bitwuzla
            .check_sat_assuming(&[&f.bool_const, &f.mk(Kind::Not, &[&f.bool_const])])
            .unwrap();

        assert_panics!(bitwuzla.is_unsat_assumption(&f.bv_const8));
        assert!(!bitwuzla.is_unsat_assumption(&f.true_));

        assert!(!bitwuzla.is_unsat_assumption(&f.bool_var));
        assert_panics!(bitwuzla.is_unsat_assumption(&f.bool_lambda));
        assert!(!bitwuzla.is_unsat_assumption(&f.bool_lambda_body));

        bitwuzla.is_unsat_assumption(&f.bool_const);
    }
}

#[test]
fn get_unsat_assumptions() {
    if !has_incremental_sat_solver() {
        return;
    }
    let f = Fixture::new();
    {
        let mut options = Options::new();
        options.set(Opt::ProduceUnsatAssumptions, false).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
        assert_panics!(bitwuzla.get_unsat_assumptions());
    }
    {
        let mut options = Options::new();
        options.set(Opt::ProduceUnsatAssumptions, true).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();

        bitwuzla.assert_formula(&f.true_);
        bitwuzla.check_sat_assuming(&[&f.bool_const]).unwrap();
        assert_panics!(bitwuzla.get_unsat_assumptions());

        bitwuzla
            .check_sat_assuming(&[
                &f.bv_const1_true,
                &f.bv_const1_false,
                &f.and_bv_const1,
                &f.eq_bv_const8,
            ])
            .unwrap();
        assert!(bitwuzla.is_unsat_assumption(&f.bv_const1_true));
        assert!(bitwuzla.is_unsat_assumption(&f.bv_const1_false));
        assert!(!bitwuzla.is_unsat_assumption(&f.and_bv_const1));
        assert!(!bitwuzla.is_unsat_assumption(&f.eq_bv_const8));
        let unsat_ass = bitwuzla.get_unsat_assumptions();
        assert_eq!(unsat_ass.len(), 2);
        for a in &unsat_ass {
            assert!(bitwuzla.is_unsat_assumption(a));
        }
        for a in &unsat_ass {
            bitwuzla.assert_formula(a);
        }
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    }
}

#[test]
fn get_unsat_core() {
    if !has_incremental_sat_solver() {
        return;
    }
    let f = Fixture::new();
    {
        let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
        assert_panics!(bitwuzla.get_unsat_core());
    }
    // Non-incremental SAT solvers do not support unsat cores and assumptions.
    for solver in ["kissat", "gimsatul"] {
        if !has_sat_solver(solver) {
            continue;
        }
        {
            let mut options = Options::new();
            options.set(Opt::ProduceUnsatCores, true).unwrap();
            options.set(Opt::SatSolver, solver).unwrap();
            assert_err!(Bitwuzla::new(&f.tm, &options));
        }
        {
            let mut options = Options::new();
            options.set(Opt::ProduceUnsatAssumptions, true).unwrap();
            options.set(Opt::SatSolver, solver).unwrap();
            assert_err!(Bitwuzla::new(&f.tm, &options));
        }
    }
    {
        let mut options = Options::new();
        options.set(Opt::ProduceUnsatCores, true).unwrap();
        options.set(Opt::ProduceUnsatAssumptions, true).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();

        bitwuzla.assert_formula(&f.true_);
        bitwuzla.check_sat_assuming(&[&f.bv_const1_true]).unwrap();
        assert_panics!(bitwuzla.get_unsat_core());

        bitwuzla.assert_formula(&f.bv_const1_true);
        bitwuzla
            .check_sat_assuming(&[&f.bv_const1_false, &f.eq_bv_const8])
            .unwrap();

        assert!(bitwuzla.is_unsat_assumption(&f.bv_const1_false));
        assert!(!bitwuzla.is_unsat_assumption(&f.eq_bv_const8));
        let unsat_core = bitwuzla.get_unsat_core();
        assert_eq!(unsat_core.len(), 2);
        assert!(unsat_core.contains(&f.bv_const1_true));
        assert!(unsat_core.contains(&f.bv_const1_false));

        bitwuzla
            .check_sat_assuming(&[&f.bv_const1_false, &f.and_bv_const1, &f.eq_bv_const8])
            .unwrap();

        assert!(bitwuzla.is_unsat_assumption(&f.bv_const1_false));
        assert!(!bitwuzla.is_unsat_assumption(&f.and_bv_const1));
        assert!(!bitwuzla.is_unsat_assumption(&f.eq_bv_const8));
        let unsat_core = bitwuzla.get_unsat_core();
        assert_eq!(unsat_core.len(), 2);
        assert!(unsat_core.contains(&f.bv_const1_true));
        assert!(unsat_core.contains(&f.bv_const1_false));

        let unsat_ass = bitwuzla.get_unsat_assumptions();
        assert_eq!(unsat_ass.len(), 1);
        assert_eq!(unsat_ass[0], f.bv_const1_false);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
        bitwuzla.assert_formula(&unsat_ass[0]);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    }
}

#[test]
fn simplify() {
    let f = Fixture::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    assert_ne!(
        bitwuzla.simplify_term(&f.and_bv_const1).unwrap(),
        f.and_bv_const1
    );
    bitwuzla.assert_formula(&f.bool_const);
    bitwuzla.assert_formula(&f.and_bv_const1);
    bitwuzla.simplify().unwrap();
}

#[test]
fn simplify_term() {
    let f = Fixture::new();
    let bv4 = f.tm.mk_bv_sort(4);
    let bv4_a = f.tm.mk_const(&bv4, "a");
    let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    assert_eq!(
        bitwuzla
            .simplify_term(&f.mk(Kind::BvAdd, &[&bv4_a, &f.mk(Kind::BvNeg, &[&bv4_a])]))
            .unwrap(),
        f.tm.mk_bv_value_u64(&bv4, 0)
    );
    let fp32 = f.tm.mk_fp_sort(8, 24);
    let fp32_a = f.tm.mk_const(&fp32, "a");
    let fpabs = f.mk(Kind::FpAbs, &[&fp32_a]);
    assert_eq!(
        bitwuzla
            .simplify_term(&f.mk(Kind::FpAbs, &[&fpabs]))
            .unwrap(),
        fpabs
    );
}

#[test]
fn check_sat() {
    let f = Fixture::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    bitwuzla.check_sat().unwrap();
    bitwuzla.check_sat().unwrap();
}

#[test]
fn get_value() {
    let f = Fixture::new();
    {
        let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
        assert_panics!(bitwuzla.get_value(&f.bv_const8));
    }
    {
        let mut options = Options::new();
        options.set(Opt::ProduceModels, true).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
        bitwuzla.assert_formula(&f.bv_const1_true);
        assert_eq!(
            bitwuzla.check_sat_assuming(&[&f.bv_const1_false]).unwrap(),
            SatResult::Unsat
        );
        assert_panics!(bitwuzla.get_value(&f.bool_const));
        bitwuzla.check_sat().unwrap();
        bitwuzla.get_value(&f.bool_const);
        bitwuzla.get_value(&f.bv_const1_false);
    }
    {
        let mut options = Options::new();
        options.set(Opt::ProduceModels, true).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
        bitwuzla.assert_formula(&f.exists);
        assert_panics!(bitwuzla.get_value(&f.bv_const8));
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
        let value = bitwuzla.get_value(&f.bv_const8);
        bitwuzla.assert_formula(&f.mk(Kind::Equal, &[&f.bv_const8, &value]));
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
    }
}

#[test]
fn get_value_nested_array() {
    let f = Fixture::new();
    // Deep enough to exhaust the native stack if default model value
    // construction recurses per nesting level.
    let depth = 100000;
    let mut sort = f.tm.mk_bool_sort();
    for _ in 0..depth {
        sort = f.tm.mk_array_sort(&f.tm.mk_bool_sort(), &sort);
    }
    let x = f.tm.mk_const(&sort, "x");

    let mut options = Options::new();
    options.set(Opt::ProduceModels, true).unwrap();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
    bitwuzla.assert_formula(&f.mk(Kind::Equal, &[&x, &x]));
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
    let val = bitwuzla.get_value(&x);
    assert_eq!(val.kind(), Kind::ConstArray);
    assert_eq!(val.sort(), sort);
}

#[test]
fn get_bool_value() {
    let f = Fixture::new();
    assert!(f.true_.value_bool());
    assert!(!f.tm.mk_false().value_bool());
    assert_eq!(f.true_.value_str(2), "true");
    assert_eq!(f.tm.mk_false().value_str(2), "false");
}

#[test]
fn get_bv_value() {
    let f = Fixture::new();
    assert_panics!(f.fun.value_str(2));
    assert_eq!(f.bv_one1.value_str(2), "1");

    let bv_maxs32 = f.tm.mk_bv_max_signed(&f.bv_sort32);
    assert_eq!(bv_maxs32.value_str(2), "01111111111111111111111111111111");
    assert_eq!(bv_maxs32.value_str(10), "2147483647");
    assert_eq!(bv_maxs32.value_str(16), "7fffffff");
    let bv = |value: &str| f.tm.mk_bv_value(&f.bv_sort8, value, 10).unwrap();
    assert_eq!(bv("-1").value_str(2), "11111111");
    assert_eq!(bv("-1").value_str(10), "255");
    assert_eq!(bv("-1").value_str(16), "ff");
    assert_eq!(bv("-123").value_str(2), "10000101");
    assert_eq!(bv("-123").value_str(10), "133");
    assert_eq!(bv("-123").value_str(16), "85");
    assert_eq!(bv("-128").value_str(2), "10000000");
    assert_eq!(bv("-128").value_str(10), "128");
    assert_eq!(bv("-128").value_str(16), "80");
}

#[test]
fn get_fp_value() {
    let f = Fixture::new();
    // single bit-vector string
    assert_eq!(f.fp_nan32.value_str(2), "01111111110000000000000000000000");
    assert_eq!(
        f.fp_nzero32.value_str(2),
        "10000000000000000000000000000000"
    );
    // component bit-vector strings
    let tuple = |sign: &str, exp: &str, sig: &str| (sign.into(), exp.into(), sig.into());
    assert_eq!(
        f.fp_nan32.value_fp_ieee(2),
        tuple("0", "11111111", "10000000000000000000000")
    );
    assert_eq!(
        f.fp_nzero32.value_fp_ieee(2),
        tuple("1", "00000000", "00000000000000000000000")
    );
}

#[test]
fn get_rm_value() {
    let f = Fixture::new();
    assert_eq!(f.rm_rna.value_rm(), RoundingMode::Rna);
    assert_eq!(f.rm_rne.value_rm(), RoundingMode::Rne);
    assert_eq!(f.rm_rtn.value_rm(), RoundingMode::Rtn);
    assert_eq!(f.rm_rtp.value_rm(), RoundingMode::Rtp);
    assert_eq!(f.rm_rtz.value_rm(), RoundingMode::Rtz);
    assert_eq!(f.rm_rna.value_str(2), "RNA");
    assert_eq!(f.rm_rne.value_str(2), "RNE");
    assert_eq!(f.rm_rtn.value_str(2), "RTN");
    assert_eq!(f.rm_rtp.value_str(2), "RTP");
    assert_eq!(f.rm_rtz.value_str(2), "RTZ");
}

#[test]
fn get_interpolant() {
    if !has_sat_solver("cadical") {
        return;
    }
    let f = Fixture::new();
    let bv4 = f.tm.mk_bv_sort(4);
    let x = f.tm.mk_const(&bv4, "x");
    let y = f.tm.mk_const(&bv4, "y");
    let z = f.tm.mk_const(&bv4, "z");
    let zero = f.tm.mk_bv_zero(&bv4);
    let one = f.tm.mk_bv_one(&bv4);
    // (= z (bvadd x y))
    let a0 = f.mk(Kind::Equal, &[&z, &f.mk(Kind::BvAdd, &[&x, &y])]);
    // (distinct x y)
    let a1 = f.mk(Kind::Distinct, &[&x, &y]);
    // (and
    //   (distinct x (_ bv0 1024))
    //   (= (bvand x (bvsub x (_ bv1 1024))) (_ bv0 1024))))
    let a2 = f.mk(Kind::Distinct, &[&x, &zero]);
    let a3 = f.mk(
        Kind::Equal,
        &[
            &f.mk(Kind::BvAnd, &[&x, &f.mk(Kind::BvSub, &[&x, &one])]),
            &zero,
        ],
    );
    // (and
    //   (distinct y (_ bv0 1024))
    //   (= (bvand y (bvsub y (_ bv1 1024))) (_ bv0 1024)))
    let a4 = f.mk(Kind::Distinct, &[&y, &zero]);
    let a5 = f.mk(
        Kind::Equal,
        &[
            &f.mk(Kind::BvAnd, &[&y, &f.mk(Kind::BvSub, &[&y, &one])]),
            &zero,
        ],
    );
    //   (and
    //     (distinct z (_ bv0 1024))
    //     (= (bvand z (bvsub z (_ bv1 1024))) (_ bv0 1024)))
    let b0 = f.mk(Kind::Distinct, &[&z, &zero]);
    let b1 = f.mk(
        Kind::Equal,
        &[
            &f.mk(Kind::BvAnd, &[&z, &f.mk(Kind::BvSub, &[&z, &one])]),
            &zero,
        ],
    );

    let a = vec![a0, a1, a2, a3, a4, a5];
    // A solver with the assertions of A, b0 and b1.
    let solver = |produce_interpolants: bool| {
        let mut options = Options::new();
        options
            .set(Opt::ProduceInterpolants, produce_interpolants)
            .unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
        for t in &a {
            bitwuzla.assert_formula(t);
        }
        bitwuzla.assert_formula(&b0);
        bitwuzla.assert_formula(&b1);
        bitwuzla
    };

    {
        // produce-interpolants not enabled
        let mut bitwuzla = solver(false);
        bitwuzla.check_sat().unwrap();
        assert_err!(bitwuzla.get_interpolant(&a));
    }
    {
        // given assertion is not currently asserted
        let mut bitwuzla = solver(true);
        let mut a = a.clone();
        a.push(f.mk(Kind::Not, &[&a[0]]));
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
        assert_err!(bitwuzla.get_interpolant(&a));
    }
    {
        let mut bitwuzla = solver(true);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
        bitwuzla.get_interpolant(&a).unwrap();
    }
    {
        let mut bitwuzla = solver(true);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
        let partitions: Vec<Vec<_>> = a.iter().map(|t| vec![t]).collect();
        let interpolants = bitwuzla.get_interpolants(&partitions).unwrap();
        assert_eq!(interpolants.len(), 6);
        // Partitions of owned terms.
        let partitions: Vec<Vec<_>> = a.iter().map(|t| vec![t.clone()]).collect();
        assert_eq!(
            bitwuzla.get_interpolants(&partitions).unwrap(),
            interpolants
        );
    }
}
