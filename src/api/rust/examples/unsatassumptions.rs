//! Port of `examples/cpp/unsatassumptions.cpp`.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, RoundingMode, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();
    // (set-option :produce-unsat-assumptions true)
    options.set(Opt::ProduceUnsatAssumptions, true)?;
    // Then, create a Bitwuzla instance.
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;

    // Create Boolean sort.
    let sortbool = tm.mk_bool_sort();
    // Create a bit-vector sort of size 2.
    let sortbv2 = tm.mk_bv_sort(2);
    // Create a bit-vector sort of size 4.
    let sortbv4 = tm.mk_bv_sort(4);
    // Create Float16 floatinf-point sort.
    let sortfp16 = tm.mk_fp_sort(5, 11);
    // Create bit-vector variables.
    // (declare-const x0 (_ BitVec 4))
    let x0 = tm.mk_const(&sortbv4, "x0");
    // (declare-const x1 (_ BitVec 2))
    let x1 = tm.mk_const(&sortbv2, "x1");
    // (declare-const x2 (_ BitVec 2))
    let x2 = tm.mk_const(&sortbv2, "x2");
    // (declare-const x3 (_ BitVec 2))
    let x3 = tm.mk_const(&sortbv2, "x3");
    // (declare-const x4 Float16)
    let x4 = tm.mk_const(&sortfp16, "x4");

    // Create FP positive zero.
    let fpzero = tm.mk_fp_pos_zero(&sortfp16);
    // Create BV zero of size 4.
    let bvzero = tm.mk_bv_zero(&sortbv4);

    // (define-fun f0 ((a Float16)) Bool (fp.gt a (_ +zero 5 11)))
    let a_f0 = tm.mk_var(&sortfp16, "a_f0");
    let f0 = tm.mk_term(
        Kind::Lambda,
        &[&a_f0, &tm.mk_term(Kind::FpGt, &[&a_f0, &fpzero], &[])],
        &[],
    );

    // (define-fun f1 ((a Float16)) (_ BitVec 4) (ite (f0 a) x0 #b0000))
    let a_f1 = tm.mk_var(&sortfp16, "a_f1");
    let f1 = tm.mk_term(
        Kind::Lambda,
        &[
            &a_f1,
            &tm.mk_term(
                Kind::Ite,
                &[&tm.mk_term(Kind::Apply, &[&f0, &a_f1], &[]), &x0, &bvzero],
                &[],
            ),
        ],
        &[],
    );

    // (define-fun f2 ((a Float16)) (_ BitVec 2) ((_ extract 1 0) (f1 a)))
    let a_f2 = tm.mk_var(&sortfp16, "a_f2");
    let f2 = tm.mk_term(
        Kind::Lambda,
        &[
            &a_f2,
            &tm.mk_term(
                Kind::BvExtract,
                &[&tm.mk_term(Kind::Apply, &[&f1, &a_f2], &[])],
                &[1, 0],
            ),
        ],
        &[],
    );

    // (assert (! (bvult x2 (f2 (_ +zero 5 11))) :named a0))
    let a0 = tm.mk_const(&sortbool, "a0");
    let assumption0 = tm.mk_term(
        Kind::BvUlt,
        &[&x2, &tm.mk_term(Kind::Apply, &[&f2, &fpzero], &[])],
        &[],
    );
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&a0, &assumption0], &[]));
    // (assert (! (= x1 x2 x3) :named a1))
    let a1 = tm.mk_const(&sortbool, "a1");
    let assumption1 = tm.mk_term(Kind::Equal, &[&x1, &x2, &x3], &[]);
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&a1, &assumption1], &[]));
    // (assert (!(= x4 ((_ to_fp_unsigned 5 11) RNE x3)) :named a2))
    let a2 = tm.mk_const(&sortbool, "a2");
    let assumption2 = tm.mk_term(
        Kind::Equal,
        &[
            &x4,
            &tm.mk_term(
                Kind::FpToFpFromUbv,
                &[&tm.mk_rm_value(RoundingMode::Rne), &x3],
                &[5, 11],
            ),
        ],
        &[],
    );
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&a2, &assumption2], &[]));

    // (check-sat-assuming (assumption0 assumption1 assumption2))
    let result = bitwuzla.check_sat_assuming(&[&a0, &a1, &a2])?;
    println!("Expect: unsat");
    println!("Bitwuzla: {result}");

    // (get-unsat-assumptions)
    let unsat_assumptions = bitwuzla.get_unsat_assumptions();
    print!("Unsat Assumptions: {{");
    for a in &unsat_assumptions {
        print!(" {a}");
    }
    println!(" }}");

    Ok(())
}
