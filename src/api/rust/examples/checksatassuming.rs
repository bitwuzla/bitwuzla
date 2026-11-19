//! Port of `examples/cpp/checksatassuming.cpp`.

use bitwuzla::{Bitwuzla, Kind, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let options = Options::new();
    // Then, create a Bitwuzla instance.
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;

    // Create a bit-vector sort of size 1.
    let sortbv1 = tm.mk_bv_sort(1);
    // Create a bit-vector sort of size 2
    let sortbv2 = tm.mk_bv_sort(2);

    // Create bit-vector variables.
    // (declare-const o0 (_ BitVec 1))
    let o0 = tm.mk_const(&sortbv1, "o0");
    // (declare-const o1 (_ BitVec 1))
    let o1 = tm.mk_const(&sortbv1, "o1");
    // (declare-const s0 (_ BitVec 2))
    let s0 = tm.mk_const(&sortbv2, "s0");
    // (declare-const s1 (_ BitVec 2))
    let s1 = tm.mk_const(&sortbv2, "s1");
    // (declare-const s2 (_ BitVec 2))
    let s2 = tm.mk_const(&sortbv2, "s2");
    // (declare-const goal (_ BitVec 2))
    let goal = tm.mk_const(&sortbv2, "goal");

    // Create bit-vector values zero, one, three.
    let zero = tm.mk_bv_zero(&sortbv2);
    let one1 = tm.mk_bv_one(&sortbv1);
    let one2 = tm.mk_bv_one(&sortbv2);
    let three = tm.mk_bv_value_u64(&sortbv2, 3);

    // Add some assertions.
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&s0, &zero], &[]));
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&goal, &three], &[]));

    // (check-sat-assuming ((= s0 goal)))
    let result = bitwuzla.check_sat_assuming(&[tm.mk_term(Kind::Equal, &[&s0, &goal], &[])])?;
    println!("Expect: unsat");
    println!("Bitwuzla: {result}");

    // (assert (= s1 (ite (= o0 (_ sortbv1 1)) (bvadd s0 one) s0)))
    bitwuzla.assert_formula(&tm.mk_term(
        Kind::Equal,
        &[
            &s1,
            &tm.mk_term(
                Kind::Ite,
                &[
                    &tm.mk_term(Kind::Equal, &[&o0, &one1], &[]),
                    &tm.mk_term(Kind::BvAdd, &[&s0, &one2], &[]),
                    &s0,
                ],
                &[],
            ),
        ],
        &[],
    ));

    // (check-sat-assuming ((= s1 goal)))
    let result = bitwuzla.check_sat_assuming(&[tm.mk_term(Kind::Equal, &[&s1, &goal], &[])])?;
    println!("Expect: unsat");
    println!("Bitwuzla: {result}");

    // (assert (= s2 (ite (= o1 (_ sortbv1 1)) (bvadd s1 one) s1)))
    bitwuzla.assert_formula(&tm.mk_term(
        Kind::Equal,
        &[
            &s2,
            &tm.mk_term(
                Kind::Ite,
                &[
                    &tm.mk_term(Kind::Equal, &[&o1, &one1], &[]),
                    &tm.mk_term(Kind::BvAdd, &[&s1, &one2], &[]),
                    &s1,
                ],
                &[],
            ),
        ],
        &[],
    ));

    // (check-sat-assuming ((= s2 goal)))
    let result = bitwuzla.check_sat_assuming(&[tm.mk_term(Kind::Equal, &[&s2, &goal], &[])])?;
    println!("Expect: unsat");
    println!("Bitwuzla: {result}");

    Ok(())
}
