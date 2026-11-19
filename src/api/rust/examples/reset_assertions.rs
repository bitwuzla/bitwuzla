//! Port of `examples/cpp/reset_assertions.cpp`.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();
    // (set-option :produce-models true)
    options.set(Opt::ProduceModels, true)?;
    // Then, create a Bitwuzla instance.
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;

    // Create a bit-vector sort of size 3.
    let sortbv3 = tm.mk_bv_sort(3);

    // (declare-const x (_ BitVec 3))
    let x = tm.mk_const(&sortbv3, "x");

    // (assert (= x #b010))
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&x, &tm.mk_bv_value_u64(&sortbv3, 2)], &[]));
    // (check-sat)
    let result = bitwuzla.check_sat()?;
    println!("Expect: sat");
    println!("Bitwuzla: {result}");

    // (assert (= x #b001))
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&x, &tm.mk_bv_value_u64(&sortbv3, 1)], &[]));
    // (check-sat)
    let result = bitwuzla.check_sat()?;
    println!("Expect: unsat");
    println!("Bitwuzla: {result}");

    // (reset-assertions)
    // Note: Bitwuzla does not provide an explicit API function for
    //       reset-assertions since this is achieved by simply discarding
    //       the current Bitwuzla instance and creating a new one.
    bitwuzla = Bitwuzla::new(&tm, &options)?;

    // (assert (= x #b011))
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&x, &tm.mk_bv_value_u64(&sortbv3, 3)], &[]));
    // (check-sat)
    let result = bitwuzla.check_sat()?;
    println!("Expect: sat");
    println!("Bitwuzla: {result}");

    // (get-model)
    println!("(");
    println!(
        "  (define-fun {} () {} {})",
        x.symbol().unwrap_or_default(),
        x.sort(),
        bitwuzla.get_value(&x)
    );
    println!(")");

    Ok(())
}
