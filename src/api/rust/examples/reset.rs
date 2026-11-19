//! Port of `examples/cpp/reset.cpp`.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();
    // (set-option :produce-models false)
    options.set(Opt::ProduceModels, false)?;

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

    // (set-option :produce-models true)
    options.set(Opt::ProduceModels, true)?;

    // (reset)
    // Note: Bitwuzla does not provide an explicit API function for reset since
    //       this is achieved by simply discarding the current Bitwuzla instance
    //       and creating a new one.
    bitwuzla = Bitwuzla::new(&tm, &options)?;

    // (declare-const a ( Array (_ BitVec 2) (_ BitVec 3)))
    let sortbv2 = tm.mk_bv_sort(2);
    let a = tm.mk_const(&tm.mk_array_sort(&sortbv2, &sortbv3), "a");

    // (assert (= x #b011))
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&x, &tm.mk_bv_value_u64(&sortbv3, 3)], &[]));
    // (assert (= x (select a #b01)))
    bitwuzla.assert_formula(&tm.mk_term(
        Kind::Equal,
        &[
            &x,
            &tm.mk_term(
                Kind::ArraySelect,
                &[&a, &tm.mk_bv_value_u64(&sortbv2, 1)],
                &[],
            ),
        ],
        &[],
    ));
    // (check-sat)
    let result = bitwuzla.check_sat()?;
    println!("Expect: sat");
    println!("Bitwuzla: {result}");
    // (get-model)
    println!("(");
    for term in [&x, &a] {
        println!(
            "  (define-fun {} () {} {})",
            term.symbol().unwrap_or_default(),
            term.sort(),
            bitwuzla.get_value(term)
        );
    }
    println!(")");

    Ok(())
}
