//! Port of `examples/cpp/print.cpp`.
//!
//! The C++ API configures the bit-vector output format of a stream via
//! `set_bv_format`, the Rust API takes it as a `base` argument instead
//! (`Term::to_string_fmt`, `Bitwuzla::print_formula`). `Display` uses binary.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();
    options.set(Opt::ProduceModels, true)?;
    // Then, create a Bitwuzla instance.
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;
    // Create some sorts.
    let bv8 = tm.mk_bv_sort(8);
    let bv32 = tm.mk_bv_sort(32);
    let fp16 = tm.mk_fp_sort(5, 11);
    // Create terms.
    let b = tm.mk_const(&tm.mk_bool_sort(), "b");
    let bv = tm.mk_const(&bv8, "bv");
    let fp = tm.mk_const(&fp16, "fp");
    let rm = tm.mk_const(&tm.mk_rm_sort(), "rm");
    let fun = tm.mk_const(&tm.mk_fun_sort(&[&bv8, &fp16, &bv32], &fp16), "fun");
    let zero = tm.mk_bv_zero(&bv8);
    let ones = tm.mk_bv_ones(&tm.mk_bv_sort(23));
    let z = tm.mk_var(&bv8, "z");
    let q = tm.mk_var(&bv8, "q");
    let lambda = tm.mk_term(
        Kind::Lambda,
        &[&z, &tm.mk_term(Kind::BvAdd, &[&z, &bv], &[])],
        &[],
    );
    let fpleq = tm.mk_term(
        Kind::FpLeq,
        &[
            &tm.mk_term(
                Kind::Apply,
                &[
                    &fun,
                    &bv,
                    &fp,
                    &tm.mk_term(Kind::BvZeroExtend, &[&ones], &[9]),
                ],
                &[],
            ),
            &fp,
        ],
        &[],
    );
    let exists = tm.mk_term(
        Kind::Exists,
        &[
            &q,
            &tm.mk_term(
                Kind::Equal,
                &[&zero, &tm.mk_term(Kind::BvMul, &[&bv, &q], &[])],
                &[],
            ),
        ],
        &[],
    );
    // Assert formulas.
    bitwuzla.assert_formula(&b);
    bitwuzla.assert_formula(&tm.mk_term(
        Kind::Equal,
        &[&tm.mk_term(Kind::Apply, &[&lambda, &bv], &[]), &zero],
        &[],
    ));
    bitwuzla.assert_formula(&exists);
    bitwuzla.assert_formula(&fpleq);

    // Print sort.
    println!("Print bit-vector sort of size 32:");
    println!("---------------------------------");
    let bv32_str = bv32.to_string();
    println!("Display:     {bv32}");
    println!("to_string(): {bv32_str}");
    println!();

    // Print terms.
    // Note: Hexadecimal bv output format is ignored if the value is not of size
    //       divisible by 4.
    println!("Print term:");
    println!("-----------");
    println!("Display           [bin]:           {rm}");
    println!(
        "to_string_fmt(10) [dec (ignored)]: {}",
        rm.to_string_fmt(10)
    );
    println!(
        "to_string_fmt(16) [hex (ignored)]: {}",
        rm.to_string_fmt(16)
    );
    println!();
    println!("Display           [bin]: {zero}");
    println!("to_string_fmt(10) [dec]: {}", zero.to_string_fmt(10));
    println!("to_string_fmt(16) [hex]: {}", zero.to_string_fmt(16));
    println!();
    println!("Display           [bin]:           {fpleq}");
    println!(
        "to_string_fmt(10) [dec]:           {}",
        fpleq.to_string_fmt(10)
    );
    println!(
        "to_string_fmt(16) [hex (ignored)]: {}",
        fpleq.to_string_fmt(16)
    );
    println!();

    // Print asserted formulas.
    // Note: This uses the binary bit-vector output format.
    {
        let expected_smt2 = "(set-logic UFBVFP)\n\
             (declare-const b Bool)\n\
             (declare-const bv (_ BitVec 8))\n\
             (declare-const fp (_ FloatingPoint 5 11))\n\
             (declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec 32)) \
             (_ FloatingPoint 5 11))\n\
             (assert b)\n\
             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) #b00000000))\n\
             (assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv q))))\n\
             (assert (fp.leq (fun bv fp ((_ zero_extend 9) #b11111111111111111111111)) fp))\n\
             (check-sat)\n\
             (exit)\n";
        let s = bitwuzla.print_formula("smt2", 2)?;
        assert_eq!(s, expected_smt2);
        println!("Print formula [binary bv output format]:");
        println!("----------------------------------------");
        println!("{s}");
    }

    // Print asserted formulas using hexadecimal bit-vector output format.
    {
        let expected_smt2 = "(set-logic UFBVFP)\n\
             (declare-const b Bool)\n\
             (declare-const bv (_ BitVec 8))\n\
             (declare-const fp (_ FloatingPoint 5 11))\n\
             (declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec 32)) \
             (_ FloatingPoint 5 11))\n\
             (assert b)\n\
             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) #x00))\n\
             (assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv q))))\n\
             (assert (fp.leq (fun bv fp ((_ zero_extend 9) #b11111111111111111111111)) fp))\n\
             (check-sat)\n\
             (exit)\n";
        let s = bitwuzla.print_formula("smt2", 16)?;
        assert_eq!(s, expected_smt2);
        println!("Print formula [hexadecimal bv output format]:");
        println!("---------------------------------------------");
        println!("{s}");
    }

    // Print asserted formulas using decimal bit-vector output format.
    {
        let expected_smt2 = "(set-logic UFBVFP)\n\
             (declare-const b Bool)\n\
             (declare-const bv (_ BitVec 8))\n\
             (declare-const fp (_ FloatingPoint 5 11))\n\
             (declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec 32)) \
             (_ FloatingPoint 5 11))\n\
             (assert b)\n\
             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) (_ bv0 8)))\n\
             (assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv q))))\n\
             (assert (fp.leq (fun bv fp ((_ zero_extend 9) (_ bv8388607 23))) fp))\n\
             (check-sat)\n\
             (exit)\n";
        let s = bitwuzla.print_formula("smt2", 10)?;
        assert_eq!(s, expected_smt2);
        println!("Print formula [decimal bv output format]:");
        println!("---------------------------------------------");
        println!("{s}");
    }

    bitwuzla.check_sat()?;

    // Print values.
    println!("Print value of Boolean predicate:");
    println!("---------------------------------");
    let fpleq_val = bitwuzla.get_value(&fpleq).value_bool();
    let fpleq_val_str = bitwuzla.get_value(&fpleq).value_str(2);
    println!("{fpleq}: {fpleq_val:>5} [bool]");
    println!("{fpleq}: {fpleq_val_str:>5} [String]");
    println!();

    println!("Print value of bv const:");
    println!("------------------------");
    let bv_val = bitwuzla.get_value(&bv);
    println!("{bv}: {:>8} [String] (bin)", bv_val.value_str(2));
    println!("{bv}: {:>8} [String] (dec)", bv_val.value_str(10));
    println!("{bv}: {:>8} [String] (hex)", bv_val.value_str(16));
    println!();

    println!("Print value of RoundingMode const:");
    println!("----------------------------------");
    let rm_val = bitwuzla.get_value(&rm).value_rm();
    let rm_val_str = bitwuzla.get_value(&rm).value_str(2);
    println!("{rm}: {rm_val} [RoundingMode]");
    println!("{rm}: {rm_val_str} [String]");
    println!();

    let fp_val = bitwuzla.get_value(&fp);

    println!("Print value of fp const as String (base ignored):");
    println!("-------------------------------------------------");
    assert_eq!(fp_val.value_str(2), fp_val.value_str(10));
    assert_eq!(fp_val.value_str(2), fp_val.value_str(16));
    println!("{fp}: {:>16} [String] (bin)", fp_val.value_str(2));
    println!(
        "{fp}: {:>16} [String] (dec [ignored])",
        fp_val.value_str(10)
    );
    println!(
        "{fp}: {:>16} [String] (hex [ignored])",
        fp_val.value_str(16)
    );
    println!();

    println!("Print value of fp const as tuple of String:");
    println!("-------------------------------------------");
    for (base, name) in [(2, "bin"), (10, "dec"), (16, "hex")] {
        let (sign, exp, sig) = fp_val.value_fp_ieee(base);
        println!("{fp}: ({sign}, {exp:>5}, {sig:>11}) [(String, String, String)] ({name})");
    }

    Ok(())
}
