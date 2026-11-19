//! Printing and Statistics (test_api.cpp: Printing, Statistics).
//!
//! The `set_bv_format` stream manipulator corresponds to the `base` argument
//! of `print_formula`. Not ported, the C API has no equivalent: disabling
//! letification via the `set_letify` stream manipulator (second half of
//! `print_formula5`). The standard output the C++ tests capture is written
//! to a parser output file instead.

use bitwuzla::{Bitwuzla, Kind, Options, Parser, RoundingMode};

use crate::common::{Fixture, read_and_remove, temp_path};

#[test]
fn print_set_bv_format() {
    let f = Fixture::new();
    let bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    assert_err!(bitwuzla.print_formula("smt2", 23));
}

#[test]
fn print_formula() {
    let f = Fixture::new();
    let options = Options::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();

    assert_err!(bitwuzla.print_formula("", 2));
    assert_err!(bitwuzla.print_formula("asdf", 2));

    bitwuzla.assert_formula(&f.bool_const);
    bitwuzla.assert_formula(&f.mk(
        Kind::Equal,
        &[&f.mk(Kind::Apply, &[&f.lambda, &f.bv_const8]), &f.bv_zero8],
    ));
    {
        let expected_smt2 = "(set-logic QF_UFBV)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             #b00000000))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
    }
    {
        let expected_smt2 = "(set-logic QF_UFBV)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             (_ bv0 8)))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 10).unwrap(), expected_smt2);
    }
    {
        let expected_smt2 = "(set-logic QF_UFBV)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             #x00))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 16).unwrap(), expected_smt2);
    }

    bitwuzla.assert_formula(&f.exists);
    {
        let expected_smt2 = "(set-logic UFBV)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             #b00000000))\n\
                             (assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
    }
    {
        let expected_smt2 = "(set-logic UFBV)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             (_ bv0 8)))\n\
                             (assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q))))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 10).unwrap(), expected_smt2);
    }
    {
        let expected_smt2 = "(set-logic UFBV)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             #x00))\n\
                             (assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q))))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 16).unwrap(), expected_smt2);
    }

    bitwuzla.assert_formula(&f.mk(
        Kind::FpLeq,
        &[
            &f.mk(
                Kind::Apply,
                &[
                    &f.fun_fp,
                    &f.bv_const8,
                    &f.fp_const16,
                    &f.mk_idx(Kind::BvZeroExtend, &[&f.bv_ones23], &[9]),
                ],
            ),
            &f.fp_const16,
        ],
    ));

    {
        let expected_smt2 = "(set-logic UFBVFP)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (declare-const fp16 (_ FloatingPoint 5 11))\n\
                             (declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec \
                             32)) (_ FloatingPoint 5 11))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             #b00000000))\n\
                             (assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))\n\
                             (assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) \
                             #b11111111111111111111111)) fp16))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
    }
    {
        let expected_smt2 = "(set-logic UFBVFP)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (declare-const fp16 (_ FloatingPoint 5 11))\n\
                             (declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec \
                             32)) (_ FloatingPoint 5 11))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             (_ bv0 8)))\n\
                             (assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q))))\n\
                             (assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) \
                             (_ bv8388607 23))) fp16))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 10).unwrap(), expected_smt2);
    }
    {
        let expected_smt2 = "(set-logic UFBVFP)\n\
                             (declare-const b Bool)\n\
                             (declare-const bv8 (_ BitVec 8))\n\
                             (declare-const fp16 (_ FloatingPoint 5 11))\n\
                             (declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec \
                             32)) (_ FloatingPoint 5 11))\n\
                             (assert b)\n\
                             (assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) \
                             #x00))\n\
                             (assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q))))\n\
                             (assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) \
                             #b11111111111111111111111)) fp16))\n\
                             (check-sat)\n\
                             (exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 16).unwrap(), expected_smt2);
    }
}

#[test]
fn print_formula2() {
    let f = Fixture::new();
    let options = Options::new();
    let bv1 = f.tm.mk_bv_sort(1);
    let ar1_1 = f.tm.mk_array_sort(&bv1, &bv1);
    let a = f.tm.mk_const(&ar1_1, "a");
    let b = f.tm.mk_const(&ar1_1, "b");
    let z = f.tm.mk_bv_zero(&bv1);
    let e = f.mk(Kind::ArraySelect, &[&a, &z]);
    let c = f.mk(Kind::Equal, &[&a, &b]);
    let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
    bitwuzla.assert_formula(&f.mk(Kind::Equal, &[&e, &z]));
    bitwuzla.assert_formula(&c);
    bitwuzla.assert_formula(&f.exists);

    let expected_smt2 = "(set-logic ABV)\n\
                         (declare-const bv8 (_ BitVec 8))\n\
                         (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))\n\
                         (declare-const b (Array (_ BitVec 1) (_ BitVec 1)))\n\
                         (assert (= (select a #b0) #b0))\n\
                         (assert (= a b))\n\
                         (assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))\n\
                         (check-sat)\n\
                         (exit)\n";
    assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
}

#[test]
fn print_formula3() {
    let f = Fixture::new();
    let options = Options::new();
    let bv32 = f.tm.mk_bv_sort(32);
    let n = f.tm.mk_const(&bv32, "n");
    let sim = f.tm.mk_const(&bv32, "~");
    let zero = f.tm.mk_bv_zero(&bv32);
    let two = f.tm.mk_bv_value_u64(&bv32, 2);
    let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
    bitwuzla.assert_formula(&f.mk(Kind::Distinct, &[&zero, &f.mk(Kind::BvAdd, &[&n, &sim])]));
    bitwuzla.push(1);
    bitwuzla.assert_formula(&f.mk(
        Kind::Equal,
        &[
            &f.mk(Kind::BvAdd, &[&n, &two]),
            &f.mk(
                Kind::BvNeg,
                &[&f.mk(Kind::BvAdd, &[&sim, &f.mk(Kind::BvMul, &[&n, &two])])],
            ),
        ],
    ));
    bitwuzla.push(1);
    bitwuzla.assert_formula(&f.mk(
        Kind::Equal,
        &[&zero, &f.mk(Kind::BvAdd, &[&n, &f.tm.mk_bv_one(&bv32)])],
    ));

    let expected_smt2 = "(set-logic QF_BV)\n\
                         (declare-const n (_ BitVec 32))\n\
                         (declare-const ~ (_ BitVec 32))\n\
                         (assert (distinct #b00000000000000000000000000000000 (bvadd n ~)))\n\
                         (push 1)\n\
                         (assert (= (bvadd n #b00000000000000000000000000000010) (bvneg \
                         (bvadd ~ (bvmul n \
                         #b00000000000000000000000000000010)))))\n\
                         (push 1)\n\
                         (assert (= #b00000000000000000000000000000000 (bvadd n \
                         #b00000000000000000000000000000001)))\n\
                         (check-sat)\n\
                         (exit)\n";
    assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
}

#[test]
fn print_formula4() {
    let f = Fixture::new();
    let options = Options::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
    let main_a = f.tm.mk_const(&f.tm.mk_bool_sort(), "main a");
    let pain_b = f.tm.mk_const(&f.tm.mk_bool_sort(), "|pain b|");
    let b = f.tm.mk_const(&f.tm.mk_bool_sort(), "b");
    let e = f.tm.mk_const(&f.tm.mk_bool_sort(), "");
    bitwuzla.assert_formula(&f.mk(Kind::Xor, &[&main_a, &pain_b, &b, &e]));
    let expected_smt2 = "(set-logic ALL)\n\
                         (declare-const |main a| Bool)\n\
                         (declare-const |pain b| Bool)\n\
                         (declare-const b Bool)\n\
                         (declare-const || Bool)\n\
                         (assert (xor (xor (xor |main a| |pain b|) b) ||))\n\
                         (check-sat)\n\
                         (exit)\n";
    assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
    for symbol in ["|c", "|c\\|", "|c||"] {
        let i = f.tm.mk_const(&f.tm.mk_bool_sort(), symbol);
        let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
        bitwuzla.assert_formula(&i);
        assert_err!(bitwuzla.print_formula("smt2", 2));
    }
}

#[test]
fn print_formula5() {
    let f = Fixture::new();
    let options = Options::new();
    let smt2 = "(declare-const _x0 Bool)\n\
                (assert (let ((_let0 (exists ((_x1 Bool)) (ite (= (distinct (ite \
                false _x1 _x0) _x1 _x0) _x0) (= (distinct (ite false _x1 _x0) _x1 \
                _x0) _x0) (distinct (ite false _x1 _x0) _x1 _x0)))))(ite _let0 \
                _let0 _x0)))\n";

    let mut parser = Parser::new(&f.tm, &options, "smt2", 2, "<stdout>").unwrap();
    parser.configure_parse_only(true);
    parser.parse_str(smt2).unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();

    {
        let expected_smt2 = "(set-logic ALL)\n(declare-const _x0 Bool)\n(define-const @def0 \
                             Bool (exists ((_x1 Bool)) (let ((_let0 (distinct (ite false _x1 \
                             _x0) _x1 _x0))) (let ((_let1 (= _let0 _x0))) (ite _let1 _let1 \
                             _let0)))))\n(assert (ite @def0 @def0 _x0))\n(check-sat)\n(exit)\n";
        assert_eq!(bitwuzla.print_formula("smt2", 2).unwrap(), expected_smt2);
    }
}

#[test]
fn print_fp_to_sbv_to_ubv() {
    let f = Fixture::new();
    let sort = f.tm.mk_fp_sort(8, 24);
    let rm = f.tm.mk_rm_value(RoundingMode::Rne);
    let fp = f.tm.mk_fp_from_real(&sort, &rm, "1").unwrap();
    let options = Options::new();
    let mut parser = Parser::new(&f.tm, &options, "smt2", 2, "<stdout>").unwrap();
    {
        let t1 = f.mk_idx(Kind::FpToSbv, &[&rm, &fp], &[32]);
        let t2 = parser.parse_term(&t1.to_string()).unwrap();
        assert_eq!(t1, t2);
    }
    {
        let t1 = f.mk_idx(Kind::FpToUbv, &[&rm, &fp], &[32]);
        let t2 = parser.parse_term(&t1.to_string()).unwrap();
        assert_eq!(t1, t2);
    }
}

#[test]
fn print_unicode() {
    let f = Fixture::new();
    let x = f.tm.mk_const(&f.tm.mk_bool_sort(), "|ꯍ|");
    let mut bitwuzla = Bitwuzla::new(&f.tm, &Options::new()).unwrap();
    bitwuzla.assert_formula(&x);
    print!("{}", bitwuzla.print_formula("smt2", 2).unwrap());
}

#[test]
fn print_shadow_let() {
    let f = Fixture::new();
    let options = Options::new();

    // Parse `input` (not parse-only) and return what the parser printed.
    let parse_and_solve = |input: &str| {
        let outfile = temp_path("print_shadow_let.out");
        {
            let mut parser =
                Parser::new(&f.tm, &options, "smt2", 2, outfile.to_str().unwrap()).unwrap();
            parser.parse_str(input).unwrap();
        }
        read_and_remove(&outfile)
    };

    // Parse, print and check that reparsing the printed output. Generated let
    // symbols must never shadow declared consts or bound variables occurring in
    // the formula, and must never shadow each other across nested lets.
    let test = |smt2: &str, expected: &str| {
        assert_eq!(parse_and_solve(smt2), "sat\n");
        let printed = {
            let mut parser = Parser::new(&f.tm, &options, "smt2", 2, "<stdout>").unwrap();
            parser.configure_parse_only(true);
            parser.parse_str(smt2).unwrap();
            parser.bitwuzla().unwrap().print_formula("smt2", 2).unwrap()
        };
        assert_eq!(printed, expected);
        assert_eq!(parse_and_solve(&printed), "sat\n");
    };

    // A generated let symbol must not capture a declared const `_let0` that is
    // shared inside a quantifier: the shared `(bvadd y y)` is bound to `_let1`.
    test(
        "(declare-const _let0 (_ BitVec 2)) (assert (= _let0 #b01)) (assert \
         (forall ((y (_ BitVec 2))) (=> (bvult (bvadd y y) (bvnot (bvadd y y))) \
         (= _let0 #b01)))) (check-sat)",
        "(set-logic BV)\n\
         (declare-const _let0 (_ BitVec 2))\n\
         (assert (= _let0 #b01))\n\
         (assert (forall ((y (_ BitVec 2))) (let ((_let1 (bvadd y y))) (=> \
         (bvult _let1 (bvnot _let1)) (= _let0 #b01)))))\n\
         (check-sat)\n(exit)\n",
    );

    // A generated let symbol must not capture a bound variable named `_let0`:
    // the shared `(g _let0)` is bound to `_let1`, not `_let0`.
    test(
        "(set-logic UFBV) (declare-fun g ((_ BitVec 2)) (_ BitVec 2)) \
         (declare-fun f ((_ BitVec 2) (_ BitVec 2)) (_ BitVec 2)) (assert \
         (forall ((_let0 (_ BitVec 2))) (= _let0 (f (g _let0) (g _let0))))) \
         (check-sat)",
        "(set-logic UFBV)\n\
         (declare-fun g ((_ BitVec 2)) (_ BitVec 2))\n\
         (declare-fun f ((_ BitVec 2) (_ BitVec 2)) (_ BitVec 2))\n\
         (assert (forall ((_let0 (_ BitVec 2))) (let ((_let1 (g _let0))) (= \
         _let0 (f _let1 _let1)))))\n\
         (check-sat)\n(exit)\n",
    );

    // Nested lets must not reuse a let symbol even when an outer let symbol was
    // bumped past a declared const `_let0`: the outer lets are `_let1`/`_let2`
    // and the nested let continues with a fresh `_let3` (rather than reusing
    // `_let2`, which would capture the outer `(bvnot (g1 _let0))`).
    test(
        "(set-logic UFBV) (declare-const _let0 (_ BitVec 4)) \
         (declare-fun g0 ((_ BitVec 4)) (_ BitVec 4)) \
         (declare-fun g1 ((_ BitVec 4)) (_ BitVec 4)) \
         (declare-fun h ((_ BitVec 4)) (_ BitVec 4)) \
         (declare-fun f ((_ BitVec 4) (_ BitVec 4)) (_ BitVec 4)) \
         (assert (or (not (= (f (bvnot (g0 _let0)) (bvnot (g0 _let0))) \
         (f (bvnot (g1 _let0)) (bvnot (g1 _let0))))) \
         (forall ((w (_ BitVec 4))) \
         (= (bvnot (g1 _let0)) (f (bvnot (h w)) (bvnot (h w))))))) (check-sat)",
        "(set-logic UFBV)\n\
         (declare-const _let0 (_ BitVec 4))\n\
         (declare-fun g0 ((_ BitVec 4)) (_ BitVec 4))\n\
         (declare-fun g1 ((_ BitVec 4)) (_ BitVec 4))\n\
         (declare-fun h ((_ BitVec 4)) (_ BitVec 4))\n\
         (declare-fun f ((_ BitVec 4) (_ BitVec 4)) (_ BitVec 4))\n\
         (assert (let ((_let1 (bvnot (g0 _let0)))) (let ((_let2 (bvnot (g1 \
         _let0)))) (or (not (= (f _let1 _let1) (f _let2 _let2))) (forall ((w (_ \
         BitVec 4))) (let ((_let3 (bvnot (h w)))) (= _let2 (f _let3 _let3))))))))\
         \n\
         (check-sat)\n(exit)\n",
    );
}

#[test]
fn statistics() {
    let f = Fixture::new();
    let options = Options::new();
    let mut bitwuzla = Bitwuzla::new(&f.tm, &options).unwrap();
    bitwuzla.assert_formula(&f.bool_const);
    let stats = bitwuzla.statistics();
    for (name, val) in &stats {
        println!("{name}: {val}");
    }
}
