/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/cpp/bitwuzla.h>

#include <cassert>
#include <iostream>
#include <sstream>

using namespace bitwuzla;

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;
  // Then, create a Bitwuzla instance.
  Bitwuzla bitwuzla(options);
  // Create some sorts.
  Sort bv8  = mk_bv_sort(8);
  Sort bv32 = mk_bv_sort(32);
  Sort fp16 = mk_fp_sort(5, 11);
  // Create terms.
  Term b      = mk_const(mk_bool_sort(), "b");
  Term bv     = mk_const(bv8, "bv");
  Term fp     = mk_const(fp16, "fp");
  Term fun    = mk_const(mk_fun_sort({bv8, fp16, bv32}, fp16), "fun");
  Term zero   = mk_bv_zero(bv8);
  Term ones   = mk_bv_ones(mk_bv_sort(23));
  Term z      = mk_var(bv8, "z");
  Term q      = mk_var(bv8, "q");
  Term lambda = mk_term(Kind::LAMBDA, {z, mk_term(Kind::BV_ADD, {z, bv})});
  Term fpleq  = mk_term(
      Kind::FP_LEQ,
      {mk_term(Kind::APPLY,
                {fun, bv, fp, mk_term(Kind::BV_ZERO_EXTEND, {ones}, {9})}),
        fp});
  Term exists = mk_term(
      Kind::EXISTS,
      {q, mk_term(Kind::EQUAL, {zero, mk_term(Kind::BV_MUL, {bv, q})})});
  // Assert formulas.
  bitwuzla.assert_formula(b);
  bitwuzla.assert_formula(
      mk_term(Kind::EQUAL, {mk_term(Kind::APPLY, {lambda, bv}), zero}));
  bitwuzla.assert_formula(exists);
  bitwuzla.assert_formula(fpleq);

  // Print sort.
  std::cout << "Print bit-vector sort of size 32:" << std::endl;
  std::cout << "---------------------------------" << std::endl;
  std::cout << "operator<<: " << bv32 << std::endl;
  std::cout << "str():      " << bv32.str() << std::endl << std::endl;
  ;

  // Print terms.
  // Note: Term::str() uses the binary bv output format (not configurable).
  std::cout << "Print term [default (binary) bv output format]:" << std::endl;
  std::cout << "-----------------------------------------------" << std::endl;
  std::cout << "operator<<: " << fpleq << std::endl;
  std::cout << "str():      " << fpleq.str() << std::endl << std::endl;

  std::cout << "Print term [hexadecimal bv output format]:" << std::endl;
  std::cout << "------------------------------------------" << std::endl;
  std::cout << set_bv_format(16);
  std::cout << "operator<<: " << fpleq << std::endl;
  std::cout << "str():      " << fpleq.str() << std::endl << std::endl;

  std::cout << "Print term [decimal bv output format]:" << std::endl;
  std::cout << "--------------------------------------" << std::endl;
  std::cout << set_bv_format(10);
  std::cout << "operator<<: " << fpleq << std::endl;
  std::cout << "str():      " << fpleq.str() << std::endl << std::endl;

  // Print asserted formulas.
  // Note: This uses the default bit-vector output format (binary).
  {
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic UFBVFP)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv (_ BitVec 8))" << std::endl
        << "(declare-const fp (_ FloatingPoint 5 11))" << std::endl
        << "(declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec "
           "32)) (_ FloatingPoint 5 11))"
        << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) "
           "#b00000000))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv q))))"
        << std::endl
        << "(assert (fp.leq (fun bv fp ((_ zero_extend 9) "
           "#b11111111111111111111111)) fp))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    std::stringstream ss;
    bitwuzla.print_formula(ss, "smt2");
    assert(ss.str() == expected_smt2.str());
    std::cout << "Print formula [default (binary) bv output format]:"
              << std::endl;
    std::cout << "--------------------------------------------------"
              << std::endl;
    std::cout << ss.str() << std::endl;
  }

  // Print asserted formulas using hexadecimal bit-vector output format.
  {
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic UFBVFP)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv (_ BitVec 8))" << std::endl
        << "(declare-const fp (_ FloatingPoint 5 11))" << std::endl
        << "(declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec "
           "32)) (_ FloatingPoint 5 11))"
        << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) "
           "#x0))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= #x0 (bvmul bv q))))"
        << std::endl
        << "(assert (fp.leq (fun bv fp ((_ zero_extend 9) "
           "#x7fffff)) fp))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    std::stringstream ss;
    // configure output stream with hexadecimal bv output format
    ss << set_bv_format(16);
    bitwuzla.print_formula(ss, "smt2");
    assert(ss.str() == expected_smt2.str());
    std::cout << "Print formula [hexadecimal bv output format]:" << std::endl;
    std::cout << "---------------------------------------------" << std::endl;
    std::cout << ss.str() << std::endl;
  }

  // Print asserted formulas using decimal bit-vector output format.
  {
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic UFBVFP)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv (_ BitVec 8))" << std::endl
        << "(declare-const fp (_ FloatingPoint 5 11))" << std::endl
        << "(declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec "
           "32)) (_ FloatingPoint 5 11))"
        << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) "
           "(_ bv0 8)))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv q))))"
        << std::endl
        << "(assert (fp.leq (fun bv fp ((_ zero_extend 9) "
           "(_ bv8388607 23))) fp))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    std::stringstream ss;
    // configure output stream with decimal bv output format
    ss << set_bv_format(10);
    bitwuzla.print_formula(ss, "smt2");
    assert(ss.str() == expected_smt2.str());
    std::cout << "Print formula [decimal bv output format]:" << std::endl;
    std::cout << "---------------------------------------------" << std::endl;
    std::cout << ss.str() << std::endl;
  }
  return 0;
}
