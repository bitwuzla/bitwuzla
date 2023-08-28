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

using namespace bitwuzla;

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;
  // Then, enable unsat core extraction.
  // Note: Unsat core extraction is disabled by default.
  options.set(Option::PRODUCE_UNSAT_CORES, true);
  // Then, create a Bitwuzla instance.
  Bitwuzla bitwuzla(options);

  // Create a bit-vector sort of size 2.
  Sort sortbv2 = mk_bv_sort(2);
  // Create a bit-vector sort of size 4.
  Sort sortbv4 = mk_bv_sort(4);
  // Create Float16 floatinf-point sort.
  Sort sortfp16 = mk_fp_sort(5, 11);

  // Create bit-vector variables.
  // (declare-const x0 (_ BitVec 4))
  Term x0 = mk_const(sortbv4, "x0");
  // (declare-const x1 (_ BitVec 2))
  Term x1 = mk_const(sortbv2, "x1");
  // (declare-const x2 (_ BitVec 2))
  Term x2 = mk_const(sortbv2, "x2");
  // (declare-const x3 (_ BitVec 2))
  Term x3 = mk_const(sortbv2, "x3");
  // (declare-const x4 Float16)
  Term x4 = mk_const(sortfp16, "x4");

  // Create FP positive zero.
  Term fpzero = mk_fp_pos_zero(sortfp16);
  // Create BV zero of size 4.
  Term bvzero = mk_bv_zero(sortbv4);

  // (define-fun f0 ((a Float16)) Bool (fp.gt a (_ +zero 5 11)))
  Term a_f0 = mk_var(sortfp16, "a_f0");
  Term f0 = mk_term(Kind::LAMBDA, {a_f0, mk_term(Kind::FP_GT, {a_f0, fpzero})});

  // (define-fun f1 ((a Float16)) (_ BitVec 4) (ite (f0 a) x0 #b0000))
  Term a_f1 = mk_var(sortfp16, "a_f1");
  Term f1   = mk_term(
      Kind::LAMBDA,
      {a_f1,
         mk_term(Kind::ITE, {mk_term(Kind::APPLY, {f0, a_f1}), x0, bvzero})});

  // (define-fun f2 ((a Float16)) (_ BitVec 2) ((_ extract 1 0) (f1 a)))
  Term a_f2 = mk_var(sortfp16, "a_f2");
  Term f2   = mk_term(
      Kind::LAMBDA,
      {a_f2,
         mk_term(Kind::BV_EXTRACT, {mk_term(Kind::APPLY, {f1, a_f2})}, {1, 0})});

  // (assert (! (bvult x2 (f2 (_ +zero 5 11))) :named a0))
  Term a0 = mk_term(Kind::BV_ULT, {x2, mk_term(Kind::APPLY, {f2, fpzero})});
  bitwuzla.assert_formula(a0);

  // (assert (! (= x1 x2 x3) :named a1))
  Term a1 = mk_term(Kind::EQUAL, {x1, x2, x3});
  bitwuzla.assert_formula(a1);

  // (assert (!(= x4 ((_ to_fp_unsigned 5 11) RNE x3)) :named a2))
  Term a2 = mk_term(Kind::EQUAL,
                    {x4,
                     mk_term(Kind::FP_TO_FP_FROM_UBV,
                             {mk_rm_value(RoundingMode::RNE), x3},
                             {5, 11})});
  bitwuzla.assert_formula(a2);

  // (check-sat)
  Result result = bitwuzla.check_sat();
  std::cout << "Expect: unsat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;

  // (get-unsat-core)
  auto unsat_core = bitwuzla.get_unsat_core();
  std::cout << "Unsat Core:" << std::endl << "{" << std::endl;
  for (const auto& t : unsat_core)
  {
    std::cout << " " << t << std::endl;
  }
  std::cout << "}" << std::endl;

  return 0;
}
