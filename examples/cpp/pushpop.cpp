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

#include <iostream>

using namespace bitwuzla;

int
main()
{
  // First, create a term manager instance.
  TermManager tm;
  // Create a Bitwuzla options instance.
  Options options;
  // Then, create a Bitwuzla instance.
  Bitwuzla bitwuzla(tm, options);

  // Create a bit-vector sort of size 1.
  Sort sortbv1 = tm.mk_bv_sort(1);
  // Create a bit-vector sort of size 2.
  Sort sortbv2 = tm.mk_bv_sort(2);

  // Create bit-vector variables.
  // (declare-const o0 (_ BitVec 1))
  Term o0 = tm.mk_const(sortbv1, "o0");
  // (declare-const o1 (_ BitVec 1))
  Term o1 = tm.mk_const(sortbv1, "o1");
  // (declare-const s0 (_ BitVec 2))
  Term s0 = tm.mk_const(sortbv2, "s0");
  // (declare-const s1 (_ BitVec 2))
  Term s1 = tm.mk_const(sortbv2, "s1");
  // (declare-const s2 (_ BitVec 2))
  Term s2 = tm.mk_const(sortbv2, "s2");
  // (declare-const goal (_ BitVec 2))
  Term goal = tm.mk_const(sortbv2, "goal");

  // Create bit-vector values zero, one, three.
  Term zero  = tm.mk_bv_zero(sortbv2);
  Term one1  = tm.mk_bv_one(sortbv1);
  Term one2  = tm.mk_bv_one(sortbv2);
  Term three = tm.mk_bv_value_uint64(sortbv2, 3);

  // Add some assertions.
  bitwuzla.assert_formula(tm.mk_term(Kind::EQUAL, {s0, zero}));
  bitwuzla.assert_formula(tm.mk_term(Kind::EQUAL, {goal, three}));

  // Push, assert, check sat and pop.
  bitwuzla.push(1);
  bitwuzla.assert_formula(tm.mk_term(Kind::EQUAL, {s0, goal}));
  Result result = bitwuzla.check_sat();
  std::cout << "Expect: unsat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;
  bitwuzla.pop(1);

  // (assert (= s1 (ite (= o0 (_ sortbv1 1)) (bvadd s0 one) s0)))
  bitwuzla.assert_formula(
      tm.mk_term(Kind::EQUAL,
                 {s1,
                  tm.mk_term(Kind::ITE,
                             {tm.mk_term(Kind::EQUAL, {o0, one1}),
                              tm.mk_term(Kind::BV_ADD, {s0, one2}),
                              s0})}));

  // Push, assert, check sat and pop.
  bitwuzla.push(1);
  bitwuzla.assert_formula(tm.mk_term(Kind::EQUAL, {s1, goal}));
  result = bitwuzla.check_sat();
  std::cout << "Expect: unsat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;
  bitwuzla.pop(1);

  // (assert (= s2 (ite (= o1 (_ sortbv1 1)) (bvadd s1 one) s1)))
  bitwuzla.assert_formula(
      tm.mk_term(Kind::EQUAL,
                 {s2,
                  tm.mk_term(Kind::ITE,
                             {tm.mk_term(Kind::EQUAL, {o1, one1}),
                              tm.mk_term(Kind::BV_ADD, {s1, one2}),
                              s1})}));

  // Push, assert, check sat and pop.
  bitwuzla.push(1);
  bitwuzla.assert_formula(tm.mk_term(Kind::EQUAL, {s2, goal}));
  result = bitwuzla.check_sat();
  std::cout << "Expect: unsat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;
  bitwuzla.pop(1);

  return 0;
}
