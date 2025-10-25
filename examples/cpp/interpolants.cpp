/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
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
  TermManager tm;

  Sort bv2 = tm.mk_bv_sort(2);
  Sort bv4 = tm.mk_bv_sort(4);
  Term x1  = tm.mk_const(bv2, "x1");
  Term x2  = tm.mk_const(bv2, "x2");
  Term x3  = tm.mk_const(bv2, "x3");
  Term a1  = tm.mk_term(Kind::BV_SLT,
                        {tm.mk_bv_zero(bv4),
                         tm.mk_term(Kind::BV_SUB,
                                    {tm.mk_term(Kind::BV_ZERO_EXTEND, {x1}, {2}),
                                     tm.mk_bv_one(bv4)})});
  Term a2  = tm.mk_term(Kind::EQUAL, {x1, x2});
  Term a3  = tm.mk_term(
      Kind::EQUAL,
      {x3,
        tm.mk_term(Kind::BV_EXTRACT,
                   {tm.mk_term(Kind::BV_NEG,
                               {tm.mk_term(Kind::BV_ZERO_EXTEND, {x2}, {2})})},
                   {1, 0})});
  Term a4 = tm.mk_term(Kind::EQUAL, {x3, tm.mk_bv_zero(bv2)});

  Options options;
  options.set(Option::PRODUCE_INTERPOLANTS, true);
  options.set(Option::INTERPOLANTS_SIMP, true);

  Bitwuzla bitwuzla(tm, options);
  bitwuzla.assert_formula(a1);
  bitwuzla.assert_formula(a2);
  bitwuzla.assert_formula(a3);
  bitwuzla.assert_formula(a4);
  bitwuzla.check_sat();

  // Query an interpolant for A /\ B with A = {a1, a2}.
  Term interpolant = bitwuzla.get_interpolant({a1, a2});
  // (not (= x2 #b00))
  std::cout << interpolant << std::endl;

  // Query an interpolation sequence for a sequence of A/B-partitions
  //     {
  //       ({a1},        {a2, a3, a4}),
  //       ({a1, a2},    {a3, a4}),
  //       ({a1, a2, a3, {a4})
  //     }
  // given as a list {{a1}, {a2}, {a3}} of increments of A.
  std::vector<Term> interpolants =
      bitwuzla.get_interpolants({{a1}, {a2}, {a3}});
  // [0]: (= ((_ extract 3 3) (bvadd (concat #b00 x1) #b1111)) #b0)
  // [1]: (not (= x2 #b00))
  // [2]: (not (= x3 #b00))
  std::cout << "(" << std::endl;
  for (const auto& itp : interpolants)
  {
    std::cout << itp << std::endl;
  }
  std::cout << ")" << std::endl;
}
