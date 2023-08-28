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
  Result result;

  // First, create a Bitwuzla options instance.
  Options options;
  // (set-option :produce-models false)
  options.set(Option::PRODUCE_MODELS, false);

  // Then, create a Bitwuzla instance.
  std::unique_ptr<Bitwuzla> bitwuzla(new Bitwuzla(options));

  // Create a bit-vector sort of size 3.
  Sort sortbv3 = mk_bv_sort(3);

  // (declare-const x (_ BitVec 3))
  Term x = mk_const(sortbv3, "x");

  // (assert (= x #b010))
  bitwuzla->assert_formula(
      mk_term(Kind::EQUAL, {x, mk_bv_value_uint64(sortbv3, 2)}));
  // (check-sat)
  result = bitwuzla->check_sat();
  std::cout << "Expect: sat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;

  // (set-option :produce-models true)
  options.set(Option::PRODUCE_MODELS, true);

  // (reset)
  // Note: Bitwuzla does not provide an explicit API function for reset since
  //       this is achieved by simply discarding the current Bitwuzla instance
  //       and creating a new one.
  bitwuzla.reset(new Bitwuzla(options));

  // (declare-const a ( Array (_ BitVec 2) (_ BitVec 3)))
  Sort sortbv2 = mk_bv_sort(2);
  Term a       = mk_const(mk_array_sort(sortbv2, sortbv3), "a");

  // (assert (= x #b011))
  bitwuzla->assert_formula(
      mk_term(Kind::EQUAL, {x, mk_bv_value_uint64(sortbv3, 3)}));
  // (assert (= x (select a #b01)))
  bitwuzla->assert_formula(mk_term(
      Kind::EQUAL,
      {x, mk_term(Kind::ARRAY_SELECT, {a, mk_bv_value_uint64(sortbv2, 1)})}));
  // (check-sat)
  result = bitwuzla->check_sat();
  std::cout << "Expect: sat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;
  // (get-model)
  std::cout << "(" << std::endl
            << "  (define-fun " << x.symbol()->get() << " () " << x.sort()
            << " " << bitwuzla->get_value(x) << ")" << std::endl
            << "  (define-fun " << a.symbol()->get() << " () " << a.sort()
            << " " << bitwuzla->get_value(a) << ")" << std::endl
            << ")" << std::endl;

  return 0;
}
