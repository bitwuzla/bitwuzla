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

#include <chrono>
#include <iostream>

using namespace bitwuzla;
using namespace std::chrono;

class TestTerminator : public Terminator
{
 public:
  TestTerminator(uint32_t time_limit_ms)
      : Terminator(),
        time_limit_ms(time_limit_ms),
        start(high_resolution_clock::now())
  {
  }
  bool terminate() override
  {
    if (duration_cast<milliseconds>(high_resolution_clock::now() - start)
            .count()
        >= time_limit_ms)
    {
      return true;
    }
    return false;
  }
  uint32_t time_limit_ms = 0;
  high_resolution_clock::time_point start;
};

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;
  // Then, create a Bitwuzla instance.
  Bitwuzla bitwuzla(options);

  Sort bv = mk_bv_sort(32);

  Term x = mk_const(bv);
  Term s = mk_const(bv);
  Term t = mk_const(bv);

  Term a = mk_term(Kind::DISTINCT,
                   {mk_term(Kind::BV_MUL, {s, mk_term(Kind::BV_MUL, {x, t})}),
                    mk_term(Kind::BV_MUL, {mk_term(Kind::BV_MUL, {s, x}), t})});

  // Now, we check that the following formula is unsat.
  // (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))
  std::cout << "> Without terminator (with preprocessing):" << std::endl;
  std::cout << "Expect: unsat" << std::endl;
  std::cout << "Result: " << bitwuzla.check_sat({a}) << std::endl;

  // Now, for illustration purposes, we disable preprocessing, which will
  // significantly increase solving time, and connect a terminator instance
  // that terminates after a certain time limit.
  options.set(Option::PREPROCESS, false);
  // Create new Bitwuzla instance with reconfigured options.
  Bitwuzla bitwuzla2(options);
  // Configure and connect terminator.
  TestTerminator tt(1000);
  bitwuzla2.configure_terminator(&tt);

  // Now, we expect Bitwuzla to be terminated during the check-sat call.
  std::cout << "> With terminator (no preprocessing):" << std::endl;
  std::cout << "Expect: unknown" << std::endl;
  std::cout << "Result: " << bitwuzla2.check_sat({a}) << std::endl;

  return 0;
}
