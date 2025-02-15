/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_CHECK_CHECK_INTERPOLANT_H_INCLUDED

#include "solving_context.h"
#include "util/logger.h"

namespace bzla::check {

class CheckInterpolant
{
 public:
  CheckInterpolant(SolvingContext& ctx);
  /**
   * Check interpolant.
   * This checks the given interpolant I wrt to the current set of assertions A
   * and conjecture C, i.e., (and A (not I)) and (and I (not C)) are both unsat.
   * @param C           The conjecture.
   * @param idx_B       The index of the assertion B (not C) corresponding to C
   *                    on the assertion stack.
   * @param interpolant The interpolant I.
   * @return True if the check succeeds.
   */
  bool check(const Node& C, size_t idx_B, const Node& interpolant);

 private:
  SolvingContext& d_ctx;
  util::Logger& d_logger;
};

}  // namespace bzla::check
#endif
