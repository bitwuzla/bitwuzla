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
   * This checks the given interpolant I wrt to assertions A and B (all of each
   * currently asserted and A given in terms of original assertions).
   * We check that (=> A I) and (=> I (not B)), i.e., that (and A (not I)) and
   * (and I B) are both unsat.
   * @param A           The set of original assertions representing A.
   * @param interpolant The interpolant I.
   * @return True if the check succeeds.
   */
  bool check(const std::unordered_set<Node>& A, const Node& interpolant);

 private:
  SolvingContext& d_ctx;
  util::Logger& d_logger;
};

}  // namespace bzla::check
#endif
