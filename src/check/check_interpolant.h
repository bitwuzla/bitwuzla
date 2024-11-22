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
  bool check(const std::vector<Node>& A,
             const Node& C,
             const Node& interpolant);

 private:
  SolvingContext& d_ctx;
  util::Logger& d_logger;
};

}  // namespace bzla::check
#endif
