/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_CHECK_CHECK_UNSAT_CORE_H_INCLUDED

#include <unordered_map>
#include <vector>

#include "solving_context.h"
#include "util/logger.h"

namespace bzla::check {

class CheckUnsatCore
{
 public:
  CheckUnsatCore(SolvingContext& ctx);

  bool check();

 private:
  SolvingContext& d_ctx;
  util::Logger& d_logger;
};

}  // namespace bzla::check

#endif
