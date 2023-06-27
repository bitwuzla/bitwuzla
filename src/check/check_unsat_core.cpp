/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "check/check_unsat_core.h"

#include <unordered_set>

#include "node/node_manager.h"

namespace bzla::check {

using namespace node;

CheckUnsatCore::CheckUnsatCore(SolvingContext& ctx)
    : d_ctx(ctx), d_logger(ctx.env().logger())
{
}

bool
CheckUnsatCore::check()
{
  if (!d_ctx.options().dbg_check_unsat_core()
      || !d_ctx.options().produce_unsat_cores())
  {
    return true;
  }

  Log(1);
  Log(1) << "*** check unsat core";
  Log(1);

  option::Options opts;
  opts.dbg_check_model.set(false);
  opts.dbg_check_unsat_core.set(false);
  SolvingContext check_ctx(opts, "chkuc");
  for (const Node& assertion : d_ctx.get_unsat_core())
  {
    check_ctx.assert_formula(assertion);
  }

  return check_ctx.solve() == Result::UNSAT;
}

}  // namespace bzla::check
