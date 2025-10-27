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
  SolvingContext check_ctx =
#if defined(BZLA_USE_CADICAL) || defined(BZLA_USE_CMS) \
    || defined(BZLA_USE_GIMSATUL) || defined(BZLA_USE_KISSAT)
      d_ctx.env().sat_factory()
          ? SolvingContext(d_ctx.env().nm(),
                           opts,
                           d_ctx.env().sat_factory(),
                           "chkuc",
                           true)
          : SolvingContext(d_ctx.env().nm(), opts, "chkuc", true);
#else
      SolvingContext(
          d_ctx.env().nm(), opts, d_ctx.env().sat_factory(), "chkuc", true);
#endif
  for (const Node& assertion : d_ctx.get_unsat_core())
  {
    check_ctx.assert_formula(assertion);
  }

  return check_ctx.solve() != Result::SAT; // unknown allowed for now
}

}  // namespace bzla::check
