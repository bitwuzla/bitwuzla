/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "check/check_interpolant.h"

namespace bzla::check {

CheckInterpolant::CheckInterpolant(SolvingContext& ctx)
    : d_ctx(ctx), d_logger(ctx.env().logger())
{
}

bool
CheckInterpolant::check(const std::vector<Node>& A,
                        const Node& C,
                        const Node& interpolant)
{
  if (!d_ctx.options().dbg_check_interpolant())
  {
    return true;
  }

  Log(1);
  Log(1) << "*** check interpolant";
  Log(1);

  NodeManager& nm = d_ctx.env().nm();

  // First, check if A implies interpolant.
  {
    option::Options opts;
    opts.dbg_check_interpolant.set(false);
    SolvingContext check_ctx(
        nm, opts, d_ctx.env().sat_factory(), "chkinterpol");
    for (size_t i = 0, n = A.size(); i < n; ++i)
    {
      Log(1) << "A[" << i << "]: " << A[i];
      check_ctx.assert_formula(A[i]);
    }
    Log(1) << "C: " << C;
    Log(1) << "I: " << interpolant;
    Log(1);
    check_ctx.assert_formula(nm.mk_node(node::Kind::NOT, {interpolant}));
    Result res = check_ctx.solve();
    Log(1) << "(and A (not I)): " << res;
    if (res != Result::UNSAT)
    {
      return false;
    }
  }

  // Then, check if interpolant implies C
  option::Options opts;
  opts.dbg_check_interpolant.set(false);
  SolvingContext check_ctx(nm, opts, d_ctx.env().sat_factory(), "chkinterpol");
  check_ctx.assert_formula(interpolant);
  check_ctx.assert_formula(nm.mk_node(node::Kind::NOT, {C}));
  Result res = check_ctx.solve();
  if (d_logger.is_log_enabled(1))
  {
    Log(1) << "(and I (not C)): " << res;
  }
  return res == Result::UNSAT;
}
}  // namespace bzla::check
