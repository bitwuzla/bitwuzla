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
CheckInterpolant::check(const Node& C, size_t idx_B, const Node& interpolant)
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
    check_ctx.env().configure_terminator(d_ctx.env().terminator());
    const auto& assertions = d_ctx.original_assertions();
    for (size_t i = 0, n = assertions.size(); i < n; ++i)
    {
      if (i == idx_B) continue;
      Log(1) << "A[" << i << "]: " << assertions[i];
      check_ctx.assert_formula(assertions[i]);
    }
    Log(1) << "C: " << C;
    Log(1) << "I: " << interpolant;
    Log(1);
    check_ctx.assert_formula(nm.mk_node(node::Kind::NOT, {interpolant}));
    Log(1) << "check: (and A (not I))";
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
  check_ctx.env().configure_terminator(d_ctx.env().terminator());
  check_ctx.assert_formula(interpolant);
  check_ctx.assert_formula(nm.mk_node(node::Kind::NOT, {C}));
  Log(1) << "check: (and A (not I))";
  Result res = check_ctx.solve();
  Log(1) << "(and I (not C)): " << res;
  return res == Result::UNSAT;
}
}  // namespace bzla::check
