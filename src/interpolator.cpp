/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "interpolator.h"

namespace bzla {

Interpolator::Interpolator(SolvingContext& ctx)
    : d_ctx(ctx),
      d_env(ctx.env()),
      d_logger(d_env.logger()),
      d_original_assertions(ctx.original_assertions()),
      d_pp_assertions(ctx.assertions()),
      d_stats(d_env.statistics())
{
}

Node
Interpolator::get_interpolant(const std::unordered_set<Node>& A)
{
  util::Timer timer(d_stats.time_get_interpolant);

  Log(1);
  Log(1) << "*** interpolant";
  Log(1);
  Log(1) << "expected assertion partitioning:";
  if (d_logger.is_log_enabled(1))
  {
    for (size_t i = 0, ia = 0, ib = 0, n = d_original_assertions.size(); i < n;
         ++i)
    {
      if (A.find(d_original_assertions[i]) != A.end())
      {
        Log(1) << "A[" << ia++ << "]: " << d_original_assertions[i];
      }
      else
      {
        Log(1) << "B[" << ib++ << "]: " << d_original_assertions[i];
      }
    }
  }
  Log(1);

  Node ipol;
  NodeManager& nm = d_env.nm();

  // Partition preprocessed assertions into A and B
  std::unordered_set<Node> B;
  std::vector<Node> ppA, ppB;
  std::unordered_set<Node> orig_ass{d_original_assertions.begin(),
                                    d_original_assertions.end()};
  for (size_t i = 0, size = d_pp_assertions.size(); i < size; ++i)
  {
    // trace assertion back to original assertion
    Node orig =
        d_ctx.preprocessor().original_assertion(d_pp_assertions[i], orig_ass);
    auto it = A.find(orig);
    if (it != A.end())
    {
      ppA.push_back(d_pp_assertions[i]);
    }
    else
    {
      B.insert(orig);
      ppB.push_back(d_pp_assertions[i]);
    }
  }

  Log(1) << "actual assertion partitioning:";
  if (d_logger.is_log_enabled(1))
  {
    for (const auto& a : A)
    {
      Log(1) << "A: " << a;
    }
    for (const auto& a : B)
    {
      Log(1) << "B: " << a;
    }
    for (size_t i = 0, size = ppA.size(); i < size; ++i)
    {
      Log(1) << "ppA[" << i << "]: " << ppA[i];
    }
    for (size_t i = 0, size = ppB.size(); i < size; ++i)
    {
      Log(1) << "ppB[" << i << "]: " << ppB[i];
    }
  }

  // Preprocessor determined unsat, so we can make a shortcut.
  if (d_ctx.sat_state_pp() == Result::UNSAT)
  {
    for (const auto& a : ppA)
    {
      if (a.is_value() && !a.value<bool>())
      {
        ipol = nm.mk_value(false);
        break;
      }
    }
    for (const auto& a : ppB)
    {
      if (a.is_value() && !a.value<bool>())
      {
        ipol = nm.mk_value(true);
        break;
      }
    }
  }

  if (ipol.is_null())
  {
    ipol = d_ctx.solver_engine().interpolant(A, B, ppA, ppB);
  }

  return ipol;
}

Interpolator::Statistics::Statistics(util::Statistics& stats)
    : time_get_interpolant(stats.new_stat<util::TimerStatistic>(
          "interpolator::time_get_interpolant"))
{
}
}  // namespace bzla
