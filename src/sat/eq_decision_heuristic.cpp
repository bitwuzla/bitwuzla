/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/eq_decision_heuristic.h"

#include <cassert>

#include "sat/propagator.h"

namespace bzla::sat {

EqDecisionHeuristic::EqDecisionHeuristic(
    const std::vector<std::vector<int32_t>>& bvs)
    : d_bvs(bvs)
{
  if (!d_bvs.empty())
  {
    d_assigned.resize(d_bvs[0].size(), false);
  }
}

void
EqDecisionHeuristic::attach_propagator(Propagator* propagator)
{
  d_propagator = propagator;
  assert(!d_bvs.empty());
  for (const auto& bv : d_bvs)
  {
    size_t i = 0;
    for (int32_t bit : bv)
    {
      int32_t var = std::abs(bit);
      d_propagator->watch(var);
      d_idxmap.emplace(var, i++);
    }
  }
}

void
EqDecisionHeuristic::assign(int32_t lit)
{
  int32_t var = std::abs(lit);
  auto it     = d_idxmap.find(var);
  if (it == d_idxmap.end())
  {
    return;
  }

  size_t idx = it->second;
  if (d_assigned[idx])
  {
    return;
  }
  d_assigned[idx] = true;
  int32_t phase   = lit < 0 ? -1 : 1;
  for (size_t i = 0, size = d_bvs.size(); i < size; ++i)
  {
    d_propagator->force_phase(d_bvs[i][idx] * phase);
  }
}

void
EqDecisionHeuristic::unassign(int32_t var)
{
  auto it = d_idxmap.find(var);
  if (it == d_idxmap.end())
  {
    return;
  }

  size_t idx = it->second;
  if (!d_assigned[idx])
  {
    return;
  }
  d_assigned[idx] = false;
  for (size_t i = 0, size = d_bvs.size(); i < size; ++i)
  {
    d_propagator->force_unphase(d_bvs[i][idx]);
  }
}

}  // namespace bzla::sat
