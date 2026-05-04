/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/distinct_decision_heuristic.h"

#include <cassert>

#include "lib/bv/bitvector.h"
#include "sat/propagator.h"

namespace bzla::sat {

DistinctDecisionHeuristic::DistinctDecisionHeuristic(
    const std::vector<std::vector<int32_t>>& bvs)
    : d_bvs(bvs)
{
  if (!d_bvs.empty())
  {
    d_assigned.resize(d_bvs[0].size(), false);
  }
}

void
DistinctDecisionHeuristic::attach_propagator(Propagator* propagator)
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

  BitVector phase(d_bvs.front().size());
  // Watch all literals of watched bit-vectors.
  for (const auto& bv : d_bvs)
  {
    for (size_t i = 0, size = bv.size(); i < size; ++i)
    {
      int32_t lit = bv[i];
      d_propagator->observe(lit);
      // This is a heuristic for now and should be adapated based on current
      // assignments. We assume all bit-vectors to be different.
      d_propagator->force_phase(phase.bit(size - 1 - i) ? lit : -lit);
    }
    phase.ibvinc();
  }
}

void
DistinctDecisionHeuristic::assign(int32_t lit)
{
  (void) lit;
}

void
DistinctDecisionHeuristic::unassign(int32_t var)
{
  (void) var;
}

}  // namespace bzla::sat
