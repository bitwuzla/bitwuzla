/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*----------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*----------------------------------------------------------------------------*/

#include "sat/eq_decision_heuristic.h"

#include <cassert>

#include "sat/propagator.h"

namespace bzla::sat {

EqDecisionHeuristic::EqDecisionHeuristic(
    const std::vector<std::vector<int32_t>>& bvs,
    const std::vector<uint64_t>& node_ids)
    : SatPropagator(Kind::EQ_DECISION, node_ids), d_bvs(bvs)
{
  if (!d_bvs.empty())
  {
    d_setter.resize(d_bvs[0].size(), 0);
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
      d_propagator->watch(var, this);
      d_idxmap.emplace(var, std::make_pair(i++, bit));
    }
  }
  // The bits of constants are literals of the single variable fixed to true,
  // which only maps to its first column, and its assignment may never be
  // notified since it was fixed before we watched it. Force columns with a
  // root-fixed bit to its value right away, they are never released.
  for (size_t idx = 0, size = d_setter.size(); idx < size; ++idx)
  {
    for (const auto& bv : d_bvs)
    {
      int32_t fixed = d_propagator->info(std::abs(bv[idx])).fixed;
      if (fixed)
      {
        int32_t value = bv[idx] < 0 ? -fixed : fixed;
        for (const auto& b : d_bvs)
        {
          d_propagator->force_phase(b[idx] * value);
        }
        d_setter[idx] = s_setter_fixed;
        break;
      }
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

  auto [idx, bit] = it->second;
  if (d_setter[idx])
  {
    return;
  }
  d_setter[idx] = var;
  // The bits are CNF literals, the bit is true iff its literal was assigned.
  int32_t value = lit == bit ? 1 : -1;
  for (size_t i = 0, size = d_bvs.size(); i < size; ++i)
  {
    d_propagator->force_phase(d_bvs[i][idx] * value);
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

  // Several variables map to the same column, only the one that forced its
  // phases releases them. Unassignments arrive in reverse assignment order,
  // hence it is the last variable of its column to be unassigned.
  size_t idx = it->second.first;
  if (d_setter[idx] != var)
  {
    return;
  }
  d_setter[idx] = 0;
  for (size_t i = 0, size = d_bvs.size(); i < size; ++i)
  {
    d_propagator->force_unphase(d_bvs[i][idx]);
  }
}

}  // namespace bzla::sat

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/
