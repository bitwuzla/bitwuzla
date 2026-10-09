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

#include "sat/distinct_decision_heuristic.h"

#include <cassert>
#include <utility>

#include "lib/bv/bitvector.h"
#include "sat/propagator.h"

namespace bzla::sat {

DistinctDecisionHeuristic::DistinctDecisionHeuristic(
    std::vector<std::vector<int32_t>> bvs,
    const std::vector<uint64_t>& node_ids)
    : SatPropagator(Kind::DISTINCT_DECISION, node_ids), d_bvs(std::move(bvs))
{
}

void
DistinctDecisionHeuristic::attach_propagator(Propagator* propagator)
{
  d_propagator = propagator;
  assert(!d_bvs.empty());
  BitVector phase(d_bvs.front().size());
  // Decisions are only allowed over observed variables. The bits are not
  // watched since we do not track their assignments. Bits that are already
  // root-fixed, e.g., of constants, are notified as assigned when observed and
  // are thus never decided on.
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

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/
