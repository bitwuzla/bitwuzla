/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_DISTINCT_DECISION_HEURISTIC_H_INCLUDED
#define BZLA_SAT_DISTINCT_DECISION_HEURISTIC_H_INCLUDED

#include <cstddef>
#include <unordered_map>
#include <vector>

#include "sat/sat_propagator.h"

namespace bzla::sat {

class DistinctDecisionHeuristic : public SatPropagator
{
 public:
  DistinctDecisionHeuristic(const std::vector<std::vector<int32_t>>& bvs);

  void attach_propagator(Propagator* propagator) override;
  void assign(int32_t lit) override;
  void unassign(int32_t var) override;
  bool done() const override { return false; }

 private:
  Propagator* d_propagator = nullptr;
  std::vector<std::vector<int32_t>> d_bvs;
  std::unordered_map<int32_t, size_t> d_idxmap;
  std::vector<bool> d_assigned;
};

}  // namespace bzla::sat

#endif
