/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_EQ_DECISION_HEURISTIC_H_INCLUDED
#define BZLA_SAT_EQ_DECISION_HEURISTIC_H_INCLUDED

#include <cstddef>
#include <unordered_map>
#include <utility>
#include <vector>

#include "sat/sat_propagator.h"

namespace bzla::sat {

class EqDecisionHeuristic : public SatPropagator
{
 public:
  EqDecisionHeuristic(const std::vector<std::vector<int32_t>>& bvs,
                      const std::vector<uint64_t>& node_ids);

  void attach_propagator(Propagator* propagator) override;
  void assign(int32_t lit) override;
  void unassign(int32_t var) override;
  bool done() const override { return false; }

 private:
  Propagator* d_propagator = nullptr;
  std::vector<std::vector<int32_t>> d_bvs;
  /** Maps a variable to its column and the literal it occurs as. */
  std::unordered_map<int32_t, std::pair<size_t, int32_t>> d_idxmap;
  /** The variable that forced the phases of a column, 0 if none. */
  std::vector<int32_t> d_setter;
};

}  // namespace bzla::sat

#endif
