/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_ELIM_EXTRACT_H_INCLUDED
#define BZLA_PREPROCESS_PASS_ELIM_EXTRACT_H_INCLUDED

#include <unordered_map>

#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to eliminate applications on lambda nodes.
 */
class PassElimExtract : public PreprocessingPass
{
 public:
  PassElimExtract(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

  Node process(const Node& term) override;

 private:
  std::unordered_set<Node> d_cache;

  /**
   * Collect all bit-vectors extracts on bit-vector constants reachable from
   * assertion.
   */
  void collect_extracts(const Node& assertion,
                        std::unordered_map<Node, std::vector<Node>>& extracts);

  /** Normalize extract indices, eliminates overlapping extract ranges. */
  bool compute_non_overlapping(
      std::unordered_set<std::pair<uint64_t, uint64_t>>& indices);

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_elim;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
