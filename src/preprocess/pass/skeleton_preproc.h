/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_SKELETON_PREPROC_H_INCLUDED
#define BZLA_PREPROCESS_PASS_SKELETON_PREPROC_H_INCLUDED

#include <memory>

#include "backtrack/vector.h"
#include "node/unordered_node_ref_map.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla {

namespace sat {
class SatSolver;
}

namespace preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassSkeletonPreproc : public PreprocessingPass
{
 public:
  PassSkeletonPreproc(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

 private:
  int64_t lit(const Node& term);
  void encode(const Node& assertion);

  std::unique_ptr<sat::SatSolver> d_sat_solver;
  node::unordered_node_ref_map<bool> d_encode_cache;
  backtrack::vector<Node> d_assertions;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_new_assertions;

  } d_stats;
};

}  // namespace preprocess::pass
}  // namespace bzla
#endif
