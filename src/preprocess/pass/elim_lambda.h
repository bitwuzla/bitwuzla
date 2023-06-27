/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_ELIM_LAMBDA_H_INCLUDED
#define BZLA_PREPROCESS_PASS_ELIM_LAMBDA_H_INCLUDED

#include <unordered_map>

#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to eliminate applications on lambda nodes.
 */
class PassElimLambda : public PreprocessingPass
{
 public:
  PassElimLambda(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

  Node process(const Node& term) override;

 private:
  Node reduce(const Node& node) const;

  std::unordered_map<Node, Node> d_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_elim;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
