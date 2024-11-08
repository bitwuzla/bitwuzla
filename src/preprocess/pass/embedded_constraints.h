/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_EMBEDDED_CONSTRAINTS_H_INCLUDED
#define BZLA_PREPROCESS_PASS_EMBEDDED_CONSTRAINTS_H_INCLUDED

#include "backtrack/unordered_map.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to substitute embedded constraints with true.
 */
class PassEmbeddedConstraints : public PreprocessingPass
{
 public:
  PassEmbeddedConstraints(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  Node _process(const Node& node, std::unordered_map<Node, Node>& cache);

  /** Backtrackable substitution map. */
  backtrack::unordered_map<Node, Node> d_substitutions;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_substs;
  } d_stats;
};

}  // namespace bzla::preprocess::pass

#endif
