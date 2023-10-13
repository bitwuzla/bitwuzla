/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_CONTRADICTING_ANDS_H_INCLUDED
#define BZLA_PREPROCESS_PASS_CONTRADICTING_ANDS_H_INCLUDED

#include "backtrack/unordered_map.h"
#include "node/unordered_node_ref_set.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to substitute embedded constraints with true.
 */
class PassContradictingAnds : public PreprocessingPass
{
 public:
  PassContradictingAnds(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  /**
   * Determine if given node is a contradicting end.
   * @param node    The node to check.
   * @param visited The visited cache, records (globally, i.e., during the DFS
   *                traversal in apply() ) visited nodes.
   * @return A pair of leaf nodes to continue the DFS traversal in apply() and
   *         false if the node is not a contradicting and, and an empty set and
   *         true, otherwise.
   */
  std::pair<node::unordered_node_ref_set, bool> is_contradicting_and(
      const Node& node, node::unordered_node_ref_set& visited);

  /** Backtrackable substitution map. */
  backtrack::unordered_map<Node, Node> d_substitutions;
  /**
   * Cache of processed nodes that maybe shared across substitutions.
   * Clear after a call to process to avoid sharing.
   */
  std::unordered_map<Node, Node> d_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_substs;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
