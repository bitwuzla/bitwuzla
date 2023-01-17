#ifndef BZLA_PREPROCESS_PASS_EMBEDDED_CONSTRAINTS_H_INCLUDED
#define BZLA_PREPROCESS_PASS_EMBEDDED_CONSTRAINTS_H_INCLUDED

#include "backtrack/unordered_map.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to substitue embedded constraints with true.
 */
class PassEmbeddedConstraints : public PreprocessingPass
{
 public:
  PassEmbeddedConstraints(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_substs;
  } d_stats;

  /** Replace all occurrences of `d_substititutions` in `node. */
  Node substitute(const Node& node);
  /** Only required to check the current assertion level. */
  const backtrack::BacktrackManager* d_backtrack_mgr;
  /** Backtrackable substitution map. */
  backtrack::unordered_map<Node, Node> d_substitutions;
  /**
   * Cache of processed nodes that maybe shared across substitutions.
   */
  backtrack::unordered_map<Node, Node> d_cache;
};

}  // namespace bzla::preprocess::pass

#endif
