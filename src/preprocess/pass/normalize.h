#ifndef BZLA_PREPROCESS_PASS_NORMALIZE_H_INCLUDED
#define BZLA_PREPROCESS_PASS_NORMALIZE_H_INCLUDED

#include "backtrack/unordered_map.h"
#include "node/unordered_node_ref_map.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

class PassNormalize : public PreprocessingPass
{
 public:
  PassNormalize(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  static node::unordered_node_ref_map<uint64_t> compute_factors(
      const Node& node);
  static std::pair<Node, bool> normalize_eq_mul(const Node& node0,
                                                const Node& node1);

  /**
   * Cache of processed nodes that maybe shared across substitutions.
   * Clear after a call to process to avoid sharing.
   */
  backtrack::unordered_map<Node, Node> d_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_normalizations;
  } d_stats;
};

}  // namespace bzla::preprocess::pass

#endif
