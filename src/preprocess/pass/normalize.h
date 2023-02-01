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
  /**
   * Compute the 'factors' (the number of occurrences) of subterms of a chain
   * of nodes of the kind of the given top node. That is, (bvmul a (bvmul c d))
   * would result in {{a -> 1}, {c -> 1}, {d -> 1}}, and (bvmul a (bvadd c d))
   * in {{a -> 1}, {(bvadd c d) -> 1}}.
   * @param node The top node.
   * @return A map from node to its occurrence count. Empty if share_aware
   *         is true and this occurrence count is > 1.
   */
  node::unordered_node_ref_map<uint64_t> compute_factors(
      const Node& node, const std::unordered_map<Node, uint64_t>& parents);
  /**
   * Helper to determine the normalized set of 'factors' (occurrences) for an
   * equality over the given two nodes of the same kind.
   * @param node0 The left hand side node of the equality.
   * @param node1 The right hand side node of the equality.
   * @param share_aware True to detect occurrences > 1, i.e., nodes of given
   *                    kind that have mutiple parents. If true, we do not
   *                    normalize such nodes to avoid blow-up on the bit-level.
   * @return A set of normalized factors per node, with a boolean
   *         flag to indicate if normalization was successful. The resulting
   *         sets may be empty (only both, or none).
   */
  std::tuple<node::unordered_node_ref_map<uint64_t>,
             node::unordered_node_ref_map<uint64_t>,
             bool>
  get_normalized_factors(const Node& node0,
                         const Node& node1,
                         bool share_aware);
  /**
   * Normalize equality over addition or multiplication.
   * @param node0 The left hand side of the equality.
   * @param node1 The right hand side of the equality.
   * @param share_aware True to detect occurrences > 1, i.e., nodes of given
   *                    kind that have mutiple parents. If true, we do not
   *                    normalize such nodes to avoid blow-up on the bit-level.
   * @param A pair of normalized node and a boolean flag to indicate if
   *        normalization was successful.
   */
  std::pair<Node, bool> normalize_eq_add_mul(const Node& node0,
                                             const Node& node1,
                                             bool share_aware);
  /**
   * Helper to normalize equality over multiplication.
   * @param factors0 The normalized factors of the left hand side of the
   * equality.
   * @param factors1 The normalized factors of the right hand side of the
   * equality.
   * @param A pair of lhs and rhs normalized nodes.
   */
  std::pair<Node, Node> _normalize_eq_mul(
      const node::unordered_node_ref_map<uint64_t>& factors0,
      const node::unordered_node_ref_map<uint64_t>& factors1,
      uint64_t bv_size);
  /**
   * Helper to normalize equality over addition.
   * @param factors0 The normalized factors of the left hand side of the
   * equality.
   * @param factors1 The normalized factors of the right hand side of the
   * equality.
   * @param A pair of lhs and rhs normalized nodes.
   */
  std::pair<Node, Node> _normalize_eq_add(
      const node::unordered_node_ref_map<uint64_t>& factors0,
      const node::unordered_node_ref_map<uint64_t>& factors1,
      uint64_t bv_size);

  /**
   * Cache of processed nodes that maybe shared across substitutions.
   * Clear after a call to process to avoid sharing.
   */
  std::unordered_map<Node, Node> d_cache;

  /**
   * Cache of parents count for currently reachable nodes, populated for the
   * duration of a call to apply().
   */
  std::unordered_map<Node, uint64_t> d_parents;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_normalizations;
  } d_stats;
};

}  // namespace bzla::preprocess::pass

#endif
