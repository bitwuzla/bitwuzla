#ifndef BZLA_PREPROCESS_PASS_NORMALIZE_H_INCLUDED
#define BZLA_PREPROCESS_PASS_NORMALIZE_H_INCLUDED

#include <unordered_map>

#include "backtrack/unordered_map.h"
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
  using CoefficientsMap = std::unordered_map<Node, BitVector>;
  /**
   * Compute the 'coefficients' (the number of occurrences) of the leafs of a
   * chain of nodes of the kind of the given top node. That is, (bvmul a (bvmul
   * c d)) would result in {{a -> 1}, {c -> 1}, {d -> 1}}, and (bvmul a (bvadd
   * c d)) in {{a -> 1}, {(bvadd c d) -> 1}}.
   *
   * @note If parents are given (share aware normalization), we treat subterms
   *       of the same kind as the top node as leafs if they have parents
   *       outside of this chain.
   *
   * @param node The top node.
   * @param parents The parents count of the equality over adders/multipliers
   *                this node is one of the operands of. Empty if we do
   *                not normalize in a share aware manner.
   * @return A map from node to its occurrence count.
   */
  std::unordered_map<Node, BitVector> compute_coefficients(
      const Node& node, const std::unordered_map<Node, uint64_t>& parents);
  /**
   * Helper to determine the normalized set of 'coefficients' (occurrences) for
   * an equality over the given two nodes of the same kind.
   * @param node0 The left hand side node of the equality.
   * @param node1 The right hand side node of the equality.
   * @param share_aware True to detect occurrences > 1, i.e., nodes of given
   *                    kind that have multiple parents. If true, we do not
   *                    normalize such nodes to avoid blow-up.
   * @return A set of normalized coefficients per node, with a boolean
   *         flag to indicate if normalization was successful. The resulting
   *         sets may be empty (only both, or none).
   */
  std::tuple<CoefficientsMap, CoefficientsMap, bool>
  get_normalized_coefficients_for_eq(const Node& node0,
                                     const Node& node1,
                                     bool share_aware);
  /**
   * Normalize equality over addition or multiplication.
   * @param node0 The left hand side of the equality.
   * @param node1 The right hand side of the equality.
   * @param share_aware True to detect occurrences > 1, i.e., nodes of given
   *                    kind that have multiple parents. If true, we do not
   *                    normalize such nodes to avoid blow-up.
   * @param A pair of normalized node and a boolean flag to indicate if
   *        normalization was successful.
   */
  std::pair<Node, bool> normalize_eq_add_mul(const Node& node0,
                                             const Node& node1,
                                             bool share_aware);
  /**
   * Helper to normalize equality over multiplication.
   * @param coeffs0 The normalized coefficients of the left hand side of the
   * equality.
   * @param coeffs1 The normalized coefficients of the right hand side of the
   * equality.
   * @param A pair of lhs and rhs normalized nodes.
   */
  std::pair<Node, Node> _normalize_eq_mul(const CoefficientsMap& coeffs0,
                                          const CoefficientsMap& coeffs1,
                                          uint64_t bv_size);
  /**
   * Helper to normalize equality over addition.
   * @param coeffs0 The normalized coefficients of the left hand side of the
   * equality.
   * @param coeffs1 The normalized coefficients of the right hand side of the
   * equality.
   * @param A pair of lhs and rhs normalized nodes.
   */
  std::pair<Node, Node> _normalize_eq_add(CoefficientsMap& coeffs0,
                                          CoefficientsMap& coeffs1,
                                          uint64_t bv_size);

  bool _normalize_coefficients_eq_add(PassNormalize::CoefficientsMap& coeffs0,
                                      PassNormalize::CoefficientsMap& coeffs1,
                                      uint64_t bv_size);

  /**
   * General normalization of adder and multiplier chains to extract common
   * parts.
   */
  std::pair<Node, bool> normalize_comm_assoc(node::Kind parent_kind,
                                             const Node& node0,
                                             const Node& node1,
                                             bool share_aware);

  /**
   * Helper to normalize common parts of lhs and rhs.
   *
   * @param kind Operator kind used to join operands in lhs.
   * @param lhs The normalized operands of the left hand side.
   * @param rhs The normalized operands of the right hand side.
   * @return Normalized left and right node.
   */
  std::pair<Node, Node> normalize_common(node::Kind kind,
                                         CoefficientsMap& lhs,
                                         CoefficientsMap& rhs);

  /**
   * Helper to extract top-most adder or multiplier from node.
   * @return The top-most adder or multiplier.
   */
  Node get_top(const Node& node);

  /**
   * Helper to rebuild top-most node found via get_top().
   *
   * @param node The node passed to get_top().
   * @param top The node of returned by get_top(node).
   * @param normalized The normalized node that should replace top.
   */
  Node rebuild_top(const Node& node, const Node& top, const Node& normalized);

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

  std::unordered_set<Node> d_parents_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_normalizations;
  } d_stats;
};

}  // namespace bzla::preprocess::pass

#endif
