/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
  using ParentsMap      = std::unordered_map<Node, uint64_t>;
  using CoefficientsMap = std::unordered_map<Node, BitVector>;

  PassNormalize(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
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
   * @param coeffs The resulting map from node to its occurrence count.
   */
  void compute_coefficients(const Node& node,
                            node::Kind kind,
                            const std::unordered_map<Node, uint64_t>& parents,
                            CoefficientsMap& coeffs);

  /**
   * Factor out common subterms of given left hand side and right hand side
   * operands of a given kind.
   * @param kind The operator kind.
   * @param lhs The coefficients of the left hand side.
   * @param rhs The coefficients of the right hand side.
   * @return A node representing the combination of common subterms, maximizing
   *         sharing of subterms. Occurrences of common subterms are removed
   *         from `lhs` and `rhs`, e.g., if `a` appears twice in lhs and once
   *         in rhs, lhs will contain `a: 1` and rhs `a: 0` after calling this
   *         function.
   */
  CoefficientsMap compute_common_coefficients(CoefficientsMap& lhs,
                                              CoefficientsMap& rhs);

  Node mk_node(node::Kind kind, const CoefficientsMap& coeffs);

  /**
   * Normalize factors for bit-vector add.
   * @param node The adder node.
   * @param coeffs The coefficients of the adder as determined by
   *               compute_coefficients().
   * @param parents The parents information of this adder.
   * @return A bit-vector value representing the summarized, normalized leaf
   *         values of the given adder. After normalize_add() is called, it
   *         can be asserted that no values with a coefficient > 0 occur
   *         in the coefficients map.
   */
  BitVector normalize_add(const Node& node,
                          CoefficientsMap& coeffs,
                          ParentsMap& parents,
                          bool keep_value = false);
  /**
   * Normalize factors for bit-vector and.
   * @param node The adder node.
   * @param coeffs The coefficients of the and as determined by
   *               compute_coefficients().
   * @return A bit-vector value representing the constant folded, normalized
   *         leaf values of the given and. After normalize_and() is called,
   *         it can be asserted that no values with a coefficient > 0 occur
   *         in the coefficients map.
   */
  BitVector normalize_and(const Node& node, CoefficientsMap& coeffs);
  /**
   * Normalize factors for bit-vector multiplication.
   * @param node The adder node.
   * @param coeffs The coefficients of the multiplier as determined by
   *               compute_coefficients().
   * @return A bit-vector value representing the summarized, normalized leaf
   *         values of the given adder. After normalize_add() is called, it
   *         can be asserted that no values with a coefficient > 0 occur
   *         in the coefficients map.
   */
  BitVector normalize_mul(const Node& node,
                          CoefficientsMap& coeffs,
                          bool keep_value = false);
  /**
   * Helper to determine the normalized set of 'coefficients' (occurrences) for
   * an equality over the given two nodes of the same kind.
   * @param node0 The left hand side node of the equality.
   * @param node1 The right hand side node of the equality.
   * @param coeffs0 The left hand side coefficients, to be updated during
   *                this function call.
   * @param coeffs1 The right hand side coefficients, to be updated during
   *                this function call.
   */
  void normalize_coefficients_eq(const Node& node0,
                                 const Node& node1,
                                 CoefficientsMap& coeffs0,
                                 CoefficientsMap& coeffs1);
  /**
   * Normalize equality over addition or multiplication.
   * @param node0 The left hand side of the equality.
   * @param node1 The right hand side of the equality.
   * @param A pair of normalized node and a boolean flag to indicate if
   *        normalization was successful.
   */
  std::pair<Node, bool> normalize_eq_add_mul(const Node& node0,
                                             const Node& node1);
  /**
   * Helper to normalize equality over multiplication.
   * @param coeffs0 The normalized coefficients of the left hand side of the
   *                equality.
   * @param coeffs1 The normalized coefficients of the right hand side of the
   *                equality.
   * @param A pair of lhs and rhs normalized nodes.
   */
  std::pair<Node, Node> _normalize_eq_mul(const CoefficientsMap& coeffs0,
                                          const CoefficientsMap& coeffs1);
  /**
   * Helper to normalize equality over addition.
   * @param coeffs0 The normalized coefficients of the left hand side of the
   *                equality.
   * @param coeffs1 The normalized coefficients of the right hand side of the
   *                equality.
   * @param bv_size The bit-vector size of the operands of the equality.
   * @return A pair of lhs and rhs normalized nodes.
   */
  std::pair<Node, Node> _normalize_eq_add(CoefficientsMap& coeffs0,
                                          CoefficientsMap& coeffs1,
                                          uint64_t bv_size);

  /**
   * Helper for _normalize_eq_add().
   * @param coeffs0 The normalized coefficients of the left hand side of the
   *                equality.
   * @param coeffs1 The normalized coefficients of the right hand side of the
   *                equality.
   * @param value   The summarized lhs value as determined by normalize_add.
   *                Is updated during normalization and not added to the
   *                coefficients map.
   */
  void normalize_coefficients_eq_add(PassNormalize::CoefficientsMap& coeffs0,
                                     PassNormalize::CoefficientsMap& coeffs1,
                                     BitVector& value);

  /**
   * General normalization of associative and commutative operators.
   */
  std::pair<Node, bool> normalize_comm_assoc(node::Kind parent_kind,
                                             const Node& node0,
                                             const Node& node1);

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

  void collect_adders(const Node& assertion);

  /**
   * True to detect occurrences > 1, i.e., nodes of given kind that have
   * multiple parents. If true, we do not normalize such nodes to avoid
   * blow-up.
   */
  bool d_share_aware = false;

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

  std::vector<Node> d_adder_chains;
  std::unordered_map<Node, uint64_t> d_adder_chains_length;
  std::unordered_set<Node> d_adder_chains_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_normalizations;
  } d_stats;
};

}  // namespace bzla::preprocess::pass

#endif
