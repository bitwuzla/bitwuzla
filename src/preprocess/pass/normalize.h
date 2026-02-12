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

#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"
#include "util/integer.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

class PassNormalize : public PreprocessingPass
{
 public:
  using OccMap = std::map<Node, util::Integer>;

  PassNormalize(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  /**
   * Compute the  number of occurrences of the leafs of a
   * chain of nodes of the kind of the given top node. That is, (bvmul a (bvmul
   * c d)) would result in {{a -> 1}, {c -> 1}, {d -> 1}}, and (bvmul a (bvadd
   * c d)) in {{a -> 1}, {(bvadd c d) -> 1}}.
   *
   * @param node The top node.
   * @param occs The resulting map from node to its occurrence count.
   */
  void compute_occurrences_mul(const Node& node, OccMap& occs) const;
  void compute_occurrences_add(const Node& node, OccMap& occs) const;

  /**
   * Factor out common subterms of given left hand side and right hand side
   * operands of a given kind.
   * @param kind The operator kind.
   * @param lhs The occurrences of the left hand side.
   * @param rhs The occurrences of the right hand side.
   * @return A node representing the combination of common subterms, maximizing
   *         sharing of subterms. Occurrences of common subterms are removed
   *         from `lhs` and `rhs`, e.g., if `a` appears twice in lhs and once
   *         in rhs, lhs will contain `a: 1` and rhs `a: 0` after calling this
   *         function.
   */
  OccMap compute_common_subterms(OccMap& lhs, OccMap& rhs);

  Node mk_node(node::Kind kind, const OccMap& occs);

  /*std::pair<Node, util::Integer> undo_mul_pow2_rewrite(const Node& n);*/

  /**
   * Normalize factors for bit-vector add.
   * @param node The adder node.
   * @param occs The term occurrences of the adder as determined by
   *               compute_occurrences().
   * @return A bit-vector value representing the summarized, normalized leaf
   *         values of the given adder. After normalize_add() is called, it
   *         can be asserted that no values with an occurrences > 0 occur
   *         in the occurrences map.
   */
  BitVector normalize_add(const Node& node,
                          OccMap& occs,
                          bool keep_value = false,
                          bool push_neg   = true);
  /**
   * Normalize factors for bit-vector and.
   * @param node The adder node.
   * @param occs The number of occurrences in the and as determined by
   *               compute_occurrences().
   * @return A bit-vector value representing the constant folded, normalized
   *         leaf values of the given and. After normalize_and() is called,
   *         it can be asserted that no values with a occurrences > 0 occur
   *         in the occurrences map.
   */
  BitVector normalize_and(const Node& node, OccMap& occs);
  /**
   * Normalize factors for bit-vector multiplication.
   * @param node The adder node.
   * @param occs The multiplier operand's exponents as determined by
   *               compute_occurrences().
   * @return A bit-vector value representing the summarized, normalized leaf
   *         values of the given adder. After normalize_mul() is called, it
   *         can be asserted that no values with a occurrences > 0 occur
   *         in the occurrences map.
   */
  BitVector normalize_mul(const Node& node,
                          OccMap& occs,
                          bool keep_value = false);
  /**
   * Helper to determine the normalized set of occurrences for
   * an equality over the given two nodes of the same kind.
   * @param node0 The left hand side node of the equality.
   * @param node1 The right hand side node of the equality.
   * @param occs0 The left hand side occurrences, to be updated during
   *                this function call.
   * @param occs1 The right hand side occurrences, to be updated during
   *                this function call.
   */
  void normalize_occurrences_eq(node::Kind kind,
                                const Node& node0,
                                const Node& node1,
                                OccMap& occs0,
                                OccMap& occs1);
  /**
   * Normalize equality over addition or multiplication.
   * @param node0 The left hand side of the equality.
   * @param node1 The right hand side of the equality.
   * @param A pair of normalized node and a boolean flag to indicate if
   *        normalization was successful.
   */
  std::pair<Node, bool> normalize_eq(node::Kind kind,
                                     const Node& node0,
                                     const Node& node1);

  /**
   * Helper for normalize_occurrences_eq().
   * @param occs0 The normalized occurrences of the left hand side of the
   *              equality.
   * @param occs1 The normalized occurrences of the right hand side of the
   *              equality.
   */
  void normalize_occurrences_eq_add(uint64_t bv_size,
                                    OccMap& occs0,
                                    OccMap& occs1);

  /**
   * General normalization of associative and commutative operators.
   */
  std::pair<Node, bool> normalize_comm_assoc(node::Kind parent_kind,
                                             const Node& node0,
                                             const Node& node1);

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

  void normalize_adders(const std::vector<Node>& assertions,
                        std::vector<Node>& norm_assertions);
  void collect_adders(const std::vector<Node>& assertions,
                      std::map<Node, OccMap>& adders);

  /**
   * Cache of processed nodes that maybe shared across substitutions.
   * Clear after a call to process to avoid sharing.
   */
  std::unordered_map<Node, Node> d_cache;

  std::vector<Node> d_adder_chains;
  std::unordered_map<Node, uint64_t> d_adder_chains_length;
  std::unordered_set<Node> d_adder_chains_cache;

  /** A rewriter configured specifically for normalization rewrites. */
  Rewriter d_rewriter;

  /** Indicates whether we compute a bit-blasting score. */
  bool d_enable_scoring = true;
  /** Only query caches for already processed assertions. */
  bool d_disabled = false;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_normalize_add;
    util::TimerStatistic& time_normalize_mul;
    util::TimerStatistic& time_compute_occurrences;
    util::TimerStatistic& time_adder_chains;
    util::TimerStatistic& time_score;
    uint64_t& num_normalizations;
    uint64_t& num_common_normalizations;
    uint64_t& num_normalized_assertions;
    uint64_t& num_pass1_successful;
    uint64_t& num_pass2_successful;
  } d_stats;
};

std::ostream& operator<<(std::ostream& os, const PassNormalize::OccMap& occs);

}  // namespace bzla::preprocess::pass

#endif
