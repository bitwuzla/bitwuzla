/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_VARIABLE_SUBSTITUTION_H_INCLUDED
#define BZLA_PREPROCESS_PASS_VARIABLE_SUBSTITUTION_H_INCLUDED

#include <tuple>

#include "backtrack/object.h"
#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform term substitution based on top-level
 * equalities.
 */
class PassVariableSubstitution : public PreprocessingPass
{
 public:
  PassVariableSubstitution(Env& env,
                           backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

  /** Exclude variables from being substituted. */
  void exclude(const std::unordered_set<Node>& exclude);

  /** Process term and apply currently cached substitutions. */
  Node process(const Node& term) override;

  /** Get current set of substitutions. */
  const std::unordered_map<Node, Node>& substitutions() const;

  /** Get substitution assertion for substituted variable. */
  const Node& substitution_assertion(const Node& var) const;

 private:
  /**
   * Extract variable substitution, if possible.
   * @param assertion The assertion to extract a variable substitution from.
   * @return A pair that maps variable to substitution, if successful, and
   *         a pair of null nodes, otherwise.
   */
  std::pair<Node, Node> find_substitution(const Node& assertion);
  std::vector<Node> normalize_for_substitution(const Node& assertion);
  std::pair<Node, Node> normalize_substitution_eq(const Node& node);
  std::pair<Node, Node> normalize_substitution_bv_ineq(const Node& node);
  std::vector<Node> normalize_substitution_eq_bv_concat(const Node& node);

  /**
   * Register `var = term` derived from the assertion at index `index` as
   * substitution candidate. Swaps `var` and `term` if `term` is a variable
   * that is the better candidate.
   * @return False if neither side can be substituted.
   */
  bool add_candidate(const AssertionVector& assertions,
                     Node var,
                     Node term,
                     const Node& assertion,
                     size_t index);

  /** @return Whether `var` can be substituted at all. */
  bool can_substitute(const Node& var) const;

  /**
   * @return Whether `term` is a concatenation of variables that can be
   *         substituted and do not have a substitution candidate yet.
   */
  bool is_concat_of_vars(const Node& term) const;

  /**
   * Substitute the current substitutions and candidates in `term`.
   *
   * Rebuilt nodes are rewritten on construction, unchanged nodes are kept as
   * is, i.e., the result is rewritten if `term` is.
   *
   * Cyclic candidates are detected lazily: a node reached again while it is
   * still being expanded closes a cycle, which is broken by moving the
   * innermost candidate on the current path to its next substitution term.
   */
  Node substitute(const Node& term);

  /** Clear the substitution cache if substitutions were popped. */
  void sync_cache();

  /**
   * Determines whether `var` occurs in the assertions of previous
   * preprocessing calls. These assertions are not reprocessed, so the
   * substitution constraint of such a variable must be kept.
   */
  bool occurs_in_previous(const AssertionVector& assertions, const Node& var);

  void process_extracts(
      const std::unordered_map<Node, std::vector<std::pair<Node, Node>>>&
          extract_map,
      AssertionVector& assertions);

  /** Helper struct for extract elimination. */
  struct Range
  {
    uint64_t upper;
    uint64_t lower;
    std::vector<Node> terms;
  };

  /**
   * Compute the non-overlapping set of given index ranges indices.
   */
  std::vector<Range> compute_non_overlapping(
      NodeManager& nm,
      uint64_t size,
      std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>>&
          indices);

  /** Substitution candidates of a variable found in the current apply(). */
  struct Candidate
  {
    /** Candidate terms with their substitution assertions and indices. */
    std::vector<std::tuple<Node, Node, size_t>> terms;
    /** Index of the selected term, terms.size() if all terms are cyclic. */
    size_t selected = 0;
    /** True if the substitution constraint must be kept. */
    bool keep = false;
  };

  /** Current set of variable substitutions. */
  backtrack::unordered_map<Node, Node> d_substitutions;
  /** Maps substituted variable to its substitution assertion. */
  backtrack::unordered_map<Node, Node> d_substitution_assertions;
  /**
   * Maps assertion stack index to substituted variable for substitution
   * assertions that must be kept.
   */
  backtrack::unordered_map<size_t, Node> d_keep;

  /** Substitution candidates of the current apply(). */
  std::unordered_map<Node, Candidate> d_candidates;
  /** Candidate variables in the order they were found. */
  std::vector<Node> d_candidate_vars;
  /**
   * Maps substitution assertions of the current apply() derived from extracts
   * to the number of extracts they eliminate, counted if the candidate is
   * selected.
   */
  std::unordered_map<Node, size_t> d_extract_eqs;

  /**
   * Substitution cache, maps nodes to their substituted node. Pending
   * expansions are marked with a null node.
   */
  std::unordered_map<Node, Node> d_cache;
  /** Number of substitutions d_cache was computed for. */
  size_t d_cache_num_substs = 0;
  /**
   * Lower bound of the node ids of all variables that were ever substituted.
   * Nodes with smaller ids cannot contain any of them.
   */
  uint64_t d_min_subst_id = UINT64_MAX;

  /**
   * Nodes occurring in the assertions of previous preprocessing calls up to
   * stack index d_prev_scanned, computed on demand by occurs_in_previous().
   */
  backtrack::unordered_set<Node> d_prev_nodes;
  backtrack::object<size_t> d_prev_scanned;

  /** Do not substitute these consts. */
  std::unordered_set<Node> d_exclude_consts;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    util::TimerStatistic& time_register;
    util::TimerStatistic& time_substitute;
    util::TimerStatistic& time_scan_previous;
    util::TimerStatistic& time_find_substitution;
    util::TimerStatistic& time_compute_non_overlap;
    uint64_t& num_substs;
    uint64_t& num_cycles;
    uint64_t& num_norm_eq_linear_eq;
    uint64_t& num_norm_eq_gauss_elim;
    uint64_t& num_norm_eq_bv_concat;
    uint64_t& num_norm_bv_ult;
    uint64_t& num_norm_bv_slt;
    uint64_t& num_eq_elim_extracts;
    uint64_t& num_eq_elim_extracts_substs;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
