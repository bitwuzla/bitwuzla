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

#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "node/unordered_node_ref_map.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassVariableSubstitution : public PreprocessingPass
{
 public:
  PassVariableSubstitution(Env& env,
                           backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

  /** Process term and apply currently cached substitutions. */
  Node process(const Node& term) override;

  /** Get current set of substitutions. */
  const std::unordered_map<Node, Node>& substitutions() const;

  /** Get substitution assertion for substituted variable. */
  const Node& substitution_assertion(const Node& var) const;

 private:
  void remove_indirect_cycles(std::unordered_map<Node, Node>& substs) const;

  bool is_direct_cycle(const Node& var, const Node& term) const;

  /**
   * Extract variable substitution, if possible.
   * @param assertion The assertion to extract a variable substitution from.
   * @return A pair that maps variable to substitution, if successful, and
   *         a pair of null nodes, otherwise.
   */
  std::pair<Node, Node> find_substitution(const Node& assertion);
  Node normalize_for_substitution(const Node& assertion);
  std::pair<Node, Node> normalize_substitution_eq(const Node& node);
  std::pair<Node, Node> normalize_substitution_bv_ineq(const Node& node);

  Node substitute(const Node& term,
                  const Node& excl_var,
                  const std::unordered_map<Node, Node>& substitutions,
                  std::unordered_map<Node, Node>& subst_cache);

  Node process(const Node& term, const Node& excl_var);

  /**
   * Determines whether we can fully substitute given variable, or if we have
   * to keep the substitution assertion.
   */
  bool is_safe_to_substitute(const Node& var, size_t assertion_start_index);
  /** Maps variables found in assertion to index. */
  void find_vars(const Node& assertion, size_t index);

  /** Current set of variable substitutions. */
  backtrack::unordered_map<Node, std::pair<Node, Node>> d_substitutions;
  /**
   * Current set of variable substitution assertions, maps assertion index to
   * substituted var.
   */
  backtrack::unordered_map<size_t, Node> d_substitution_assertions;

  /**
   * Maps first occurrence of variable to assertion index where it was found.
   */
  backtrack::unordered_map<Node, size_t> d_first_seen;
  /** Cache for find_vars. */
  backtrack::unordered_set<Node> d_first_seen_cache;

  /** Backtrackable cache. */
  class Cache : public backtrack::Backtrackable
  {
   public:
    Cache(backtrack::BacktrackManager* mgr);

    void push() override;

    void pop() override;

    /** @return Current substitution map. */
    std::unordered_map<Node, Node>& substitutions();

    const std::unordered_map<Node, Node>& substitutions() const;

    /** @return Current substitution cache. */
    std::unordered_map<Node, Node>& cache();

   private:
    /** Backtrackable substitution map. One map per scope level. */
    std::vector<std::unordered_map<Node, Node>> d_map;
    /** Backtrackable substitution cache. One cache per scope level. */
    std::vector<std::unordered_map<Node, Node>> d_cache;
  };

  /** Backtrackable substitution cache. */
  Cache d_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    util::TimerStatistic& time_register;
    util::TimerStatistic& time_direct_cycle_check;
    util::TimerStatistic& time_remove_cycles;
    util::TimerStatistic& time_substitute;
    util::TimerStatistic& time_find_vars;
    util::TimerStatistic& time_find_substitution;
    uint64_t& num_substs;
    uint64_t& num_linear_eq;
    uint64_t& num_gauss_elim;
    uint64_t& num_norm_bv_ult;
    uint64_t& num_norm_bv_slt;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
