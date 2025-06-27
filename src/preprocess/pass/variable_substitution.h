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
#include "preprocess/preprocessing_pass.h"
#include "preprocess/simplify_cache.h"
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

  /** Process term and apply currently cached substitutions. */
  Node process(const Node& term) override;

  /** Get current set of substitutions. */
  const backtrack::unordered_map<Node, Node>& substitutions() const;

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

  Node substitute(
      const Node& term,
      const std::unordered_map<Node, std::vector<Node>>& substitutions,
      backtrack::unordered_map<Node, bool>& subst_cache,
      bool use_coi);

  /** Determines whether we can fully substitute given variable. */
  bool is_safe_to_substitute(const Node& var);
  /** Mark COI of substitutions and remove cyclic candidate substitutions. */
  void mark_coi_and_remove_cycles(
      const AssertionVector& assertions,
      std::unordered_map<Node, std::vector<Node>>& subst_candidates);

  /** Maps variable to its original substitution assertion. */
  backtrack::unordered_map<Node, Node> d_substitutions;

  /** Caches visited nodes during substitution. */
  backtrack::unordered_map<Node, bool> d_subst_cache;
  /** Caches visited nodes during COI computation. */
  backtrack::unordered_map<Node, std::pair<bool, size_t>> d_coi_cache;

  /** COI for current set of substitutions. */
  backtrack::unordered_set<Node> d_coi;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    util::TimerStatistic& time_register;
    util::TimerStatistic& time_backtrack_cyclic_subst;
    util::TimerStatistic& time_substitute;
    util::TimerStatistic& time_coi;
    util::TimerStatistic& time_find_substitution;
    util::TimerStatistic& time_process;
    uint64_t& num_substs;
    uint64_t& num_cycles;
    uint64_t& num_norm_eq_linear_eq;
    uint64_t& num_norm_eq_gauss_elim;
    uint64_t& num_norm_eq_bv_concat;
    uint64_t& num_norm_bv_ult;
    uint64_t& num_norm_bv_slt;
    uint64_t& num_coi_trav;
    uint64_t& num_subst_trav;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
