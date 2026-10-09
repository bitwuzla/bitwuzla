/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_QUANT_QUANT_SOLVER_H_INCLUDED
#define BZLA_SOLVER_QUANT_QUANT_SOLVER_H_INCLUDED

#include <memory>

#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "solver/bv/bv_inverter.h"
#include "solver/solver.h"
#include "util/statistics.h"

namespace bzla {

class SolvingContext;

namespace quant {

class QuantSolver : public Solver
{
 public:
  enum class LemmaKind
  {
    /** Instantiation lemma with ground terms or model values. */
    MBQI_INST,
    /** Instantiation lemma with at least one inverse term (see quant_ic). */
    MBQI_INST_INV,
    /** Skolemization lemma for a universal quantifier assigned to false. */
    SKOLEMIZATION,
  };

  /**
   * Determine if given term is a leaf node for other solvers than the
   * quant solver.
   * @param term The term to query.
   * @return True if `term` is a quantified formula.
   */
  static bool is_theory_leaf(const Node& term);

  QuantSolver(Env& env, SolverState& state);
  ~QuantSolver();

  /**
   * Check quantified formulas against the current model.
   *
   * Universally quantified formulas assigned to false are skolemized, and
   * checked for counterexamples via mbqi_check() when assigned to true.
   *
   * @return True if none of the quantified formulas assigned to true has a
   *         counterexample in the current model.
   */
  bool check() override;

  /**
   * Not supported. The values of quantified formulas are determined by the
   * bit-vector abstraction.
   */
  Node value(const Node& term) override;

  /**
   * Register a quantified formula.
   * @param term The quantified formula.
   */
  void register_term(const Node& term) override;
  /**
   * Register an assertion.
   * @note The assertion is registered after it was processed by the
   *       abstraction module, and thus may contain abstractions.
   * @param assertion The assertion.
   */
  void register_assertion(const Node& assertion);

 private:
  /**
   * Rewrite and send given lemma.
   * @note Duplicate lemmas and lemmas that rewrite to true are not sent.
   * @param lemma The lemma.
   * @param kind  The kind of the lemma.
   */
  void lemma(const Node& lemma, LemmaKind kind);

  /**
   * Instantiate the body of the given quantified formula.
   * @param q      The quantified formula.
   * @param substs Map from variables of the quantifier prefix of `q` to their
   *               instantiation terms.
   * @return The body of `q` instantiated with `substs`.
   */
  Node instantiate(const Node& q, const std::unordered_map<Node, Node>& substs);
  /**
   * Convenience wrapper for node::utils::substitute.
   * @param n      The node.
   * @param substs The substitution map.
   * @return The node with `substs` applied.
   */
  Node substitute(const Node& n, const std::unordered_map<Node, Node>& substs);

  /**
   * Get the instantiation constant for the variable of the given quantifier.
   * Its value in the model of the MBQI solver is a counterexample.
   * @param q The quantifier.
   * @return The instantiation constant, created on first query.
   */
  const Node& inst_const(const Node& q);
  /**
   * Get the skolem constant for the variable of given quantifier.
   * @param q The quantifier.
   * @return The skolem constant, created on first query.
   */
  const Node& skolem_const(const Node& q);

  /**
   * Skolemize given quantified formula.
   * @param q The quantified formula.
   * @return The body of `q` with all variables of its quantifier prefix
   *         replaced by their skolem constants.
   */
  Node skolemize(const Node& q);

  /**
   * Get the skolemization lemma `(not q) => (not skolemize(q))` for the given
   * quantified formula.
   * @param q The quantified formula.
   * @return The rewritten skolemization lemma, created on first query.
   */
  const Node& skolemization_lemma(const Node& q);

  /**
   * Collect the constants, ground terms and ground applications of partial
   * floating-point operators that occur in given assertion. Ground terms that
   * contain quantifiers are not collected.
   * @param q The assertion.
   */
  void process(const Node& q);

  /**
   * Replace all abstractions in the given node with their values in the
   * current model.
   * @param node The node.
   * @return The node with all abstractions replaced by their values.
   */
  Node abstractions_to_values(const Node& node);

  /**
   * The MBQI check.
   *
   * Check given quantified formulas and generate instantiation lemmas for the
   * ones with counterexamples.
   *
   * @param to_check The quantified formulas assigned to true.
   * @return True if no quantified formula in `to_check` has a counterexample.
   *         False if there were counterexamples, or if the MBQI sub-query
   *         returned unknown.
   */
  bool mbqi_check(const std::vector<Node>& to_check);
  /**
   * Get the formula asserted in the MBQI solver to check given quantified
   * formula for a counterexample.
   * @param q The quantified formula.
   * @return The negated body of `q` with all variables of its quantifier
   *         prefix replaced by their instantiation constants.
   */
  const Node& mbqi_inst(const Node& q);

  /**
   * Generate and send an instantiation lemma `q => q[x := t]` for the given
   * quantified formula based on its current counterexample.
   *
   * @param q            The quantified formula with a counterexample.
   * @param model_values The values of the instantiation constants in the model
   *                     of the MBQI solver, i.e., the counterexample.
   * @param ground_terms Map from values in the current model to ground terms
   *                     with that value, ordered by preference.
   */
  void mbqi_lemma(
      const Node& q,
      const std::unordered_map<Node, Node>& model_values,
      const std::unordered_map<Node, std::vector<Node>>& ground_terms);

  /**
   * Replace the values occurring in the given term with ground terms that
   * have the same value in the current model. If `term` is a value, this
   * selects a single ground term. Values without such a ground term are kept.
   * The selected ground terms are recorded in d_selected_terms.
   * @param term         The term.
   * @param ground_terms Map from values in the current model to ground terms
   *                     with that value, the first term is selected.
   * @return The term with its values replaced by ground terms.
   */
  Node symbolic_term(
      const Node& term,
      const std::unordered_map<Node, std::vector<Node>>& ground_terms);

  /**
   * Try to find an inverse term instantiation for the variable of `q_cur`.
   * @param q            The active quantified formula.
   * @param q_cur        The quantifier for whose variable to find an
   *                     instantiation.
   * @param body         The body of the quantified formula.
   * @param inst         The instantiation term determined via symbolic_term().
   * @param model_values The current model values of the currently active
   *                     instantiation constants.
   * @param deps         Output parameter, the free variables of the inverse
   *                     and its conditions (variables of the quantifier
   *                     prefix). The caller must only accept the inverse if
   *                     closing these references keeps the conditions over
   *                     the fresh instantiation constants acyclic (else they
   *                     may form a cyclic, potentially unsatisfiable system
   *                     of constraints), and caches accepted inverses.
   * @param conditions   Output parameter, the conditions of this inverse
   *                     (choice conditions and the optional definition of the
   *                     fresh instantiation constant), to be added to the
   *                     lemma by the caller on acceptance.
   * @return The inverse term.
   */
  Node inverse_term(const Node& q,
                    const Node& q_cur,
                    const Node& body,
                    const Node& inst,
                    const std::unordered_map<Node, Node>& model_values,
                    std::unordered_set<Node>& deps,
                    std::vector<Node>& conditions);

  /**
   * Helper for inverse_term(). Determines the node and path to consider
   * for computing an inverse term. For example, when bounds-based projection
   * is enabled, it will replace the bit-vectore inequality in the path with
   * an equality based on the operands model values.
   * @param q            The active quantified formula.
   * @param node         The node.
   * @param var          The variable to find the instantiation for.
   * @param model_values The current model values of the currently active
   *                     instantiation constants.
   */
  std::pair<Node, std::unordered_map<Node, size_t>> project(
      const Node& q,
      const Node& node,
      const Node& var,
      const std::unordered_map<Node, Node>& model_values);

  /**
   * Helper for project(). Determines the model values of the operands of the
   * given node (must be a bit-vector equality or inequality).
   * @param q            The active quantified formula.
   * @param node         The node.
   * @param model_values The current model values of the currently active
   *                     instantiation constants.
   */
  std::pair<BitVector, BitVector> get_value_for_operands(
      const Node& q,
      const Node& node,
      const std::unordered_map<Node, Node>& model_values);

  /** @return True if node is considered too expensive to add as a lemma. */
  bool is_expensive(const Node& node) const;

  /** The associated bit-vector inverter. */
  bv::BvInverter d_bv_inverter;

  /** The registered quantified formulas. */
  backtrack::vector<Node> d_quantifiers;
  /** The registered assertions, may contain abstractions. */
  backtrack::vector<Node> d_assertions;
  /** The processed assertions and the collected terms (see process()). */
  backtrack::unordered_set<Node> d_process_cache;
  /** The constants in the assertions, fixed to their values in MBQI checks. */
  backtrack::vector<Node> d_consts;
  /**
   * The ground applications of partial floating-point operators in the
   * assertions, fixed to their values in MBQI checks. May contain
   * abstractions.
   */
  backtrack::vector<Node> d_partial_ops;
  /**
   * The ground terms in the assertions, considered for instantiation. May
   * contain abstractions.
   */
  backtrack::vector<Node> d_ground_terms;
  /**
   * Maps ground term ids to the number of times they were selected for
   * instantiation. Ground terms with the same value are ordered by this
   * count, so that less frequently selected terms are preferred.
   */
  std::unordered_map<uint64_t, uint64_t> d_num_selected;
  /**
   * The ids of the ground terms selected in the current lemma generation
   * round of mbqi_check(), see symbolic_term().
   */
  std::vector<uint64_t> d_selected_terms;

  /** Maps quantifiers to the instantiation constant of their variable. */
  std::unordered_map<Node, Node> d_instantiation_consts;
  /** Maps quantifiers to the skolem constant of their variable. */
  std::unordered_map<Node, Node> d_skolem_consts;

  /** Maps quantified formulas to their skolemization lemma. */
  backtrack::unordered_map<Node, Node> d_skolemization_lemmas;

  /** The MBQI solver, recreated in each mbqi_check(). */
  std::unique_ptr<SolvingContext> d_mbqi_solver;
  /** Cache for mbqi_inst(). */
  std::unordered_map<Node, Node> d_mbqi_inst;
  /** The rewritten lemmas generated so far, to detect duplicates. */
  backtrack::unordered_set<Node> d_lemma_cache;

  /** Maps the number of value instantiations per quantifier. */
  std::unordered_map<Node, uint64_t> d_value_insts;
  /** Cache quantifiers for whose variables we have created an IC inst. */
  backtrack::unordered_set<Node> d_inv_cache;

  /** True if a lemma was sent during the current check(). */
  bool d_added_lemma;

  /** Cache configuration of option QUANT_IC. */
  bool d_opt_quant_ic;
  /** Cache configuration of option QUANT_IC_BOUNDS. */
  bool d_opt_quant_ic_bounds;
  /** Cache configuration of option QUANT_IC_FILTER. */
  bool d_opt_quant_ic_filter;
  /** Cache configuration of option QUANT_IC_VALUE_LIMIT. */
  uint64_t d_opt_quant_ic_value_limit;
  /** Cache configuration of option ABSTRACTION. */
  bool d_opt_abstraction;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);

    uint64_t& mbqi_checks;
    uint64_t& num_lemmas;
    uint64_t& num_lemma_iterations;
    util::HistogramStatistic& lemmas;

    util::TimerStatistic& time_check;
    util::TimerStatistic& time_process;
    util::TimerStatistic& time_mbqi;
  } d_stats;
};

}  // namespace quant
}  // namespace bzla

#endif
