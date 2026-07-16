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
    MBQI_INST,
    MBQI_INST_INV,
    SKOLEMIZATION,
  };

  /**
   * Determine if given term is a leaf node for other solvers than the
   * quant solver.
   * @param term The term to query.
   */
  static bool is_theory_leaf(const Node& term);

  QuantSolver(Env& env, SolverState& state);
  ~QuantSolver();

  bool check() override;

  Node value(const Node& term) override;

  void register_term(const Node& term) override;
  void register_assertion(const Node& assertion);

 private:
  void lemma(const Node& lemma, LemmaKind kind);

  Node instantiate(const Node& q, const std::unordered_map<Node, Node>& substs);
  Node substitute(const Node& n, const std::unordered_map<Node, Node>& substs);
  // void add_instance(const Node& q, const Node& inst);

  const Node& inst_const(const Node& q);
  const Node& skolem_const(const Node& q);
  const Node& ce_const(const Node& q);

  Node skolemize(const Node& q);

  const Node& skolemization_lemma(const Node& q);
  const Node& value_inst_lemma(const Node& q);

  void process(const Node& q);

  bool mbqi_check(const std::vector<Node>& to_check);
  const Node& mbqi_inst(const Node& q);
  void mbqi_lemma(
      const Node& q,
      const std::unordered_map<Node, Node>& model_values,
      const std::unordered_map<Node, std::vector<Node>>& ground_terms);
  Node symbolic_term(
      const Node& term,
      const std::unordered_map<Node, std::vector<Node>>& ground_terms);

  /**
   * Try to find an inverse term instantiation for var.
   * @param q            The active quantified formula.
   * @param var          The variable to find the instantiation for.
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
                    const Node& var,
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

  bv::BvInverter d_bv_inverter;

  backtrack::vector<Node> d_quantifiers;
  backtrack::vector<Node> d_assertions;
  backtrack::unordered_set<Node> d_process_cache;
  backtrack::vector<Node> d_consts;
  backtrack::vector<Node> d_ground_terms;
  std::unordered_map<uint64_t, uint64_t> d_num_selected;
  std::vector<uint64_t> d_selected_terms;

  std::unordered_map<Node, Node> d_ce_consts;
  std::unordered_map<Node, Node> d_instantiation_consts;
  std::unordered_map<Node, Node> d_skolem_consts;

  backtrack::unordered_map<Node, Node> d_skolemization_lemmas;

  std::unique_ptr<SolvingContext> d_mbqi_solver;
  std::unordered_map<Node, Node> d_mbqi_inst;
  backtrack::unordered_set<Node> d_lemma_cache;

  /** Maps the number of value instantiations per quantified variable. */
  std::unordered_map<Node, uint64_t> d_value_insts;
  /** Cache quantified variables for which we have created an IC inst. */
  backtrack::unordered_set<Node> d_inv_cache;

  bool d_added_lemma;

  /** Cache configuration of option QUANT_IC. */
  bool d_opt_quant_ic;
  /** Cache configuration of option QUANT_IC_BOUNDS. */
  bool d_opt_quant_ic_bounds;
  /** Cache configuration of option QUANT_IC_FILTER. */
  bool d_opt_quant_ic_filter;
  /** Cache configuration of option QUANT_IC_VALUE_LIMIT. */
  uint64_t d_opt_quant_ic_value_limit;

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
