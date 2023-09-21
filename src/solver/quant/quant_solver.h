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

#include "backtrack/unordered_set.h"
#include "backtrack/unordered_map.h"
#include "backtrack/vector.h"
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
  Node mbqi_lemma(const Node& q);

  backtrack::vector<Node> d_quantifiers;
  backtrack::vector<Node> d_assertions;
  backtrack::unordered_set<Node> d_process_cache;
  backtrack::vector<Node> d_consts;
  backtrack::vector<Node> d_ground_terms;

  std::unordered_map<Node, Node> d_ce_consts;
  std::unordered_map<Node, Node> d_instantiation_consts;
  std::unordered_map<Node, Node> d_skolem_consts;

  backtrack::unordered_map<Node, Node> d_skolemization_lemmas;

  std::unique_ptr<SolvingContext> d_mbqi_solver;
  std::unordered_map<Node, Node> d_mbqi_inst;
  backtrack::unordered_set<Node> d_lemma_cache;

  bool d_added_lemma;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);

    uint64_t& mbqi_checks;
    uint64_t& num_lemmas;
    util::HistogramStatistic& lemmas;

    util::TimerStatistic& time_check;
    util::TimerStatistic& time_process;
    util::TimerStatistic& time_mbqi;
  } d_stats;
};

}  // namespace quant
}  // namespace bzla

#endif
