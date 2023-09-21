/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_SOLVER_ENGINE_H_INCLUDED
#define BZLA_SOLVER_SOLVER_ENGINE_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "backtrack/backtrackable.h"
#include "backtrack/pop_callback.h"
#include "backtrack/unordered_set.h"
#include "node/node.h"
#include "rewrite/rewriter.h"
#include "solver/array/array_solver.h"
#include "solver/bv/bv_solver.h"
#include "solver/fp/fp_solver.h"
#include "solver/fun/fun_solver.h"
#include "solver/quant/quant_solver.h"
#include "solver/result.h"
#include "solver/solver_state.h"
#include "util/statistics.h"

namespace bzla {

class SolvingContext;
class Env;

class ComputeValueException : std::exception
{
 public:
  ComputeValueException(const Node& node) : d_node(node) {}

  const Node& node() const { return d_node; }

 private:
  Node d_node;
};

class SolverEngine
{
  friend SolvingContext;

 public:
  SolverEngine(SolvingContext& context);

  /**
   * Solve current set of assertions.
   *
   * @note Should only be called by SolvingContext, hence the friend
   *       declaration.
   */
  Result solve();

  /** Get value of given term. Queries corresponding solver for value. */
  Node value(const Node& term);

  /** Get unsat core of last solve() call. */
  void unsat_core(std::vector<Node>& core) const;

  /** Add a lemma.
   *
   * @note: A solver is not allowed to send duplicate lemmas.
   */
  void lemma(const Node& lemma);

  /** @return Solver engine backtrack manager. */
  backtrack::BacktrackManager* backtrack_mgr();

  /** Ensure that we have model values for given terms. */
  void ensure_model(const std::vector<Node>& terms);

 private:
  /** Synchronize d_backtrack_mgr up to given level. */
  void sync_scope(size_t level);

  /**
   * Process current set of assertions via process_assertion().
   */
  void process_assertions();

  /**
   * Processes given assertion and distributes reachable theory leafs to
   * solvers.
   */
  void process_assertion(const Node& assertion, bool top_level, bool is_lemma);

  /** Traverse term and register terms to corresponding solvers. */
  void process_term(const Node& term);

  /** Returns true if term was registered to the corresponding theory solver. */
  bool registered(const Node& term) const;

  /** Process lemmas added via lemma(). */
  void process_lemmas();

  /** Compute value for given term. */
  Node _value(const Node& term);

  /** Cache value for given term. */
  void cache_value(const Node& term, const Node& value);

  /** Get cached model value for given term. */
  const Node& cached_value(const Node& term) const;

  /** Print statistics line. */
  void print_statistics();

  /** Counter for how often a statistics line was printed. */
  uint64_t d_num_printed_stats = 0;

  /** Model value cache for _value(). */
  std::unordered_map<Node, Node> d_value_cache;

  /** Associated solving context. */
  SolvingContext& d_context;

  /** Solver engine backtrack manager. */
  backtrack::BacktrackManager d_backtrack_mgr;
  /** Callback to sync with solving context backtrack manager on pop(). */
  backtrack::PopCallback d_pop_callback;
  /** Assertion view of unprocessed assertions. */
  backtrack::AssertionView& d_assertions;
  /** Assertion cache used by process_assertion(). */
  backtrack::unordered_set<Node> d_register_assertion_cache;
  /** Term cache used by process_term(). */
  backtrack::unordered_set<Node> d_register_term_cache;

  /** Lemmas added via lemma(). */
  std::vector<Node> d_lemmas;
  /** Indicates whether new terms were registered while solving. */
  bool d_new_terms_registered = false;
  /** Lemma cache. */
  backtrack::unordered_set<Node> d_lemma_cache;

  /** Result of latest solve() call. */
  Result d_sat_state;

  /** Indicates whether solver engine is currently in solving loop. */
  bool d_in_solving_mode;
  /**
   * Indicates whether solver engine requires additional checks for model
   * construction.
   */
  bool d_need_check = false;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_lemmas;
    uint64_t& num_lemmas_array;
    uint64_t& num_lemmas_fp;
    uint64_t& num_lemmas_fun;
    uint64_t& num_lemmas_quant;
    util::TimerStatistic& time_register_term;
    util::TimerStatistic& time_solve;
  } d_stats;

  /** Environment. */
  Env& d_env;
  /** Logger instance. */
  util::Logger& d_logger;

  /** Solver state. */
  SolverState d_solver_state;

  /** Theory solvers. */
  bv::BvSolver d_bv_solver;
  fp::FpSolver d_fp_solver;
  fun::FunSolver d_fun_solver;
  array::ArraySolver d_array_solver;
  quant::QuantSolver d_quant_solver;
};

}  // namespace bzla

#endif
