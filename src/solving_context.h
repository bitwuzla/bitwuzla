/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVING_CONTEXT_H_INCLUDED
#define BZLA_SOLVING_CONTEXT_H_INCLUDED

#include <vector>

#include "backtrack/assertion_stack.h"
#include "backtrack/backtrackable.h"
#include "env.h"
#include "node/node.h"
#include "preprocess/preprocessor.h"
#include "rewrite/rewriter.h"
#include "solver/result.h"
#include "solver/solver_engine.h"

namespace bzla {

class ResourceTerminator;

class SolvingContext
{
 public:
  /**
   * @param nm          The associated node manager.
   * @param options     The associated options.
   * @param sat_factory The SAT solver factory.
   * @param name        The name of this context, for logging purposes.
   * @param subsolver   True if this context is a subsolver of another context.
   */
  SolvingContext(NodeManager& nm,
                 const option::Options& options,
                 sat::SatSolverFactory& sat_factory,
                 const std::string& name = "",
                 bool subsolver          = false);
  /** Destructor. */
  ~SolvingContext();

  /** Solve the current set of assertions in the context. */
  Result solve();

  /** Preprocess current set of assertions. */
  Result preprocess();

  /** Rewrite given node. */
  Node rewrite(const Node& node);

  /** Assert formula to context. */
  void assert_formula(const Node& formula);

  /**
   * Get the value of `term`.
   *
   * @note: Only valid if last solve() call returned Result::SAT.
   *
   * @param term The term to compute the value for.
   * @return The value of `term` in the current model.
   */
  Node get_value(const Node& term);

  /** @return Unsat core of previous check_sat() call. */
  std::vector<Node> get_unsat_core();
  // bool is_in_unsat_core(const Node& term) const;

  /**
   * Get interpolant I given the set of formulas A and a conjecture C such that
   * (and A (not C)) is unsat and (=> A I) and (=> I C) are valid.
   */
  Node get_interpolant(const std::vector<Node>& A, const Node& C);

  /** Increase assertion stack level. */
  void push();
  /** Decrease assertion stack level. */
  void pop();

  /** @return Context options object. */
  const option::Options& options() const;

  backtrack::AssertionView& assertions();

  const backtrack::vector<Node>& original_assertions() const;

  /** @return The solving context backtrack manager. */
  backtrack::BacktrackManager* backtrack_mgr();

  /** @return The solving context preprocessor. */
  preprocess::Preprocessor& preprocessor() { return d_preprocessor; }

  /** @return The solving context rewriter. */
  Rewriter& rewriter();

  /** @return The solving context environment. */
  Env& env();

  /** @return The solver engine. */
  const SolverEngine& solver_engine() const { return d_solver_engine; }

 private:
  /** Helper for checking models, unsat cores and interpolants after solve. */
  void check();

  void check_no_free_variables() const;

  void compute_formula_statistics(util::HistogramStatistic& stat);

  void ensure_model();

  /** Set resource terminator. */
  void set_resource_limits();

  /** Solving context environment. */
  Env d_env;
  /** Logger instance. */
  util::Logger& d_logger;

  /** Manages push()/pop() requests. */
  backtrack::BacktrackManager d_backtrack_mgr;

  /** Assertion stack of this solving context. */
  backtrack::AssertionStack d_assertions;

  /** Original input assertions added via assert_formula(). */
  backtrack::vector<Node> d_original_assertions;

  /** Do we have quantifiers in the current set of assertions? */
  backtrack::object<bool> d_have_quantifiers;

  /** The solving context preprocessor. */
  preprocess::Preprocessor d_preprocessor;

  /** Solver engine that manages all solvers. */
  SolverEngine d_solver_engine;

  /** Result of last solve() call. */
  Result d_sat_state = Result::UNKNOWN;

  /** Terminator used for timeout per solve() call. */
  std::unique_ptr<ResourceTerminator> d_resource_terminator;

  /** Indicates whether solving context is used as subsolver (e.g. MBQI). */
  bool d_subsolver;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_solve;
    util::TimerStatistic& time_ensure_model;
    util::TimerStatistic& time_check_model;
    util::TimerStatistic& time_check_unsat_core;
    util::TimerStatistic& time_check_interpolant;
    uint64_t& max_memory;
    util::HistogramStatistic& formula_kinds_pre;
    util::HistogramStatistic& formula_kinds_post;
  } d_stats;
};

}  // namespace bzla

#endif
