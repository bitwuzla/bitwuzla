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

  /** Add a lemma.
   *
   * @note: A solver is not allowed to send duplicate lemmas.
   */
  void lemma(const Node& lemma);

  /** @return Solver engine backtrack manager. */
  backtrack::BacktrackManager* backtrack_mgr();

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
  void process_assertion(const Node& assertion, bool top_level);

  /** Traverse term and register terms to corresponding solvers. */
  void process_term(const Node& term);

  /** Process lemmas added via lemma(). */
  void process_lemmas();

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
  /** Lemma cache. */
  std::unordered_set<Node> d_lemma_cache;

  /** Result of latest solve() call. */
  Result d_sat_state;

  /** Indicates whether solver engine is currently in solving loop. */
  bool d_in_solving_mode;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    uint64_t& num_lemmas;
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
