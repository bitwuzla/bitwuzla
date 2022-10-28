#ifndef BZLA_SOLVING_CONTEXT_H_INCLUDED
#define BZLA_SOLVING_CONTEXT_H_INCLUDED

#include <unordered_set>
#include <vector>

#include "backtrack/assertion_stack.h"
#include "backtrack/backtrackable.h"
#include "node/node.h"
#include "option/option.h"
#include "preprocess/preprocessor.h"
#include "rewrite/rewriter.h"
#include "solver/bv/bv_solver.h"
#include "solver/result.h"

namespace bzla {

class SolvingContext
{
 public:
  SolvingContext();

  /** Solve the current set of assertions in the context. */
  Result solve();

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

  void push();
  void pop();

  // std::vector<Node>& get_unsat_core();
  // bool is_in_unsat_core(const Node& term) const;

  option::Options& options();

  backtrack::AssertionView& assertions();

  backtrack::BacktrackManager* backtrack_mgr();

  Rewriter& rewriter();

 private:
  void register_assertion(const Node& formula);

  option::Options d_options;

  backtrack::BacktrackManager d_backtrack_mgr;
  backtrack::AssertionStack d_assertions;

  preprocess::Preprocessor d_preprocessor;
  Rewriter d_rewriter;

  /** Bit-vector solver. */
  bv::BvSolver d_bv_solver;

  /** Result of last solve() call. */
  Result d_sat_state = Result::UNKNOWN;
};

}  // namespace bzla

#endif
