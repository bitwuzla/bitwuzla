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
  SolvingContext(const option::Options& options);

  /** Solve the current set of assertions in the context. */
  Result solve();

  /** Preprocess current set of assertions. */
  Result preprocess();

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

  /** @return Context options object. */
  const option::Options& options() const;

  backtrack::AssertionView& assertions();

  backtrack::BacktrackManager* backtrack_mgr();

  preprocess::Preprocessor& preprocessor() { return d_preprocessor; };

  Rewriter& rewriter();

 private:
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
