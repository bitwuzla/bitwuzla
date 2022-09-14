#ifndef BZLA_SOLVING_CONTEXT_H_INCLUDED
#define BZLA_SOLVING_CONTEXT_H_INCLUDED

#include <unordered_set>
#include <vector>

#include "node/node.h"
#include "solver/bv/bv_solver.h"
#include "solver/result.h"

namespace bzla {

class SolvingContext
{
  friend class bv::BvSolver;  // TODO: Temporary until we have proper assertion
                              // interface

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

  // void push();
  // void pop();
  // std::vector<Node>& get_unsat_core();
  // bool is_in_unsat_core(const Node& term) const;

 private:
  /** Currently asserted formulas. */
  std::vector<Node> d_assertions;
  /** Cache of currently asserted formulas. */
  std::unordered_set<Node> d_assertions_cache;

  /** Result of last solve() call. */
  Result d_sat_state = Result::UNKNOWN;

  /** Bit-vector solver. */
  bv::BvSolver d_bv_solver;
};

}  // namespace bzla

#endif
