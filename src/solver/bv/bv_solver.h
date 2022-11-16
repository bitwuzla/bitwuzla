#ifndef BZLA_SOLVER_BV_BV_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_SOLVER_H_INCLUDED

#include "option/option.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solver/bv/bv_prop_solver.h"
#include "solver/bv/bv_solver_interface.h"
#include "solver/solver.h"

namespace bzla::bv {

class BvSolver : public Solver, public BvSolverInterface
{
 public:
  /** Determine if `term` is a leaf node for the bit-vector solver. */
  static bool is_leaf(const Node& term);

  BvSolver(SolverEngine& solver_engine);
  ~BvSolver();

  // Solver interface
  Node value(const Node& term) override;

  // BvSolver interface
  void register_assertion(const Node& assertion, bool top_level) override;

  Result solve() override;

 private:
  /** Query leaf assignment from subsolver. */
  Node assignment(const Node& term);

  /** Result of the last check() call. */
  Result d_sat_state = Result::UNKNOWN;

  /** Bitblast subsolver. */
  BvBitblastSolver d_bitblast_solver;
  /** Propagation-based local search subsolver. */
  BvPropSolver d_prop_solver;

  /** The currently enabled subsolver. */
  option::BvSolver d_cur_solver;
};

}  // namespace bzla::bv

#endif
