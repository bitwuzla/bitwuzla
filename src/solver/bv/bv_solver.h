#ifndef BZLA_SOLVER_BV_BV_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_SOLVER_H_INCLUDED

#include "option/option.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solver/bv/bv_prop_solver.h"
#include "solver/bv/bv_solver_interface.h"
#include "solver/solver.h"
#include "util/statistics.h"

namespace bzla::bv {

class BvSolver : public Solver, public BvSolverInterface
{
 public:
  /**
   * Determine if given term is a leaf node for the bit-vector solver, i.e.,
   * a term of Boolean or bit-vector type that belongs to any of the other
   * theories.
   * @param term The term to query.
   */
  static bool is_leaf(const Node& term);

  BvSolver(Env& env, SolverState& state);
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

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    uint64_t& num_checks;
    util::TimerStatistic& time_check;
  } d_stats;
};

}  // namespace bzla::bv

#endif
