/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_BV_INTERPOLATION_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_INTERPOLATION_SOLVER_H_INCLUDED

#include <unordered_map>

#include "backtrack/assertion_stack.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "sat/sat_solver.h"
#include "solver/bv/aig_bitblaster.h"
#include "solver/bv/bv_solver_interface.h"
#include "solver/solver.h"
#include "util/statistics.h"

namespace CaDiCraig {
class CraigTracer;
}

namespace bzla {

namespace sat {
class Cadical;
}

namespace bv {

class BvSolver;

class BvInterpolationSolver : public Solver, public BvSolverInterface
{
 public:
  BvInterpolationSolver(Env& env, SolverState& state);
  ~BvInterpolationSolver();

  Node interpolant(const std::vector<Node>& A, const Node& C) override;

  void register_assertion(const Node& assertion,
                          bool top_level,
                          bool is_lemma) override;

  /** Get statistics. */
  const auto& statistics() const { return d_stats; }

  /** The following are unsupported and should never be called. */
  Result solve() override;
  Node value(const Node& term) override;
  void unsat_core(std::vector<Node>& core) const override;

 private:
  /** Update AIG and CNF statistics. */
  void update_statistics();

  /**
   * Helper to map known SAT variables to nodes.
   * @param vars      The known SAT vars occurring in the interpolant.
   */
  std::unordered_map<int64_t, Node> map_vars_to_node(
      const std::unordered_set<int64_t>& vars) const;

  /** Sat interface used for d_cnf_encoder. */
  class InterpolationSatSolver;

  /** The current set of assertions. */
  backtrack::vector<Node> d_assertions;
  /** The current set of assumptions. */
  backtrack::vector<Node> d_assumptions;

  /** AIG bit-blaster. */
  AigBitblaster d_bitblaster;

  /** CNF encoder for AIGs. */
  std::unique_ptr<bitblast::AigCnfEncoder> d_cnf_encoder;
  /** SAT solver used for solving bit-blasted formula. */
  std::unique_ptr<sat::Cadical> d_sat_solver;
  std::unique_ptr<CaDiCraig::CraigTracer> d_craig_tracer;
  /** SAT solver interface for CNF encoder, which wraps `d_sat_solver`. */
  std::unique_ptr<InterpolationSatSolver> d_interpol_sat_solver;
  /** Result of last solve() call. */
  Result d_last_result;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    util::TimerStatistic& time_interpol;
    util::TimerStatistic& time_bitblast;
    util::TimerStatistic& time_encode;
    uint64_t& num_aig_ands;
    uint64_t& num_aig_consts;
    uint64_t& num_aig_shared;
    uint64_t& num_cnf_vars;
    uint64_t& num_cnf_clauses;
    uint64_t& num_cnf_literals;
  } d_stats;
};

}  // namespace bv
}  // namespace bzla

#endif
