/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_BV_BITBLAST_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_BITBLAST_SOLVER_H_INCLUDED

#include "backtrack/backtrackable.h"
#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig/aig_printer.h"
#include "sat/sat_solver.h"
#include "solver/bv/aig_bitblaster.h"
#include "solver/bv/bv_solver_interface.h"
#include "solver/solver.h"
#include "util/statistics.h"

namespace bzla {

namespace sat::interpolants {
class Tracer;
}

namespace bv {

class BvSolver;
class BvInterpolator;

class BvBitblastSolver : public Solver,
                         public BvSolverInterface,
                         public backtrack::Backtrackable
{
 public:
  BvBitblastSolver(Env& env, SolverState& state);
  ~BvBitblastSolver();

  Result solve() override;

  void register_assertion(const Node& assertion,
                          bool top_level,
                          bool is_lemma) override;

  /** Query value of leaf node. */
  Node value(const Node& term) override;

  /** Get unsat core of last solve() call. */
  void unsat_core(std::vector<Node>& core) const override;

  /** Get AIG bit-blaster instance. */
  AigBitblaster& bitblaster() { return d_bitblaster; }

  /** Get statistics. */
  const auto& statistics() const { return d_stats; }

  void push() override {}
  void pop() override;

  sat::interpolants::Tracer* tracer() { return d_tracer.get(); }

  /**
   * Get interpolant I of formulas A and B such that
   * (and A B) is unsat and (=> A I) and (=> I (not B)) are valid.
   *
   * For computing the interpolant, we require that the satisfiability of
   * (and A B) has been determined as unsat. That is,
   *   - A and B must have been asserted
   *   - and its satisfiability must have been determined via solve() as unsat
   *     before calling this function.
   *
   * @param ppA The set of formulas A, given as preprocessed assertions.
   * @param ppB The set of formulas B, given as preprocessed assertions.
   *
   * @note In case the abstraction module is enabled, sets ppA and ppB must
   *       contain the abstracted version of assertions with abstracted terms.
   *       This is necessary because for labeling, the interpolation engine
   *       needs to process the assertions that have actually been processed
   *       during solving.
   */
  Node interpolant(const std::vector<Node>& ppA, const std::vector<Node>& ppB);

 private:
  /** Initialize sat solver and bitblast infrastructure. */
  void init_sat_solver();
  /** Update AIG and CNF statistics. */
  void update_statistics();

  /** Sat interface used for d_cnf_encoder. */
  class BitblastSatSolver;
  /** Sat interface used for d_cnf_encoder when producing interpolants. */
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
  std::unique_ptr<sat::SatSolver> d_sat_solver;
  /** SAT solver interface for CNF encoder, which wraps `d_sat_solver`. */
  std::unique_ptr<bitblast::SatInterface> d_bitblast_sat_solver;

  /** Interpolation subsolver. */
  std::unique_ptr<BvInterpolator> d_bv_interpolator;

  /** Result of last solve() call. */
  Result d_last_result;

  /** Option to print AIGER/CNF to file. */
  bool d_opt_print_aig;
  /** The AIG printer. */
  bitblast::aig::AigPrinter d_aig_printer;

  /** True if produce-interpolants is enabled. */
  bool d_produce_interpolants = false;
  /** Interpolation proof tracer. */
  std::unique_ptr<sat::interpolants::Tracer> d_tracer;
  /** True to reset SAT solver on each solve() call. */
  bool d_reset_sat = false;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    util::TimerStatistic& time_sat;
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
