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

#include <unordered_map>

#include "backtrack/assertion_stack.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "sat/sat_solver.h"
#include "solver/bv/aig_bitblaster.h"
#include "solver/bv/bv_solver_interface.h"
#include "solver/solver.h"
#include "util/statistics.h"

namespace bzla::bv {

class BvSolver;

class BvBitblastSolver : public Solver, public BvSolverInterface
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

 private:
  /** Update AIG and CNF statistics. */
  void update_statistics();

  /** Sat interface used for d_cnf_encoder. */
  class BitblastSatSolver;

  /** The current set of assertions. */
  backtrack::vector<Node> d_assumptions;

  /** AIG bit-blaster. */
  AigBitblaster d_bitblaster;

  /** CNF encoder for AIGs. */
  std::unique_ptr<bb::AigCnfEncoder> d_cnf_encoder;
  /** SAT solver used for solving bit-blasted formula. */
  std::unique_ptr<sat::SatSolver> d_sat_solver;
  /** SAT solver interface for CNF encoder, which wraps `d_sat_solver`. */
  std::unique_ptr<BitblastSatSolver> d_bitblast_sat_solver;
  /** Result of last solve() call. */
  Result d_last_result;

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

}  // namespace bzla::bv

#endif
