/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
  void register_assertion(const Node& assertion,
                          bool top_level,
                          bool is_lemma) override;

  Result solve() override;

  /** Get unsat core of last solve() call. */
  void unsat_core(std::vector<Node>& core) const override;

  /** Get overall BV solver statistics. */
  const auto& statistics() const { return d_stats; }

  /** Get bitblast solver statistics. */
  const auto& statistics_bitblast() const
  {
    return d_bitblast_solver.statistics();
  }

  option::BvSolver cur_solver() const { return d_cur_solver; }

 private:
  /** Result of the last check() call. */
  Result d_sat_state = Result::UNKNOWN;

  /** Bitblast subsolver. */
  BvBitblastSolver d_bitblast_solver;
  /** Propagation-based local search subsolver. */
  BvPropSolver d_prop_solver;

  /**
   * The currently enabled subsolver. Used to determine which solver to ask
   * for model values and unsat cores.
   */
  option::BvSolver d_cur_solver;
  /**
   * The subsolver configured via options. Used to determine to which
   * solver to send registered terms.
   */
  const option::BvSolver d_solver_mode;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    uint64_t& num_checks;
    uint64_t& num_assertions;
    util::TimerStatistic& time_check;
  } d_stats;
};

}  // namespace bzla::bv

#endif
