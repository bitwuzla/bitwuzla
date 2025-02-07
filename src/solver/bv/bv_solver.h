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
#include "solver/bv/bv_interpolation_solver.h"
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
  void unsat_core(std::vector<Node>& core) const override;

  /**
   * Get interpolant I of a set of formulas A and a conjecture C such that
   * (and A (not C)) is unsat and (=> A I) and (=> I C) are valid.
   *
   * Note that our SAT interpolation tracer interface defines interpolant I as
   * (A -> I) and (I -> not B), for formulas A, B with (and A B) unsat. That is,
   * in our word-level interface (in SolvingContext), C = not B.
   *
   * For computing the interpolant, we first need to determine unsat of
   * (and A (not C)). That is,
   *   - A and (not C) must have been asserted
   *   - C must have been cached via SolverEngine::cache_interpol_conj_assertion
   *     as the (preprocessed) assertion B = (not C) on the assertion stack
   *   - and its satisfiability must have been determined via solver() as unsat
   * before calling this function.
   */
  Node interpolant();

  /** Get overall BV solver statistics. */
  const auto& statistics() const { return d_stats; }

  /** Get bitblast solver statistics. */
  const auto& statistics_bitblast() const
  {
    return d_bitblast_solver.statistics();
  }

  option::BvSolver cur_solver() const { return d_cur_solver; }

  BvInterpolationSolver* interpol_solver() const
  {
    return d_interpol_solver.get();
  }

 private:
  /** Result of the last check() call. */
  Result d_sat_state = Result::UNKNOWN;

  /** Bitblast subsolver. */
  BvBitblastSolver d_bitblast_solver;
  /** Propagation-based local search subsolver. */
  std::unique_ptr<BvPropSolver> d_prop_solver;
  /** Interpolation subsolver. */
  std::unique_ptr<BvInterpolationSolver> d_interpol_solver;

  /**
   * The currently enabled subsolver. Used to determine which solver to ask
   * for model values and unsat cores.
   */
  option::BvSolver d_cur_solver;
  /** Cache optiont :produce-interpolants. */
  bool d_produce_interpolants;
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
