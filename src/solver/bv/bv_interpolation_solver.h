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

#include <cstdint>
#include <unordered_set>

#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "sat/interpolants/tracer_kinds.h"
#include "solver/bv/bv_solver_interface.h"
#include "solver/solver.h"
#include "util/statistics.h"

namespace CaDiCraig {
class CraigTracer;
}

namespace bzla {

namespace sat {
class Cadical;
namespace interpolants {
class Tracer;
}
}

namespace bv {

class BvSolver;
class InterpolationBitblaster;

class BvInterpolationSolver : public Solver, public BvSolverInterface
{
 public:
  /** Sat interface used for d_cnf_encoder. */
  class InterpolationSatSolver;

  BvInterpolationSolver(Env& env, SolverState& state);
  ~BvInterpolationSolver();

  void register_assertion(const Node& assertion,
                          bool top_level,
                          bool is_lemma) override;
  Result solve() override;
  Node value(const Node& term) override;
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

  /** Get statistics. */
  const auto& statistics() const { return d_stats; }

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    util::TimerStatistic& time_sat;
    util::TimerStatistic& time_interpol;
    util::TimerStatistic& time_bitblast;
    util::TimerStatistic& time_label;
    util::TimerStatistic& time_encode;
    uint64_t& size_interpolant;
    uint64_t& bb_num_aig_ands;
    uint64_t& bb_num_aig_consts;
    uint64_t& bb_num_aig_shared;
    uint64_t& bb_num_cnf_vars;
    uint64_t& bb_num_cnf_clauses;
    uint64_t& bb_num_cnf_literals;
  } d_stats;

 private:
  /** Update AIG and CNF statistics. */
  void update_statistics();

  /**
   * Label bit-vector consts in node.
   * @param node The node.
   * @param kind The SAT variable kind to label with.
   */
  void label(const Node& node, sat::interpolants::VariableKind kind);

  /**
   * Log current state of bitblaster cache when given log level is enabled.
   * @param level The log level.
   */
  void log_bitblaster_cache(uint64_t level) const;

  /** The current set of assertions. */
  backtrack::vector<Node> d_assertions;
  /** The current set of assumptions. */
  backtrack::vector<Node> d_assumptions;
  /** The current set of lemmas. */
  backtrack::unordered_set<Node> d_lemmas;

  /** AIG bit-blaster. */
  std::unique_ptr<InterpolationBitblaster> d_bitblaster;

  /** CNF encoder for AIGs. */
  std::unique_ptr<bitblast::AigCnfEncoder> d_cnf_encoder;
  /** SAT solver used for solving bit-blasted formula. */
  std::unique_ptr<sat::Cadical> d_sat_solver;
  /** Interpolation tracer. */
  std::unique_ptr<sat::interpolants::Tracer> d_tracer;
  /** SAT solver interface for CNF encoder, which wraps `d_sat_solver`. */
  std::unique_ptr<InterpolationSatSolver> d_interpol_sat_solver;
  /** Result of last solve() call. */
  Result d_last_result;

  /** Cache of bit-vector const labeling. */
  std::unordered_map<Node, sat::interpolants::VariableKind> d_consts_to_kinds;
  /** Cache of SAT variable labeling. */
  std::unordered_map<int64_t, sat::interpolants::VariableKind>
      d_sat_vars_to_kinds;
};

}  // namespace bv
}  // namespace bzla

#endif
