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
#include "bitblast/aig_bitblaster.h"
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

class AigBitblaster;
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
   * Get interpolant I of a formulas A and B such that
   * (and A B) is unsat and (=> A I) and (=> I (not B)) are valid.
   *
   * For computing the interpolant, we require that the satisfiability of
   * (and A B) has been determined as unsat. That is,
   *   - A and B must have been asserted
   *   - and its satisfiability must have been determined via solve() as unsat
   *     before calling this function.
   *
   * @param A The set of formulas A, given as preprocessed assertions.
   * @param B The set of formulas B, given as preprocessed assertions.
   *
   * @note In case the abstraction module is enabled, sets A and B must
   *       contain the abstracted version of assertions with abstracted terms.
   *       This is necessary because for labeling, the interpolation engine
   *       needs to process the assertions that have actually been processed
   *       during solving.
   */
  Node interpolant(const std::vector<Node>& A, const std::vector<Node>& B);

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
   * Label associated SAT clauses in a given set of nodes.
   * @param clause_labels The clause labels map to add to. Maps AIG ids to
   *                      clause labels.
   * @param nodes         The nodes.
   * @param kind          The clause kind to label with.
   */
  void label_clauses(
      std::unordered_map<int64_t, sat::interpolants::ClauseKind>& clause_labels,
      const std::vector<Node>& nodes,
      sat::interpolants::ClauseKind kind);
  /**
   * Label bit-vector consts in `node`.
   *
   * Labels all SAT variables corresponding and associated with to bit-vector
   * consts with the given kind (if yet unlabeled) or as VariableKind::GLOBAL if
   * they occur both in A and B. This includes SAT variables corresponding to
   * nodes that are associated with the consts occuring in `node` since we have
   * to prevent non-shared consts to be pulled into the interpolant.
   *
   * @param var_labels The variable labels map to add to. Maps AIG ids to
   *                   variable labels.
   * @param node       The node.
   * @param kind       The variable kind to label with.
   */
  void label_vars(
      std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
      const Node& node,
      sat::interpolants::VariableKind kind);
  void label_var(
      std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
      const bitblast::AigBitblaster::Bits& bits,
      sat::interpolants::VariableKind kind);
  /**
   * Label unlabeled SAT variables occuring in a lemma depending on which kind
   * the non-GLOBAL variables in the lemma are assigned to.
   *
   * That is,
   * * A, S: labeled as A
   * * B, S: labeled as B
   * * S: labeled as A
   *
   * @note Currently, we do not allow lemmas with "mixed" occurrences, i.e.,
   *       occurences of both A and B local variables.
   *
   * @param var_labels    The variable labels map.
   * @param clause_labels The clause labels map.
   * @param node          The lemma.
   */
  void label_lemma(
      std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
      std::unordered_map<int64_t, sat::interpolants::ClauseKind>& clause_labels,
      const Node& node);

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
  std::unique_ptr<AigBitblaster> d_bitblaster;

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
};

}  // namespace bv
}  // namespace bzla

#endif
