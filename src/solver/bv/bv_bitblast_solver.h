#ifndef BZLA_SOLVER_BV_BV_BITBLAST_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_BITBLAST_SOLVER_H_INCLUDED

#include <unordered_map>

#include "backtrack/assertion_stack.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig_bitblaster.h"
#include "sat/sat_solver.h"
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

  /** Recursively bit-blast `term`. */
  void bitblast(const Node& term);

  /** Return encoded bits associated with bit-blasted term. */
  const bb::AigBitblaster::Bits& bits(const Node& term) const;

  /** Get unsat core of last solve() call. */
  void unsat_core(std::vector<Node>& core) const override;

 private:
  /** Update AIG and CNF statistics. */
  void update_statistics();

  /** Sat interface used for d_cnf_encoder. */
  class BitblastSatSolver;

  /** The current set of assertions. */
  backtrack::vector<Node> d_assumptions;

  /** AIG Bit-blaster. */
  bb::AigBitblaster d_bitblaster;
  /** Cached to store bit-blasted terms and their encoded bits. */
  std::unordered_map<Node, bb::AigBitblaster::Bits> d_bitblaster_cache;
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
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_sat;
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
