#ifndef BZLA_SOLVER_BV_BV_BITBLAST_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_BITBLAST_SOLVER_H_INCLUDED

#include <unordered_map>

#include "backtrack/assertion_stack.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig_bitblaster.h"
#include "sat/sat_solver.h"
#include "solver/solver.h"

namespace bzla::bv {

class BvSolver;

class BvBitblastSolver : public Solver
{
 public:
  BvBitblastSolver(SolvingContext& context);
  ~BvBitblastSolver();

  Result check() override;

  /** Query value of leaf node. */
  Node value(const Node& term) override;

  /** Recursively bit-blast `term`. */
  void bitblast(const Node& term);

  /** Return encoded bits associated with bit-blasted term. */
  const bb::AigBitblaster::Bits& bits(const Node& term) const;

 private:
  /** Sat interface used for d_cnf_encoder. */
  class BitblastSatSolver;

  void register_abstraction(const Node& term);

  /** The current set of assertions. */
  backtrack::AssertionView& d_assertion_view;
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
};

}  // namespace bzla::bv

#endif
