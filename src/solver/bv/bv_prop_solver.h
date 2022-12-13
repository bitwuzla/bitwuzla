#ifndef BZLA_SOLVER_BV_BV_PROP_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_PROP_SOLVER_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "ls/ls_bv.h"
#include "node/node_ref_vector.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solver/bv/bv_solver_interface.h"

namespace bzla {

class LocalSearchBV;

namespace bv {

class BvPropSolver : public Solver, public BvSolverInterface
{
 public:
  BvPropSolver(Env& env, SolverState& state, BvBitblastSolver& bb_solver);
  ~BvPropSolver();

  Result solve() override;

  void register_assertion(const Node& assertion, bool top_level) override;

  Node value(const Node& term) override;

 private:
  struct
  {
    uint64_t d_nfixed_bits = 0;
    uint64_t d_ntotal_bits = 0;
  } d_statistics;

  /**
   * Helper to create LocalSearchBV bit-vector node representation of given
   * node. Maps `node` to resulting LS bit-vector node id in `d_node_map`.
   * @param node The node to create a LS bit-vector node representation for.
   * @return The id of the created LS bit-vector node.
   */
  uint64_t mk_node(const Node& node);

  /**
   * The associated bit-blasting solver, for bit-blasting to determine
   * constant bits information. We utilize the bit-blaster of the BB solver
   * to avoid redundant bit-blasting work.
   */
  BvBitblastSolver& d_bb_solver;
  /** The local search engine. */
  std::unique_ptr<bzla::ls::LocalSearchBV> d_ls;
  /** Map Bitwuzla node to LocalSearchBV bit-vector node id. */
  std::unordered_map<Node, uint64_t> d_node_map;
  /** True to enable constant bits propagation. */
  bool d_use_const_bits = false;
  /** True to use sign_extend nodes for concats that represent sign_extends. */
  bool d_use_sext = false;
};
}  // namespace bv
}  // namespace bzla
#endif
