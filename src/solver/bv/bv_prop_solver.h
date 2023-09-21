/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_BV_PROP_SOLVER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_PROP_SOLVER_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "backtrack/backtrackable.h"
#include "ls/ls_bv.h"
#include "node/node_ref_vector.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solver/bv/bv_solver_interface.h"
#include "util/statistics.h"

namespace bzla {

class LocalSearchBV;

namespace bv {

class BvPropSolver : public Solver, public BvSolverInterface
{
 public:
  BvPropSolver(Env& env, SolverState& state, BvBitblastSolver& bb_solver);
  ~BvPropSolver();

  Result solve() override;

  void register_assertion(const Node& assertion,
                          bool top_level,
                          bool is_lemma) override;

  Node value(const Node& term) override;

  /** Get unsat core of last solve() call. */
  void unsat_core(std::vector<Node>& core) const override;

 private:
  /** Backtrack manager to sync push/pop with local search engine. */
  class LsBacktrack : public backtrack::Backtrackable
  {
   public:
    LsBacktrack(backtrack::BacktrackManager* mgr, bzla::ls::LocalSearchBV* ls)
        : Backtrackable(mgr), d_ls(ls)
    {
    }
    void push() override { d_ls->push(); }
    void pop() override { d_ls->pop(); }
    bzla::ls::LocalSearchBV* d_ls = nullptr;
  };

  /**
   * Helper to create LocalSearchBV bit-vector node representation of given
   * node. Maps `node` to resulting LS bit-vector node id in `d_node_map`.
   * @param node The node to create a LS bit-vector node representation for.
   * @return The id of the created LS bit-vector node.
   */
  uint64_t mk_node(const Node& node);

  /**
   * Print current progress of LocalSearchBV.
   */
  void print_progress() const;

  /**
   * The associated bit-blasting solver, for bit-blasting to determine
   * constant bits information. We utilize the bit-blaster of the BB solver
   * to avoid redundant bit-blasting work.
   */
  BvBitblastSolver& d_bb_solver;
  /** The local search engine. */
  std::unique_ptr<bzla::ls::LocalSearchBV> d_ls;
  /** The backtrack manager for the local search engine. */
  LsBacktrack d_ls_backtrack;
  /** Map Bitwuzla node to LocalSearchBV bit-vector node id. */
  std::unordered_map<Node, uint64_t> d_node_map;
  /** Map LocalSearchBV root id to Bitwuzla node for unsat cores. */
  std::unordered_map<uint64_t, Node> d_root_id_node_map;
  /** True to enable constant bits propagation. */
  bool d_use_const_bits = false;
  /** True to use sign_extend nodes for concats that represent sign_extends. */
  bool d_use_sext = false;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_checks;
    uint64_t& num_assertions;
    uint64_t& num_bits_fixed;
    uint64_t& num_bits_total;
    uint64_t& num_moves;
    uint64_t& num_props;
    uint64_t& num_props_inv;
    uint64_t& num_props_cons;
    uint64_t& num_updates;
    uint64_t& num_conflicts;
#ifndef NDEBUG
    util::HistogramStatistic& num_props_inv_per_kind;
    util::HistogramStatistic& num_props_cons_per_kind;
    util::HistogramStatistic& num_props_conflicts_per_kind;
#endif
    util::TimerStatistic& time_check;
  } d_stats;
};
}  // namespace bv
}  // namespace bzla
#endif
