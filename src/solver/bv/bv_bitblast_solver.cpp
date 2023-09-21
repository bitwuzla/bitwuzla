/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_bitblast_solver.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "sat/sat_solver_factory.h"
#include "solver/bv/bv_solver.h"
#include "solving_context.h"

namespace bzla::bv {

using namespace bzla::node;

/** Sat solver wrapper for AIG encoder. */
class BvBitblastSolver::BitblastSatSolver : public bb::SatInterface
{
 public:
  BitblastSatSolver(sat::SatSolver& solver) : d_solver(solver) {}

  void add(int64_t lit) override { d_solver.add(lit); }

  void add_clause(const std::initializer_list<int64_t>& literals) override
  {
    for (int64_t lit : literals)
    {
      d_solver.add(lit);
    }
    d_solver.add(0);
  }

  bool value(int64_t lit) override
  {
    return d_solver.value(lit) == 1 ? true : false;
  }

 private:
  sat::SatSolver& d_solver;
};

/* --- BvBitblastSolver public ---------------------------------------------- */

BvBitblastSolver::BvBitblastSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_assumptions(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN),
      d_stats(env.statistics(), "solver::bv::bitblast::")
{
  d_sat_solver.reset(sat::new_sat_solver(env.options().sat_solver()));
  d_bitblast_sat_solver.reset(new BitblastSatSolver(*d_sat_solver));
  d_cnf_encoder.reset(new bb::AigCnfEncoder(*d_bitblast_sat_solver));
}

BvBitblastSolver::~BvBitblastSolver() {}

Result
BvBitblastSolver::solve()
{
  d_sat_solver->configure_terminator(d_env.terminator());

  for (const Node& assumption : d_assumptions)
  {
    const auto& bits = d_bitblaster.bits(assumption);
    assert(!bits.empty());
    d_sat_solver->assume(bits[0].get_id());
  }

  util::Timer timer(d_stats.time_sat);
  d_last_result = d_sat_solver->solve();
  return d_last_result;
}

void
BvBitblastSolver::register_assertion(const Node& assertion,
                                     bool top_level,
                                     bool is_lemma)
{
  // If unsat cores are enabled, all assertions are assumptions except lemmas.
  if (d_env.options().produce_unsat_cores() && !is_lemma)
  {
    top_level = false;
  }

  if (!top_level)
  {
    d_assumptions.push_back(assertion);
  }

  {
    util::Timer timer(d_stats.time_bitblast);
    d_bitblaster.bitblast(assertion);
  }
  const auto& bits = d_bitblaster.bits(assertion);
  assert(!bits.empty());

  {
    util::Timer timer(d_stats.time_encode);
    d_cnf_encoder->encode(bits[0], top_level);
  }
  update_statistics();
}

Node
BvBitblastSolver::value(const Node& term)
{
  assert(BvSolver::is_leaf(term));
  assert(term.type().is_bool() || term.type().is_bv());

  const auto& bits = d_bitblaster.bits(term);
  const Type& type = term.type();
  NodeManager& nm  = NodeManager::get();

  // Return default value if not bit-blasted
  if (bits.empty())
  {
    return utils::mk_default_value(type);
  }

  if (type.is_bool())
  {
    return nm.mk_value(d_cnf_encoder->value(bits[0]) == 1);
  }

  BitVector val(type.bv_size());
  for (size_t i = 0, size = bits.size(); i < size; ++i)
  {
    val.set_bit(size - 1 - i, d_cnf_encoder->value(bits[i]) == 1);
  }
  return nm.mk_value(val);
}

void
BvBitblastSolver::unsat_core(std::vector<Node>& core) const
{
  assert(d_last_result == Result::UNSAT);
  assert(d_env.options().produce_unsat_cores());

  for (const Node& assumption : d_assumptions)
  {
    const auto& bits = d_bitblaster.bits(assumption);
    assert(bits.size() == 1);
    if (d_sat_solver->failed(bits[0].get_id()))
    {
      core.push_back(assumption);
    }
  }
}

/* --- BvBitblastSolver private --------------------------------------------- */

void
BvBitblastSolver::update_statistics()
{
  d_stats.num_aig_ands     = d_bitblaster.num_aig_ands();
  d_stats.num_aig_consts   = d_bitblaster.num_aig_consts();
  d_stats.num_aig_shared   = d_bitblaster.num_aig_shared();
  auto& cnf_stats          = d_cnf_encoder->statistics();
  d_stats.num_cnf_vars     = cnf_stats.num_vars;
  d_stats.num_cnf_clauses  = cnf_stats.num_clauses;
  d_stats.num_cnf_literals = cnf_stats.num_literals;
}

BvBitblastSolver::Statistics::Statistics(util::Statistics& stats,
                                         const std::string& prefix)
    : time_sat(
        stats.new_stat<util::TimerStatistic>(prefix + "sat::time_solve")),
      time_bitblast(
          stats.new_stat<util::TimerStatistic>(prefix + "aig::time_bitblast")),
      time_encode(
          stats.new_stat<util::TimerStatistic>(prefix + "cnf::time_encode")),
      num_aig_ands(stats.new_stat<uint64_t>(prefix + "aig::num_ands")),
      num_aig_consts(stats.new_stat<uint64_t>(prefix + "aig::num_consts")),
      num_aig_shared(stats.new_stat<uint64_t>(prefix + "aig::num_shared")),
      num_cnf_vars(stats.new_stat<uint64_t>(prefix + "cnf::num_vars")),
      num_cnf_clauses(stats.new_stat<uint64_t>(prefix + "cnf::num_clauses")),
      num_cnf_literals(stats.new_stat<uint64_t>(prefix + "cnf::num_literals"))
{
}

}  // namespace bzla::bv
