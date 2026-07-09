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
#include "env.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "option/option.h"
#include "sat/distinct_n_propagator.h"
#include "sat/cadical.h"
#include "sat/distinct_decision_heuristic.h"
#include "sat/eq_decision_heuristic.h"
#include "sat/interpolants/tracer.h"
#include "sat/sat_solver_factory.h"
#include "solver/bv/bv_interpolator.h"
#include "solver/bv/bv_solver.h"

namespace bzla::bv {

using namespace bzla::node;

/* --- BitblastSatSolver --------------------------------------------------- */

/** Sat solver wrapper for AIG encoder for bitblasting, no interpolation. */
class BvBitblastSolver::BitblastSatSolver : public bitblast::SatInterface
{
 public:
  BitblastSatSolver(sat::SatSolver& solver) : d_solver(solver) {}

  int32_t new_var() override { return d_solver.new_var(); }

  void add(int64_t lit, int64_t aig_id) override
  {
    (void) aig_id;
    d_solver.add(lit);
  }

  void add_clause(const std::initializer_list<int64_t>& literals,
                  int64_t aig_id) override
  {
    (void) aig_id;
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

/* --- InterpolationSatSolver ---------------------------------------------- */

/** Interface for interpolating SAT solver wrapper for AIG encoder. */
class BvBitblastSolver::InterpolationSatSolver : public bitblast::SatInterface
{
 public:
  InterpolationSatSolver(Env& env, sat::SatSolver& solver)
      : d_logger(env.logger()), d_solver(solver)
  {
  }

  int32_t new_var() override { return d_solver.new_var(); }

  void add(int64_t lit, int64_t aig_id) override
  {
    assert(aig_id);
    if (lit == 0)
    {
      Log(3) << "CNF encoder: add clause";
      size_t size = d_clause.size();
      if (d_logger.is_log_enabled(3))
      {
        std::stringstream ss;
        ss << "  clause: ";
        for (auto a : d_clause)
        {
          ss << " " << a;
        }
        Log(3) << ss.str();
      }
      for (size_t i = 0; i < size; ++i)
      {
        int64_t lit = d_clause[i];
        Log(3) << "  CNF encoder: add: " << lit;
        d_solver.add(lit, aig_id);
      }
      d_solver.add(0, aig_id);
      d_clause.clear();
    }
    else
    {
      d_clause.push_back(lit);
    }
  }

  void add_clause(const std::initializer_list<int64_t>& literals,
                  int64_t aig_id) override
  {
    for (int64_t lit : literals)
    {
      add(lit, aig_id);
    }
    add(0, aig_id);
  }

  bool value(int64_t lit) override
  {
    return d_solver.value(lit) == 1 ? true : false;
  }

 private:
  /** The associated logger instance. */
  util::Logger& d_logger;
  /** The associated SAT solver. */
  sat::SatSolver& d_solver;
  /** Cache literals of current clause. */
  std::vector<int64_t> d_clause;
};

/* --- BvBitblastSolver public ---------------------------------------------- */

BvBitblastSolver::BvBitblastSolver(Env& env, SolverState& state)
    : Solver(env, state),
      backtrack::Backtrackable(state.backtrack_mgr()),
      d_assertions(state.backtrack_mgr()),
      d_assumptions(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN),
      d_opt_print_aig(!env.options().write_aiger().empty()
                      || !env.options().write_cnf().empty()),
      d_produce_interpolants(env.options().produce_interpolants()),
      d_stats(env.statistics(), "solver::bv::bitblast::")
{
  init_sat_solver();
}

BvBitblastSolver::~BvBitblastSolver() {}

Result
BvBitblastSolver::solve()
{
  if (d_reset_sat)
  {
    init_sat_solver();
    d_reset_sat = false;
  }

  d_sat_solver->configure_terminator(d_env.terminator());

  if (!d_assertions.empty())
  {
    util::Timer timer(d_stats.time_encode);
    for (const Node& assertion : d_assertions)
    {
      const auto& bits = d_bitblaster.bits(assertion);
      assert(!bits.empty());
      d_cnf_encoder->encode(bits[0], true);
    }
    if (!d_produce_interpolants)
    {
      d_assertions.clear();
    }
  }

  for (const Node& assumption : d_assumptions)
  {
    const auto& bits = d_bitblaster.bits(assumption);
    assert(!bits.empty());
    util::Timer timer(d_stats.time_encode);
    d_cnf_encoder->encode(bits[0], false);
    d_sat_solver->assume(d_cnf_encoder->cnf_lit(bits[0]));
  }

  // Update CNF statistics
  update_statistics();

  d_solver_state.print_statistics();

  // Write current bit-vector abstraction as AIGER/CNF
  if (d_opt_print_aig)
  {
    if (!d_env.options().write_aiger().empty())
    {
      d_aig_printer.write_aiger(d_env.options().write_aiger());
    }
    if (!d_env.options().write_cnf().empty())
    {
      d_aig_printer.write_cnf(d_env.options().write_cnf());
    }
  }

  // Register pending heuristics.
  process_pending_eq_heuristics();
  process_pending_distinct_heuristics();

  util::Timer timer(d_stats.time_sat);
  d_last_result = d_sat_solver->solve();

  return d_last_result;
}

void
BvBitblastSolver::register_term(const Node& term)
{
  assert(term.kind() == Kind::DISTINCT_N);
  assert(term[1].type().is_bool() || term[1].type().is_bv());
  register_distinct_n(term);
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
  else
  {
    d_assertions.push_back(assertion);
  }

  {
    util::Timer timer(d_stats.time_bitblast);
    d_bitblaster.bitblast(assertion);
    if (d_opt_print_aig)
    {
      d_aig_printer.add_output(d_bitblaster.bits(assertion)[0]);
    }
  }

  // Update AIG statistics
  update_statistics();
}

void
BvBitblastSolver::register_eq_heuristic(const std::vector<Node>& nodes)
{
  d_pending_eq_heuristics.emplace_back(nodes);
}

void
BvBitblastSolver::register_distinct_heuristic(const std::vector<Node>& nodes)
{
  d_pending_distinct_heuristics.emplace_back(nodes);
}

Node
BvBitblastSolver::value(const Node& term)
{
  assert(BvSolver::is_leaf(term));
  assert(term.type().is_bool() || term.type().is_bv());

  const auto& bits = d_bitblaster.bits(term);
  const Type& type = term.type();
  NodeManager& nm  = d_env.nm();

  // Return default value if not bit-blasted
  if (bits.empty())
  {
    // std::cout << "bv::value::default: " << term << std::endl;
    return utils::mk_default_value(nm, type);
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
  // std::cout << "bv::value:: " << term << " -> " << val << std::endl;
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
    if (d_sat_solver->failed(d_cnf_encoder->cnf_lit(bits[0])))
    {
      core.push_back(assumption);
    }
  }
}

void
BvBitblastSolver::pop()
{
  if (d_produce_interpolants)
  {
    d_reset_sat = true;
  }
}

Node
BvBitblastSolver::interpolant(const std::vector<Node>& ppA,
                              const std::vector<Node>& ppB)
{
#ifndef NDEBUG
  for (const Node& assumption : d_assumptions)
  {
    assert(std::find(ppA.begin(), ppA.end(), assumption) != ppA.end()
           || std::find(ppB.begin(), ppB.end(), assumption) != ppB.end());
  }
#endif
  assert(d_env.options().produce_interpolants());
  d_bv_interpolator.reset(new BvInterpolator(d_env, d_solver_state, *this));
  return d_bv_interpolator->interpolant(ppA, ppB);
}

void
BvBitblastSolver::hint(const Node& node, const Node& value)
{
  if (!value.type().is_bv())
  {
    return;
  }
  const auto& v = value.value<BitVector>();
  d_bitblaster.bitblast(node);
  const auto& bits = d_bitblaster.bits(node);
  for (uint64_t i = 0, size = bits.size(); i < size; ++i)
  {
    d_cnf_encoder->encode(bits[i], false);
    int32_t id    = d_cnf_encoder->cnf_lit(bits[i]);
    int32_t phase = v.bit(size - 1 - i) ? id : -id;
    d_sat_solver->phase(phase);
  }
}

/* --- BvBitblastSolver private --------------------------------------------- */

void
BvBitblastSolver::init_sat_solver()
{
  assert(!d_produce_interpolants
         || d_env.options().sat_solver() == option::SatSolver::CADICAL);

  d_sat_solver = d_env.sat_factory().new_sat_solver(d_produce_interpolants);
  Msg(1) << "initialized SAT solver: " << d_sat_solver->get_name();

  if (d_produce_interpolants)
  {
#ifdef BZLA_USE_CADICAL
    d_bitblast_sat_solver.reset(
        new InterpolationSatSolver(d_env, *d_sat_solver));
#endif
  }
  else
  {
    d_bitblast_sat_solver.reset(new BitblastSatSolver(*d_sat_solver));
  }
  d_cnf_encoder.reset(new bitblast::AigCnfEncoder(*d_bitblast_sat_solver));
  if (d_produce_interpolants)
  {
#ifdef BZLA_USE_CADICAL
    reinterpret_cast<sat::CadicalInterpol*>(d_sat_solver.get())
        ->connect_tracer(d_env, d_bitblaster, *d_cnf_encoder);
#endif
  }
}

void
BvBitblastSolver::register_distinct_n(const Node& node)
{
#ifdef BZLA_USE_CADICAL
  std::vector<std::vector<int32_t>> bits;
  for (uint64_t i = 1, size = node.num_children(); i < size; ++i)
  {
    const Node& n = node[i];
    assert(n.type().is_bv() || n.type().is_bool());
    d_bitblaster.bitblast(n);
    std::vector<int32_t> ids;
    for (const auto& bit : d_bitblaster.bits(n))
    {
      d_cnf_encoder->encode(bit, false);
      ids.push_back(d_cnf_encoder->cnf_lit(bit));
    }
    bits.emplace_back(std::move(ids));
  }
  const auto& bit = d_bitblaster.bits(node)[0];
  d_cnf_encoder->encode(bit, false);
  util::Integer card(node[0].value<BitVector>());
  std::unique_ptr<sat::DistinctNPropagator> distinct_n(
      new sat::DistinctNPropagator(card, d_cnf_encoder->cnf_var(bit), bits));
  d_sat_solver->register_propagator(std::move(distinct_n));
#else
  (void) node;
#endif
}

void
BvBitblastSolver::process_pending_eq_heuristics()
{
#ifdef BZLA_USE_CADICAL
  for (const auto& nodes : d_pending_eq_heuristics)
  {
    std::vector<std::vector<int32_t>> bits;
    for (const auto& n : nodes)
    {
      assert(n.type().is_bv() || n.type().is_bool());
      d_bitblaster.bitblast(n);
      std::vector<int32_t> ids;
      for (const auto& bit : d_bitblaster.bits(n))
      {
        d_cnf_encoder->encode(bit, false);
        ids.push_back(d_cnf_encoder->cnf_lit(bit));
      }
      bits.emplace_back(std::move(ids));
    }
    std::unique_ptr<sat::EqDecisionHeuristic> eqh(
        new sat::EqDecisionHeuristic(bits));
    d_sat_solver->register_propagator(std::move(eqh));
  }
#endif
  d_pending_eq_heuristics.clear();
}

void
BvBitblastSolver::process_pending_distinct_heuristics()
{
#ifdef BZLA_USE_CADICAL
  for (const auto& nodes : d_pending_distinct_heuristics)
  {
    std::vector<std::vector<int32_t>> bits;
    for (const auto& n : nodes)
    {
      assert(n.type().is_bv() || n.type().is_bool());
      d_bitblaster.bitblast(n);
      std::vector<int32_t> ids;
      for (const auto& bit : d_bitblaster.bits(n))
      {
        d_cnf_encoder->encode(bit, false);
        ids.push_back(d_cnf_encoder->cnf_lit(bit));
      }
      bits.emplace_back(std::move(ids));
    }
    std::unique_ptr<sat::DistinctDecisionHeuristic> dih(
        new sat::DistinctDecisionHeuristic(bits));
    d_sat_solver->register_propagator(std::move(dih));
  }
#endif
  d_pending_distinct_heuristics.clear();
}

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
