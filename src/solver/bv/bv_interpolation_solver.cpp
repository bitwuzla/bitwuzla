/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_interpolation_solver.h"

#include <cadical.hpp>
#include <craigtracer.hpp>
#include <cstdint>

#include "bv/bitvector.h"
#include "env.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "sat/cadical.h"
#include "sat/sat_solver_factory.h"
#include "solver/bv/bv_solver.h"
#include "solving_context.h"
#include "util/logger.h"

namespace bzla::bv {

using namespace bzla::node;

/** Interpolating SAT solver wrapper for AIG encoder. */
class BvInterpolationSolver::InterpolationSatSolver
    : public bitblast::SatInterface
{
 public:
  InterpolationSatSolver(Env& env,
                         sat::SatSolver& solver,
                         CaDiCraig::CraigTracer& tracer)
      : d_logger(env.logger()), d_solver(solver), d_craig_tracer(tracer)
  {
  }

  void add(int64_t lit) override
  {
    if (lit == 0)
    {
      d_craig_tracer.label_clause(++d_clause_cnt, d_clause_type);
      Log(2) << "CaDiCraig label clause: " << d_clause_cnt << " "
             << (d_clause_type == CaDiCraig::CraigClauseType::A_CLAUSE ? "A"
                                                                       : "B");
      size_t size = d_clause.size();
      if (d_logger.is_log_enabled(2))
      {
        std::stringstream ss;
        ss << "CaDiCraig clause: ";
        for (auto a : d_clause)
        {
          ss << " " << a;
        }
        Log(2) << ss.str();
      }
      for (size_t i = 0; i < size; ++i)
      {
        int64_t lit = d_clause[i];
        Log(2) << "CaDiCraig add: " << lit;
        resize(lit);
        if (!is_labeled(lit))
        {
          CaDiCraig::CraigVarType var_type = CaDiCraig::CraigVarType::GLOBAL;
          // TODO: determine what to label as A_LOCAL, B_LOCAL
          // clause is unit if size == 1
          // tseitin variable: !is_unit && i == 0
          d_craig_tracer.label_variable(std::abs(lit), var_type);
          Log(2) << "CaDiCraig label var: " << std::abs(lit) << " ("
                 << (var_type == CaDiCraig::CraigVarType::A_LOCAL
                         ? "A_LOCAL"
                         : (var_type == CaDiCraig::CraigVarType::B_LOCAL
                                ? "B_LOCAL"
                                : "GLOBAL"))
                 << ")";
          set_labeled(lit);
        }
        d_solver.add(lit);
      }
      d_solver.add(0);
      d_clause.clear();
    }
    else
    {
      d_clause.push_back(lit);
    }
  }

  void add_clause(const std::initializer_list<int64_t>& literals) override
  {
    for (int64_t lit : literals)
    {
      add(lit);
    }
    add(0);
  }

  bool value(int64_t lit) override
  {
    (void) lit;
    assert(false);
    return false;
  }

  void set_clause_label(CaDiCraig::CraigClauseType type)
  {
    d_clause_type = type;
  }

 private:
  void resize(int64_t lit)
  {
    size_t pos = static_cast<size_t>(std::abs(lit) - 1);
    if (pos < d_var_labeled.size())
    {
      return;
    }
    d_var_labeled.resize(pos + 1, false);
  }
  bool is_labeled(int64_t lit) const
  {
    size_t pos = static_cast<size_t>(std::abs(lit) - 1);
    if (pos < d_var_labeled.size())
    {
      return d_var_labeled[pos];
    }
    return false;
  }
  void set_labeled(int64_t lit)
  {
    size_t pos = static_cast<size_t>(std::abs(lit) - 1);
    assert(pos < d_var_labeled.size());
    d_var_labeled[pos] = true;
  }

  /** The associated logger instance. */
  util::Logger& d_logger;
  /** The associated SAT solver. */
  sat::SatSolver& d_solver;
  /** The associated CaDiCraig tracer. */
  CaDiCraig::CraigTracer& d_craig_tracer;
  /** Maps var to flag that indicates whether the var was already labeled. */
  std::vector<bool> d_var_labeled;
  /** The current clause type (A or B). */
  CaDiCraig::CraigClauseType d_clause_type =
      CaDiCraig::CraigClauseType::A_CLAUSE;
  /** Cache literals of current clause. */
  std::vector<int64_t> d_clause;
  /** The current number of clauses added. */
  int64_t d_clause_cnt = 0;
};

/* --- BvInterpolationSolver public ---------------------------------------- */

BvInterpolationSolver::BvInterpolationSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_assertions(state.backtrack_mgr()),
      d_assumptions(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN),
      d_stats(env.statistics(), "solver::bv::interpol::")
{
  d_craig_tracer.reset(new CaDiCraig::CraigTracer());
  d_craig_tracer->set_craig_construction(
      CaDiCraig::CraigConstruction::ASYMMETRIC);
  d_sat_solver.reset(new sat::Cadical());
  d_sat_solver->solver()->connect_proof_tracer(d_craig_tracer.get(), true);
  d_interpol_sat_solver.reset(
      new InterpolationSatSolver(env, *d_sat_solver, *d_craig_tracer));
  d_cnf_encoder.reset(new bitblast::AigCnfEncoder(*d_interpol_sat_solver));
}

BvInterpolationSolver::~BvInterpolationSolver()
{
  d_sat_solver->solver()->disconnect_proof_tracer(d_craig_tracer.get());
}

std::unordered_map<int64_t, Node>
BvInterpolationSolver::map_vars_to_node(
    const std::unordered_set<int64_t>& vars) const
{
  std::unordered_map<int64_t, Node> res;
  NodeManager& nm   = d_env.nm();
  Node one          = nm.mk_value(BitVector::mk_true());
  const auto& cache = d_bitblaster.bitblaster_cache();
  for (const auto& p : cache)
  {
    bool is_bv = p.first.type().is_bv();
    assert(is_bv || p.first.type().is_bool());
    for (size_t i = 0, size = p.second.size(); i < size; ++i)
    {
      const bitblast::AigNode& a = p.second[i];
      int64_t id                 = a.get_id();
      int64_t var                = std::abs(id);
      auto it                    = res.find(var);
      // already processed
      if (it != res.end())
      {
        continue;
      }
      // don't need to consider
      if (vars.find(var) == vars.end())
      {
        continue;
      }
      // insert
      size_t j = size - 1 - i;
      Node bit;
      if (is_bv)
      {
        Node bit = nm.mk_node(Kind::BV_EXTRACT, {p.first}, {j, j});
        res.emplace(var, id < 0 ? nm.mk_node(Kind::BV_NOT, {bit}) : bit);
      }
      else
      {
        assert(j == 0);
        res.emplace(var, id < 0 ? nm.mk_node(Kind::NOT, {p.first}) : p.first);
      }
    }
  }
  return res;
}

Node
BvInterpolationSolver::interpolant(const std::vector<Node>& A, const Node& C)
{
  assert(d_assertions.empty());
  assert(d_assumptions.empty());

  d_sat_solver->configure_terminator(d_env.terminator());

  Log(1) << "*** interpolant";
  Log(1);

  if (d_logger.is_log_enabled(1))
  {
    for (size_t i = 0, n = A.size(); i < n; ++i)
    {
      Log(1) << "A[" << i << "]: " << A[i];
    }
  }
  Log(1) << "C: " << C;
  Log(1);

  assert(C.type().is_bool());
  // CaDiCraig's interface defines interpolant I as (A -> I) and (I -> not B),
  // for formulas A, B with A /\ B is unsat. In our interface, C = not B.

  NodeManager& nm = d_env.nm();
  Node B          = d_env.rewriter().rewrite(nm.mk_node(Kind::NOT, {C}));

  if (!A.empty())
  {
    util::Timer timer(d_stats.time_encode);
    d_interpol_sat_solver->set_clause_label(
        CaDiCraig::CraigClauseType::A_CLAUSE);
    for (const Node& a : A)
    {
      {
        util::Timer timer(d_stats.time_bitblast);
        d_bitblaster.bitblast(a);
      }
      const auto& bits = d_bitblaster.bits(a);
      assert(!bits.empty());
      d_cnf_encoder->encode(bits[0], true);
    }
  }

  d_interpol_sat_solver->set_clause_label(CaDiCraig::CraigClauseType::B_CLAUSE);
  {
    util::Timer timer(d_stats.time_bitblast);
    d_bitblaster.bitblast(B);
  }
  const auto& bits = d_bitblaster.bits(B);
  assert(!bits.empty());
  {
    util::Timer timer(d_stats.time_encode);
    d_cnf_encoder->encode(bits[0], true);
  }

  // Update CNF statistics
  update_statistics();

  Log(2);
  if (d_sat_solver->solve() != Result::UNSAT)
  {
    Log(1) << "not unsat";
    return Node();
  }

  util::Timer timer(d_stats.time_interpol);
  int32_t next_aig_id = d_bitblaster.aig_id_counter() + 1;
  std::vector<std::vector<int>> clauses;
  CaDiCraig::CraigCnfType result = d_craig_tracer->create_craig_interpolant(
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_aig_id);

  if (result == CaDiCraig::CraigCnfType::NONE)
  {
    Log(1) << "NONE";
    return Node();
  }
  if (result == CaDiCraig::CraigCnfType::CONSTANT0)
  {
    Log(1) << "CONSTANT0";
    return nm.mk_value(false);
  }
  if (result == CaDiCraig::CraigCnfType::CONSTANT1)
  {
    Log(1) << "CONSTANT1";
    return nm.mk_value(true);
  }

  Log(1) << "NORMAL";
  if (d_logger.is_log_enabled(1))
  {
    std::stringstream ss;
    ss << "SAT interpolant: ";
    for (const auto& cl : clauses)
    {
      ss << "(";
      for (const auto& l : cl)
      {
        ss << " " << l;
      }
      ss << " )" << std::endl;
      Log(1) << ss.str();
    }
  }

  assert(result == CaDiCraig::CraigCnfType::NORMAL);
  std::unordered_set<int64_t> vars;
  for (const auto& clause : clauses)
  {
    for (int64_t lit : clause)
    {
      vars.insert(std::abs(lit));
    }
  }
  auto map = map_vars_to_node(vars);
  Node res = nm.mk_value(true);
  for (const auto& clause : clauses)
  {
    Node cl = nm.mk_value(false);
    for (int64_t lit : clause)
    {
      auto it = map.find(std::abs(lit));
      assert(it != map.end());
      cl = nm.mk_node(
          Kind::OR,
          {cl, lit < 0 ? nm.mk_node(Kind::NOT, {it->second}) : it->second});
    }
    res = nm.mk_node(Kind::AND, {res, cl});
  }
  return d_env.rewriter().rewrite(res);
}

void
BvInterpolationSolver::register_assertion(const Node& assertion,
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
  }

  // Update AIG statistics
  update_statistics();
}

Result
BvInterpolationSolver::solve()
{
  assert(false);
  return Result::UNKNOWN;
}

Node
BvInterpolationSolver::value(const Node& term)
{
  (void) term;
  assert(false);
}

void
BvInterpolationSolver::unsat_core(std::vector<Node>& core) const
{
  (void) core;
  assert(false);
}

/* --- BvBitblastSolver private --------------------------------------------- */

void
BvInterpolationSolver::update_statistics()
{
  d_stats.num_aig_ands     = d_bitblaster.num_aig_ands();
  d_stats.num_aig_consts   = d_bitblaster.num_aig_consts();
  d_stats.num_aig_shared   = d_bitblaster.num_aig_shared();
  auto& cnf_stats          = d_cnf_encoder->statistics();
  d_stats.num_cnf_vars     = cnf_stats.num_vars;
  d_stats.num_cnf_clauses  = cnf_stats.num_clauses;
  d_stats.num_cnf_literals = cnf_stats.num_literals;
}

BvInterpolationSolver::Statistics::Statistics(util::Statistics& stats,
                                              const std::string& prefix)
    : time_interpol(
          stats.new_stat<util::TimerStatistic>(prefix + "sat::time_interpol")),
      time_bitblast(
          stats.new_stat<util::TimerStatistic>(prefix + "aig::time_bitblast")),
      time_encode(
          stats.new_stat<util::TimerStatistic>(prefix + "cnf::time_encode")),
      num_aig_ands(stats.new_stat<uint64_t>(prefix + "aig::num_ands")),
      num_aig_consts(stats.new_stat<uint64_t>(prefix + "aig::num_consts")),
      num_aig_shared(stats.new_stat<uint64_t>(prefix + "aig::num_shared")),
      num_cnf_vars(stats.new_stat<uint64_t>(prefix + "cnf::num_vars_a")),
      num_cnf_clauses(stats.new_stat<uint64_t>(prefix + "cnf::num_clauses_a")),
      num_cnf_literals(stats.new_stat<uint64_t>(prefix + "cnf::num_literals_a"))
{
}

}  // namespace bzla::bv
