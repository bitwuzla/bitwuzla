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

#include <cstdint>

#include "env.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"
#include "sat/cadical.h"
#include "sat/interpolants/cadical_tracer.h"
#include "sat/interpolants/cadicraig_tracer.h"
#include "solver/bv/aig_bitblaster.h"

using namespace bzla::node;
using namespace bzla::sat::interpolants;

namespace bzla::bv {

/* --- InterpolationSatSolver ---------------------------------------------- */

/** Interface for interpolating SAT solver wrapper for AIG encoder. */
class BvInterpolationSolver::InterpolationSatSolver
    : public bitblast::SatInterface
{
 public:
  InterpolationSatSolver(Env& env, sat::SatSolver& solver, Tracer& tracer)
      : d_logger(env.logger()), d_solver(solver), d_tracer(tracer)
  {
  }

  void set_clause_label(Tracer::ClauseKind kind) { d_clause_kind = kind; }

  void add(int64_t lit) override
  {
    if (lit == 0)
    {
      d_tracer.label_clause(++d_clause_cnt, d_clause_kind);
      Log(3) << "bitblaster: label clause: " << d_clause_cnt << " "
             << (d_clause_kind == Tracer::ClauseKind::A ? "A" : "B");
      size_t size = d_clause.size();
      if (d_logger.is_log_enabled(2))
      {
        std::stringstream ss;
        ss << "bitblaster: clause: ";
        for (auto a : d_clause)
        {
          ss << " " << a;
        }
        Log(3) << ss.str();
      }
      for (size_t i = 0; i < size; ++i)
      {
        int64_t lit = d_clause[i];
        Log(3) << "bitblaster: add: " << lit;
        resize(lit);
        if (!is_labeled(lit))
        {
          Tracer::VariableKind var_kind = Tracer::VariableKind::GLOBAL;
          // TODO: determine what to label as A_LOCAL, B_LOCAL
          // clause is unit if size == 1
          // tseitin variable: !is_unit && i == 0
          d_tracer.label_variable(std::abs(lit), var_kind);
          Log(3) << "label var: " << std::abs(lit) << " ("
                 << (var_kind == Tracer::VariableKind::A
                         ? "A"
                         : (var_kind == Tracer::VariableKind::B ? "B"
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
  /** Maps var to flag that indicates whether the var was already labeled. */
  std::vector<bool> d_var_labeled;
  /** Cache literals of current clause. */
  std::vector<int64_t> d_clause;
  /** The current number of clauses added. */
  int64_t d_clause_cnt = 0;

  /** The associated tracer. */
  Tracer& d_tracer;
  /** The current clause type (A or B). */
  Tracer::ClauseKind d_clause_kind = Tracer::ClauseKind::A;
};

/* --- BvInterpolationSolver public ---------------------------------------- */

BvInterpolationSolver::BvInterpolationSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_assertions(state.backtrack_mgr()),
      d_assumptions(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN),
      d_stats(env.statistics(), "solver::bv::interpol::")
{
  d_sat_solver.reset(new sat::Cadical());
  if (env.options().tmp_interpol_use_cadicraig())
  {
    CadiCraigTracer* cctracer = new CadiCraigTracer(env, d_bitblaster);
    d_tracer.reset(cctracer);
  }
  else
  {
    d_tracer.reset(new CadicalTracer(d_env, d_bitblaster));
  }
  d_interpol_sat_solver.reset(
      new InterpolationSatSolver(env, *d_sat_solver, *d_tracer));
  d_sat_solver->solver()->connect_proof_tracer(d_tracer.get(), true);
  d_cnf_encoder.reset(new bitblast::AigCnfEncoder(*d_interpol_sat_solver));
}

BvInterpolationSolver::~BvInterpolationSolver()
{
  d_sat_solver->solver()->disconnect_proof_tracer(d_tracer.get());
}

Node
BvInterpolationSolver::interpolant(const std::vector<Node>& A, const Node& C)
{
  assert(d_assertions.empty());
  assert(d_assumptions.empty());

  d_sat_solver->configure_terminator(d_env.terminator());

  Log(1);
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

  // Our SAT interpolation tracer interface defines interpolant I as (A -> I)
  // and (I -> not B), for formulas A, B with A /\ B is unsat (following
  // CaDiCaL's own CaDiCraig tracer's interface). In our word-level interface
  // here, C = not B.

  NodeManager& nm = d_env.nm();
  Node B          = d_env.rewriter().rewrite(nm.mk_node(Kind::NOT, {C}));

  if (!A.empty())
  {
    util::Timer timer(d_stats.time_encode);
    d_interpol_sat_solver->set_clause_label(CadicalTracer::ClauseKind::A);
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

  d_interpol_sat_solver->set_clause_label(CadicalTracer::ClauseKind::B);
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

  Log(3);
  if (d_sat_solver->solve() != Result::UNSAT)
  {
    Log(1) << "not unsat";
    return Node();
  }

  util::Timer timer(d_stats.time_interpol);
  Node res = d_env.rewriter().rewrite(d_tracer->get_interpolant());

  Log(2);
  Log(1) << "interpolant: " << res;
  if (d_logger.is_log_enabled(1))
  {
    node_ref_vector visit{res};
    unordered_node_ref_set cache;
    uint64_t interpol_size = 0;
    do
    {
      const Node& cur = visit.back();
      visit.pop_back();
      auto [it, inserted] = cache.insert(cur);
      if (inserted)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        assert(cur.kind() != Kind::BV_AND);
        if (cur.kind() == Kind::AND)
        {
          interpol_size += 1;
        }
      }
    } while (!visit.empty());
    Log(1) << "interpolant size: " << interpol_size << " ands";
  }

  return res;
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
  return Node();
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
