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
#include "sat/interpolants/cadical_tracer.h"
#include "sat/sat_solver_factory.h"
#include "solver/bv/bv_solver.h"
#include "solving_context.h"
#include "util/logger.h"

using namespace bzla::node;
using namespace bzla::sat::interpolants;

namespace bzla::bv {

static std::unordered_map<Tracer::VariableKind, CaDiCraig::CraigVarType>
    s_var_kind_to_cadicraig = {
        {Tracer::VariableKind::A, CaDiCraig::CraigVarType::A_LOCAL},
        {Tracer::VariableKind::B, CaDiCraig::CraigVarType::B_LOCAL},
        {Tracer::VariableKind::GLOBAL, CaDiCraig::CraigVarType::GLOBAL},
};
static std::unordered_map<Tracer::ClauseKind, CaDiCraig::CraigClauseType>
    s_clause_kind_to_cadicraig = {
        {Tracer::ClauseKind::A, CaDiCraig::CraigClauseType::A_CLAUSE},
        {Tracer::ClauseKind::B, CaDiCraig::CraigClauseType::B_CLAUSE},
        {Tracer::ClauseKind::LEARNED, CaDiCraig::CraigClauseType::L_CLAUSE},
};
static std::unordered_map<CaDiCraig::CraigCnfType, Tracer::CnfKind>
    s_cnf_kind_to_cadicraig = {
        {CaDiCraig::CraigCnfType::NONE, Tracer::CnfKind::NONE},
        {CaDiCraig::CraigCnfType::CONSTANT0, Tracer::CnfKind::CONSTANT0},
        {CaDiCraig::CraigCnfType::CONSTANT1, Tracer::CnfKind::CONSTANT1},
        {CaDiCraig::CraigCnfType::NORMAL, Tracer::CnfKind::NORMAL},
};

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
      Log(3) << "CaDiCraig label clause: " << d_clause_cnt << " "
             << (d_clause_kind == Tracer::ClauseKind::A ? "A" : "B");
      size_t size = d_clause.size();
      if (d_logger.is_log_enabled(2))
      {
        std::stringstream ss;
        ss << "CaDiCraig clause: ";
        for (auto a : d_clause)
        {
          ss << " " << a;
        }
        Log(3) << ss.str();
      }
      for (size_t i = 0; i < size; ++i)
      {
        int64_t lit = d_clause[i];
        Log(3) << "CaDiCraig add: " << lit;
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

/* --- sat::interpolants::Tracer ------------------------------------------- */

class CadiCraigTracer : public Tracer
{
 public:
  CadiCraigTracer()
  {
    d_tracer.reset(new CaDiCraig::CraigTracer());
    d_tracer->set_craig_construction(CaDiCraig::CraigConstruction::ASYMMETRIC);
  }
  ~CadiCraigTracer() {}

  /* CaDiCaL::Tracer interface ------------------------------------------- */

  void add_original_clause(uint64_t id,
                           bool redundant,
                           const std::vector<int32_t>& clause,
                           bool restore = false) override
  {
    d_tracer->add_original_clause(id, redundant, clause, restore);
  }

  void add_derived_clause(uint64_t id,
                          bool redundant,
                          const std::vector<int>& clause,
                          const std::vector<uint64_t>& proof_chain) override
  {
    d_tracer->add_derived_clause(id, redundant, clause, proof_chain);
  }

  void add_assumption_clause(uint64_t id,
                             const std::vector<int>& clause,
                             const std::vector<uint64_t>& proof_chain) override
  {
    d_tracer->add_assumption_clause(id, clause, proof_chain);
  }

  void delete_clause(uint64_t id,
                     bool redundant,
                     const std::vector<int>& clause) override
  {
    d_tracer->delete_clause(id, redundant, clause);
  }

  void add_assumption(int32_t lit) override { d_tracer->add_assumption(lit); }

  void add_constraint(const std::vector<int32_t>& clause) override
  {
    d_tracer->add_constraint(clause);
  }

  void reset_assumptions() override { d_tracer->reset_assumptions(); }

  void conclude_unsat(CaDiCaL::ConclusionType conclusion,
                      const std::vector<uint64_t>& proof_chain) override
  {
    d_tracer->conclude_unsat(conclusion, proof_chain);
  }

  /* --------------------------------------------------------------------- */

  void label_variable(int32_t id, VariableKind kind) override
  {
    d_tracer->label_variable(id, s_var_kind_to_cadicraig[kind]);
  }

  void label_clause(int32_t id, ClauseKind kind) override
  {
    d_tracer->label_clause(id, s_clause_kind_to_cadicraig[kind]);
  }

  CnfKind create_craig_interpolant(std::vector<std::vector<int>>& cnf,
                                   int& tseitin_offset) override
  {
    CaDiCraig::CraigCnfType res = d_tracer->create_craig_interpolant(
        CaDiCraig::CraigInterpolant::ASYMMETRIC, cnf, tseitin_offset);
    return s_cnf_kind_to_cadicraig[res];
  }

  std::unique_ptr<CaDiCraig::CraigTracer> d_tracer;
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
    CadiCraigTracer* cctracer = new CadiCraigTracer();
    d_tracer.reset(cctracer);
  }
  else
  {
    d_tracer.reset(new CadicalTracer(d_bitblaster.amgr()));
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

std::unordered_map<int64_t, Node>
BvInterpolationSolver::map_vars_to_node(const std::unordered_set<int64_t>& vars)
{
  std::unordered_map<int64_t, Node> res;
  NodeManager& nm   = d_env.nm();
  Node one          = nm.mk_value(BitVector::mk_true());
  const auto& cache = d_bitblaster.bitblaster_cache();

  // Map SAT vars to node for vars that do not occur in `vars`, we may need them
  // when creating nodes for internal AIG nodes.
  std::unordered_map<int64_t, std::pair<Node, int64_t>> skipped_vars_to_node;

  Log(2);
  Log(2) << "Bit-blaster cache: ";
  for (const auto& p : cache)
  {
    if (d_logger.is_log_enabled(2))
    {
      std::stringstream ss;
      ss << p.first << ": (";
      for (const auto& a : p.second)
      {
        ss << " " << a.get_id();
      }
      ss << " )";
      Log(2) << ss.str();
    }

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
      size_t j = size - 1 - i;
      // don't need to consider
      if (vars.find(var) == vars.end())
      {
        skipped_vars_to_node.emplace(
            var,
            std::make_pair(
                id < 0 ? node::utils::invert_node(nm, p.first) : p.first, j));
        continue;
      }
      // insert
      Node bit = p.first;
      assert(is_bv || j == 0);
      if (is_bv)
      {
        bit = node::utils::bv1_to_bool(
            nm, nm.mk_node(Kind::BV_EXTRACT, {bit}, {j, j}));
      }
      res.emplace(var, id < 0 ? nm.mk_node(Kind::NOT, {bit}) : bit);
    }
  }
  for (const int64_t var : vars)
  {
    if (res.find(var) != res.end())
    {
      continue;
    }
    // var is a circuit-internal AND gate, reconstruct in terms of inputs
    bitblast::AigNode aig_node = d_bitblaster.get_node(var);

    AigBitblaster::aig_node_ref_vector visit{aig_node};
    AigBitblaster::unordered_aig_node_ref_map<bool> cache;

    do
    {
      const bitblast::AigNode& cur = visit.back();
      int64_t id                   = cur.get_id();
      int64_t var                  = std::abs(id);

      if (res.find(var) != res.end())
      {
        visit.pop_back();
        continue;
      }

      {
        auto it = skipped_vars_to_node.find(var);
        if (it != skipped_vars_to_node.end())
        {
          Node bit   = it->second.first;
          size_t idx = it->second.second;
          assert(bit.type().is_bv() || idx == 0);
          if (bit.type().is_bv())
          {
            bit = node::utils::bv1_to_bool(
                nm, nm.mk_node(Kind::BV_EXTRACT, {bit}, {idx, idx}));
          }
          res.emplace(var, bit);
          visit.pop_back();
          continue;
        }
      }

      assert(cur.is_and());

      auto [it, inserted] = cache.emplace(cur, true);

      if (inserted)
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
      else if (it->second)
      {
        it->second       = false;
        int64_t id_left  = cur[0].get_id();
        int64_t id_right = cur[1].get_id();
        Node left        = res.at(std::abs(id_left));
        if (id_left < 0)
        {
          left = node::utils::invert_node(nm, left);
        }
        Node right = res.at(std::abs(id_right));
        if (id_right < 0)
        {
          right = node::utils::invert_node(nm, right);
        }
        res[var] = nm.mk_node(Kind::AND, {left, right});
        visit.pop_back();
      }
    } while (!visit.empty());
  }
  return res;
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
  // CaDiCraig's interface defines interpolant I as (A -> I) and (I -> not B),
  // for formulas A, B with A /\ B is unsat. In our interface, C = not B.

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
  int32_t cur_aig_id  = d_bitblaster.amgr().aig_id_counter();
  int32_t next_aig_id = cur_aig_id + 1;
  Log(3) << "cur_aig_id: " << cur_aig_id;

  std::vector<std::vector<int>> clauses;
  Tracer::CnfKind result =
      d_tracer->create_craig_interpolant(clauses, next_aig_id);

  if (result == Tracer::CnfKind::NONE)
  {
    Log(1) << "NONE";
    return Node();
  }
  if (result == Tracer::CnfKind::CONSTANT0)
  {
    Log(1) << "CONSTANT0";
    return nm.mk_value(false);
  }
  if (result == Tracer::CnfKind::CONSTANT1)
  {
    Log(1) << "CONSTANT1";
    return nm.mk_value(true);
  }

  Log(1) << "NORMAL";

  Log(2);
  Log(2) << "SAT interpolant: ";
  if (d_logger.is_log_enabled(1))
  {
    for (const auto& cl : clauses)
    {
      std::stringstream ss;
      ss << "(";
      for (const auto& l : cl)
      {
        ss << " " << l;
      }
      ss << " )";
      Log(2) << ss.str();
    }
  }

  assert(result == Tracer::CnfKind::NORMAL);
  std::unordered_map<int64_t, std::pair<int64_t, int64_t>> and_gates;
  std::unordered_set<int64_t> vars;
  for (const auto& clause : clauses)
  {
    // Every variable with id > cur_aig_id is a tseitin variable introduced
    // by CaDiCraig during CNF conversion of the AIG interpolant. The CNF
    // encoding of an AND gate is of the form, e.g.,
    // (-4 1)
    // (-4 2)
    // (4 -1 -2)
    // where 4 is a tseitin variable, 1 and 2 are the inputs of the AND gate
    // and thus 4 -> (and 1 2).

    // Collect AND gates introduced by CaDiCraig and known SAT vars to be mapped
    // to Nodes.
    int64_t var = std::abs(clause[0]);
    if (var > cur_aig_id)  // tseitin var, clause is part of AND encoding
    {
      if (clause.size() > 1)
      {
        auto [it, inserted] = and_gates.emplace(var, std::make_pair(0, 0));
        if (clause[0] < 0)
        {
          assert(clause.size() == 2);
          if (it->second.first == 0)
          {
            it->second.first = clause[1];
          }
          else
          {
            assert(it->second.second == 0);
            it->second.second = clause[1];
          }
        }
        var = std::abs(clause[1]);
        if (var <= cur_aig_id)
        {
          vars.insert(var);
        }
      }
    }
    else
    {
      assert(clause.size() == 1);
      vars.insert(var);
    }
  }

  Log(2);
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    ss << "SAT vars occurring in SAT interpolant: {";
    for (const auto& v : vars)
    {
      ss << " " << v;
    }
    ss << " }";
    Log(2) << ss.str();
  }

  // map SAT vars to Nodes
  auto map = map_vars_to_node(vars);

  if (d_logger.is_log_enabled(2))
  {
    Log(2);
    Log(2) << "SAT vars to nodes:";
    for (const auto& p : map)
    {
      Log(2) << p.first << ": " << p.second;
    }

    Log(2);
    std::stringstream ss;
    ss << "CaDiCraig Tseitin variables: {";
    for (const auto& p : and_gates)
    {
      ss << " " << p.first;
    }
    ss << " }";
    Log(2) << ss.str();
  }

  for (const auto& clause : clauses)
  {
    for (int64_t lit : clause)
    {
      int64_t var = std::abs(lit);
      auto it     = map.find(var);
      if (it == map.end())
      {
        auto iit = and_gates.find(var);
        assert(iit != and_gates.end());
        int64_t lit_left  = iit->second.first;
        int64_t lit_right = iit->second.second;
        Node left         = map.at(std::abs(lit_left));
        if (lit_left < 0)
        {
          left = node::utils::invert_node(nm, left);
        }
        Node right = map.at(std::abs(lit_right));
        if (lit_right < 0)
        {
          right = node::utils::invert_node(nm, right);
        }
        map[var] = nm.mk_node(Kind::AND, {left, right});
      }
    }
  }

  assert(clauses[clauses.size() - 1].size() == 1);
  int64_t root = clauses[clauses.size() - 1][0];
  assert(map.find(std::abs(root)) != map.end());
  Node res = map.at(std::abs(root));
  if (root < 0)
  {
    res = nm.mk_node(Kind::NOT, {res});
  }
  res = d_env.rewriter().rewrite(res);

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
