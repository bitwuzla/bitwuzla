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
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "sat/cadical.h"
#include "sat/interpolants/cadical_tracer.h"
#include "sat/interpolants/cadicraig_tracer.h"
#include "sat/interpolants/tracer_kinds.h"
#include "solver/bv/aig_bitblaster.h"
#include "solver/bv/bv_solver.h"

using namespace bzla::node;
using namespace bzla::sat::interpolants;

namespace bzla::bv {

/* --- InterpolationSatSolver ---------------------------------------------- */

/** Interface for interpolating SAT solver wrapper for AIG encoder. */
class BvInterpolationSolver::InterpolationSatSolver
    : public bitblast::SatInterface
{
 public:
  InterpolationSatSolver(
      Env& env,
      sat::SatSolver& solver,
      Tracer& tracer,
      std::unordered_map<int64_t, VariableKind>& sat_vars_to_kinds)
      : d_vars_to_kinds(sat_vars_to_kinds),
        d_logger(env.logger()),
        d_solver(solver),
        d_tracer(tracer)
  {
  }

  void set_clause_label(ClauseKind kind) { d_clause_kind = kind; }

  void add(int64_t lit) override
  {
    if (lit == 0)
    {
      d_tracer.label_clause(++d_clause_cnt, d_clause_kind);
      Log(3) << "CNF encoder: add clause";
      Log(3) << "  label clause: " << d_clause_cnt << " "
             << (d_clause_kind == ClauseKind::A ? "A" : "B");
      size_t size = d_clause.size();
      if (d_logger.is_log_enabled(2))
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
        resize(lit);
        if (!is_labeled(lit))
        {
          int64_t var                   = std::abs(lit);
          auto it                       = d_vars_to_kinds.find(var);
          VariableKind var_kind         = it != d_vars_to_kinds.end()
                                              ? d_vars_to_kinds.at(var)
                                              : VariableKind::GLOBAL;
          d_tracer.label_variable(var, var_kind);
          Log(3) << "  label var: " << var << " ("
                 << (var_kind == VariableKind::A
                         ? "A"
                         : (var_kind == VariableKind::B ? "B" : "GLOBAL"))
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
    return d_solver.value(lit) == 1 ? true : false;
  }

  /**
   * Label all SAT variables occuring in the given AIG with the given kind (if
   * yet unlabeled) or as VariableKind::GLOBAL if they occur both in A and B.
   *
   * Note that if label_bits is not called explicitly to label an AIG, it
   * will be labeled as shared.
   *
   * @param bits The AIG representation of the bit-vector to label.
   * @param kind The label kind.
   */
  void label(const bitblast::AigBitblaster::Bits& bits, VariableKind kind)
  {
    bv::AigBitblaster::aig_node_ref_vector visit;
    std::unordered_set<int64_t> cache;
    for (const auto& aig : bits)
    {
      visit.push_back(aig);
    }
    do
    {
      const bitblast::AigNode& cur = visit.back();
      int64_t id                   = cur.get_id();
      int64_t var                  = std::abs(id);

      {
        auto [it, inserted] = cache.insert(var);
        if (!inserted)
        {
          visit.pop_back();
          continue;
        }
      }

      visit.pop_back();

      if (cur.is_true() || cur.is_false())
      {
        continue;
      }

      if (cur.is_and())
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
      auto [it, inserted] = d_vars_to_kinds.emplace(var, kind);
      assert(kind == VariableKind::B || inserted
             || it->second == VariableKind::GLOBAL || kind == it->second);
      if (!inserted && it->second != kind && it->second != VariableKind::GLOBAL)
      {
        it->second = VariableKind::GLOBAL;
      }
    } while (!visit.empty());
  }

  /**
   * Label unlabeled SAT variables occuring in a lemma depending on which kind
   * the non-GLOBAL variables in the lemma are assigned to.
   *
   * That is,
   * * A, S: labeled as A
   * * B, S: labeled as B
   * * S: labeled as A
   *
   * Note that for now, we do not allow lemmas with "mixed" occurrences, i.e.,
   * occurences of both A and B local variables.
   *
   * @param bits The AIG representation of the bit-vector to label.
   */
  void label_lemma(const bitblast::AigBitblaster::Bits& bits)
  {
    bv::AigBitblaster::aig_node_ref_vector visit;
    std::unordered_set<int64_t> cache;
    std::vector<int64_t> aig_consts;
    for (const auto& aig : bits)
    {
      visit.push_back(aig);
    }
    VariableKind kind = VariableKind::GLOBAL;
    do
    {
      const bitblast::AigNode& cur = visit.back();
      int64_t id                   = cur.get_id();
      int64_t var                  = std::abs(id);

      {
        auto [it, inserted] = cache.insert(var);
        if (!inserted)
        {
          visit.pop_back();
          continue;
        }
      }

      visit.pop_back();

      if (cur.is_and())
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }

      auto it = d_vars_to_kinds.find(var);
      if (it == d_vars_to_kinds.end())
      {
        aig_consts.push_back(var);
      }
      else
      {
        if (it->second == VariableKind::GLOBAL)
        {
          continue;
        }
        assert(kind == VariableKind::GLOBAL || kind == it->second);
        kind = it->second;
      }
    } while (!visit.empty());
    for (int64_t var : aig_consts)
    {
      auto [it, inserted] = d_vars_to_kinds.emplace(var, kind);
      assert(inserted);
    }
  }

  /** Maps var to kind as labeled after bit-blasting. */
  std::unordered_map<int64_t, VariableKind>& d_vars_to_kinds;

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
  /** Indicates whether var was already labeled in the tracer. */
  std::vector<bool> d_var_labeled;
  /** Cache literals of current clause. */
  std::vector<int64_t> d_clause;
  /** The current number of clauses added. */
  int64_t d_clause_cnt = 0;

  /** The associated tracer. */
  Tracer& d_tracer;
  /** The current clause type (A or B). */
  ClauseKind d_clause_kind = ClauseKind::A;
};

/* --- InterpolationBitblaster --------------------------------------------- */

class InterpolationBitblaster : public AigBitblaster
{
 public:
  InterpolationBitblaster(
      std::unordered_map<Node, VariableKind>& consts_to_kinds,
      std::unordered_map<int64_t, VariableKind>& sat_vars_to_kinds)
      : d_consts_to_kinds(consts_to_kinds),
        d_sat_vars_to_kinds(sat_vars_to_kinds)
  {
  }
  /** Recursively bit-blast `term`. */
  void bitblast(const Node& term) override
  {
    node_ref_vector visit{term};
    unordered_node_ref_map<bool> cache;
    do
    {
      const Node& cur     = visit.back();
      auto [it, inserted] = cache.emplace(cur, true);

      if (inserted)
      {
        if (!BvSolver::is_leaf(cur))
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
        continue;
      }
      else if (it->second)
      {
        it->second = false;
        AigBitblaster::bitblast(cur);
        if (cur.kind() == Kind::CONSTANT)
        {
          auto cit = d_consts_to_kinds.find(cur);
          assert(cit != d_consts_to_kinds.end());
          const auto& cur_bits = bits(cur);
          for (const auto& bit : cur_bits)
          {
            auto [lit, linserted] = d_sat_vars_to_kinds.emplace(
                std::abs(bit.get_id()), cit->second);
            if (!linserted && lit->second != VariableKind::GLOBAL
                && lit->second != cit->second)
            {
              lit->second = VariableKind::GLOBAL;
            }
          }
        }
      }
      visit.pop_back();
    } while (!visit.empty());
  }

 private:
  std::unordered_map<Node, VariableKind>& d_consts_to_kinds;
  std::unordered_map<int64_t, VariableKind>& d_sat_vars_to_kinds;
};

/* --- BvInterpolationSolver public ---------------------------------------- */

BvInterpolationSolver::BvInterpolationSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_stats(env.statistics(), "solver::bv::interpol::"),
      d_assertions(state.backtrack_mgr()),
      d_assumptions(state.backtrack_mgr()),
      d_lemmas(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN)
{
  d_bitblaster.reset(
      new InterpolationBitblaster(d_consts_to_kinds, d_sat_vars_to_kinds));
  d_sat_solver.reset(new sat::Cadical());
  if (env.options().tmp_interpol_use_cadicraig())
  {
    CadiCraigTracer* cctracer = new CadiCraigTracer(env, *d_bitblaster);
    d_tracer.reset(cctracer);
  }
  else
  {
    d_tracer.reset(new CadicalTracer(d_env, *d_bitblaster));
  }
  d_interpol_sat_solver.reset(new InterpolationSatSolver(
      env, *d_sat_solver, *d_tracer, d_sat_vars_to_kinds));
  d_sat_solver->solver()->connect_proof_tracer(d_tracer.get(), true);
  d_cnf_encoder.reset(new bitblast::AigCnfEncoder(*d_interpol_sat_solver));
}

BvInterpolationSolver::~BvInterpolationSolver()
{
  d_sat_solver->solver()->disconnect_proof_tracer(d_tracer.get());
}

Node
BvInterpolationSolver::interpolant()
{
  assert(d_last_result == Result::UNSAT);

  Log(2);
  Log(2) << "Bitblaster cache: " << d_bitblaster->bitblaster_cache().size()
         << " entries";
  Log(2);
  if (d_logger.is_log_enabled(2))
  {
    for (const auto& p : d_bitblaster->bitblaster_cache())
    {
      std::stringstream ss;
      ss << "@t" << p.first.id() << ": " << p.first << ": (";
      for (const auto& a : p.second)
      {
        ss << " " << a.get_id();
      }
      ss << " )";
      Log(2) << ss.str();
    }
  }

  if (d_logger.is_log_enabled(3))
  {
    Log(3);
    Log(3) << "SAT var to kinds:";
    for (const auto& p : d_interpol_sat_solver->d_vars_to_kinds)
    {
      Log(3) << p.first << ": "
             << (p.second == VariableKind::A
                     ? "A"
                     : (p.second == VariableKind::B ? "B" : "GLOBAL"));
    }
    Log(3);
  }

  util::Timer timer(d_stats.time_interpol);
  Node res = d_env.rewriter().rewrite(d_tracer->get_interpolant());
  d_stats.size_interpolant += d_tracer->d_stats.size_interpolant;

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
      if (cur.type().is_bv())
      {
        continue;
      }
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

  // Label bit-vector consts that occur in assertion
  label(assertion,
        d_solver_state.is_interpol_conj(assertion) ? VariableKind::B
                                                   : VariableKind::A);
  if (is_lemma)
  {
    d_lemmas.insert(assertion);
  }

  // Update AIG statistics
  update_statistics();
}

void
BvInterpolationSolver::label(const Node& node, VariableKind kind)
{
  node_ref_vector visit{node};
  unordered_node_ref_map<bool> cache;
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);

    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second)
    {
      it->second = false;
      if (cur.is_const())
      {
        auto [lit, linserted] = d_consts_to_kinds.emplace(cur, kind);
        if (!linserted && lit->second != VariableKind::GLOBAL
            && lit->second != kind)
        {
          lit->second = VariableKind::GLOBAL;
        }
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

Result
BvInterpolationSolver::solve()
{
  d_sat_solver->configure_terminator(d_env.terminator());

  // Bitblast and determine variable labels
  if (!d_assertions.empty())
  {
    util::Timer timer(d_stats.time_bitblast);
    for (const Node& assertion : d_assertions)
    {
      d_bitblaster->bitblast(assertion);
      // we label lemmas after A and B assertions/assumptions have been labeled
      if (d_lemmas.find(assertion) != d_lemmas.end())
      {
        continue;
      }
      const auto& bits = d_bitblaster->bits(assertion);
      assert(!bits.empty());
      VariableKind kind = d_solver_state.is_interpol_conj(assertion)
                              ? VariableKind::B
                              : VariableKind::A;
      d_interpol_sat_solver->label(bits, kind);
    }
  }
  if (!d_assumptions.empty())
  {
    for (const Node& assumption : d_assumptions)
    {
      if (d_bitblaster->bits(assumption).empty())
      {
        util::Timer timer(d_stats.time_bitblast);
        d_bitblaster->bitblast(assumption);
      }
      // we label lemmas after A and B assertions/assumptions have been labeled
      if (d_lemmas.find(assumption) != d_lemmas.end())
      {
        continue;
      }
      const auto& bits = d_bitblaster->bits(assumption);
      assert(!bits.empty());
      VariableKind kind = d_solver_state.is_interpol_conj(assumption)
                              ? VariableKind::B
                              : VariableKind::A;
      d_interpol_sat_solver->label(bits, kind);
    }
  }
  for (const Node& lemma : d_lemmas)
  {
    // For now we only support interpolation in the lazy case for QF_BV +
    // abstraction, where we can only get lemmas that contain terms with
    // 1. only GLOBAL consts
    // 2. A and shared consts
    // 3. B and shared consts.
    // Thus we can assert that we don't get mixed terms (which is not the case
    // if UF or arrays are involved).
    const auto& bits = d_bitblaster->bits(lemma);
    assert(!bits.empty());
    d_interpol_sat_solver->label_lemma(bits);
  }

  // Encode
  if (!d_assertions.empty())
  {
    util::Timer timer(d_stats.time_encode);
    for (const Node& assertion : d_assertions)
    {
      ClauseKind kind = d_solver_state.is_interpol_conj(assertion)
                            ? ClauseKind::B
                            : ClauseKind::A;
      d_interpol_sat_solver->set_clause_label(kind);
      const auto& bits = d_bitblaster->bits(assertion);
      assert(!bits.empty());
      d_cnf_encoder->encode(bits[0], true);
    }
    d_assertions.clear();
  }

  for (const Node& assumption : d_assumptions)
  {
    ClauseKind kind = d_solver_state.is_interpol_conj(assumption)
                          ? ClauseKind::B
                          : ClauseKind::A;
    d_interpol_sat_solver->set_clause_label(kind);
    const auto& bits = d_bitblaster->bits(assumption);
    assert(!bits.empty());
    util::Timer timer(d_stats.time_encode);
    d_cnf_encoder->encode(bits[0], true);
    d_sat_solver->assume(bits[0].get_id());
  }

  // Update CNF statistics
  update_statistics();

  d_solver_state.print_statistics();
  util::Timer timer(d_stats.time_sat);
  d_last_result = d_sat_solver->solve();

  return d_last_result;
}

Node
BvInterpolationSolver::value(const Node& term)
{
  assert(BvSolver::is_leaf(term));
  assert(term.type().is_bool() || term.type().is_bv());

  const auto& bits = d_bitblaster->bits(term);
  const Type& type = term.type();
  NodeManager& nm  = d_env.nm();

  // Return default value if not bit-blasted
  if (bits.empty())
  {
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
  return nm.mk_value(val);
}

void
BvInterpolationSolver::unsat_core(std::vector<Node>& core) const
{
  assert(d_last_result == Result::UNSAT);
  assert(d_env.options().produce_unsat_cores());

  for (const Node& assumption : d_assumptions)
  {
    const auto& bits = d_bitblaster->bits(assumption);
    assert(bits.size() == 1);
    if (d_sat_solver->failed(bits[0].get_id()))
    {
      core.push_back(assumption);
    }
  }
}

/* --- BvInterpolationSolver private ---------------------------------------- */

void
BvInterpolationSolver::update_statistics()
{
  d_stats.bb_num_aig_ands     = d_bitblaster->num_aig_ands();
  d_stats.bb_num_aig_consts   = d_bitblaster->num_aig_consts();
  d_stats.bb_num_aig_shared   = d_bitblaster->num_aig_shared();
  auto& cnf_stats          = d_cnf_encoder->statistics();
  d_stats.bb_num_cnf_vars     = cnf_stats.num_vars;
  d_stats.bb_num_cnf_clauses  = cnf_stats.num_clauses;
  d_stats.bb_num_cnf_literals = cnf_stats.num_literals;
}

BvInterpolationSolver::Statistics::Statistics(util::Statistics& stats,
                                              const std::string& prefix)
    : time_sat(stats.new_stat<util::TimerStatistic>(prefix + "time_sat")),
      time_interpol(
          stats.new_stat<util::TimerStatistic>(prefix + "time_interpol")),
      time_bitblast(
          stats.new_stat<util::TimerStatistic>(prefix + "time_bitblast")),
      time_label(stats.new_stat<util::TimerStatistic>(prefix + "time_label")),
      time_encode(stats.new_stat<util::TimerStatistic>(prefix + "time_encode")),
      size_interpolant(stats.new_stat<uint64_t>(prefix + "size_interpolant")),
      bb_num_aig_ands(stats.new_stat<uint64_t>(prefix + "bb::aig::num_ands")),
      bb_num_aig_consts(
          stats.new_stat<uint64_t>(prefix + "bb::aig::num_consts")),
      bb_num_aig_shared(
          stats.new_stat<uint64_t>(prefix + "bb::aig::num_shared")),
      bb_num_cnf_vars(stats.new_stat<uint64_t>(prefix + "bb::cnf::num_vars")),
      bb_num_cnf_clauses(
          stats.new_stat<uint64_t>(prefix + "bb::cnf::num_clauses")),
      bb_num_cnf_literals(
          stats.new_stat<uint64_t>(prefix + "bb::cnf::num_literals"))
{
}

}  // namespace bzla::bv
