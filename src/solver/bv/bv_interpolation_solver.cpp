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
#include "node/unordered_node_ref_set.h"
#include "sat/cadical.h"
#include "sat/interpolants/cadical_tracer.h"
#include "sat/interpolants/tracer_kinds.h"
#include "solver/bv/aig_bitblaster.h"
#include "solver/bv/bv_solver.h"
#include "solver/fp/fp_solver.h"
#include "solver/fp/word_blaster.h"
#include "util/printer.h"

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

  void add(int64_t lit, int64_t aig_id) override
  {
    assert(aig_id);
    // We need to notify the interpolation SAT proof tracer which AIG id the
    // following, currently encoded SAT clauses are associated with. This
    // mapping is later utilized to generate dynamic labeling of variables and
    // clauses according to the partition of the set of current assertions into
    // A and B formulas.
    d_tracer.set_current_aig_id(aig_id);

    if (lit == 0)
    {
      Log(3) << "CNF encoder: add clause";
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
  /** The associated tracer. */
  Tracer& d_tracer;
};

/* --- BvInterpolationSolver public ---------------------------------------- */

BvInterpolationSolver::BvInterpolationSolver(Env& env, SolverState& state)
    : Solver(env, state),
      backtrack::Backtrackable(state.backtrack_mgr()),
      d_stats(env.statistics(), "solver::bv::interpol::"),
      d_assertions(state.backtrack_mgr()),
      d_assumptions(state.backtrack_mgr()),
      d_lemmas(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN)
{
  d_bitblaster.reset(new AigBitblaster());
  init_sat_solver();
}

BvInterpolationSolver::~BvInterpolationSolver()
{
  d_sat_solver->solver()->disconnect_proof_tracer(d_tracer.get());
}

Node
BvInterpolationSolver::interpolant(const std::vector<Node>& A,
                                   const std::vector<Node>& B)
{
  assert(d_last_result == Result::UNSAT);

  // map SAT var to label
  std::unordered_map<int64_t, VariableKind> var_labels;
  // map SAT clause to label
  std::unordered_map<int64_t, ClauseKind> clause_labels;

  {
    util::Timer timer(d_stats.time_label);
    label_clauses(clause_labels, A, ClauseKind::A);
    label_clauses(clause_labels, B, ClauseKind::B);

    label_vars(var_labels, A, B);

    for (const auto& a : d_lemmas)
    {
      label_lemma(var_labels, clause_labels, a);
    }
  }

  log_bitblaster_cache(2);

  util::Timer timer(d_stats.time_interpol);
  Node res = d_env.rewriter().rewrite(
      d_tracer->get_interpolant(var_labels, clause_labels));
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

  if (is_lemma)
  {
    d_lemmas.insert(assertion);
  }

  // Update AIG statistics
  update_statistics();
}

Result
BvInterpolationSolver::solve()
{
  d_sat_solver->configure_terminator(d_env.terminator());
  if (d_reset_sat)
  {
    init_sat_solver();
    d_reset_sat = false;
  }

  // Bitblast and determine variable labels
  if (!d_assertions.empty())
  {
    util::Timer timer(d_stats.time_bitblast);
    for (const Node& assertion : d_assertions)
    {
      d_bitblaster->bitblast(assertion);
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
    }
  }

  // Encode

  if (!d_assertions.empty())
  {
    util::Timer timer(d_stats.time_encode);
    for (const Node& assertion : d_assertions)
    {
      const auto& bits = d_bitblaster->bits(assertion);
      assert(!bits.empty());
      d_cnf_encoder->encode(bits[0], true);
    }
  }

  for (const Node& assumption : d_assumptions)
  {
    const auto& bits = d_bitblaster->bits(assumption);
    assert(!bits.empty());
    util::Timer timer(d_stats.time_encode);
    d_cnf_encoder->encode(bits[0], false);
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
BvInterpolationSolver::init_sat_solver()
{
  if (d_sat_solver)
  {
    d_sat_solver->solver()->disconnect_proof_tracer(d_tracer.get());
  }
  d_tracer.reset(new CadicalTracer(d_env, *d_bitblaster));
  d_sat_solver.reset(new sat::Cadical());
  d_interpol_sat_solver.reset(
      new InterpolationSatSolver(d_env, *d_sat_solver, *d_tracer));
  d_sat_solver->solver()->connect_proof_tracer(d_tracer.get(), true);
  d_cnf_encoder.reset(new bitblast::AigCnfEncoder(*d_interpol_sat_solver));
}
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

void
BvInterpolationSolver::label_clauses(
    std::unordered_map<int64_t, ClauseKind>& clause_labels,
    const std::vector<Node>& nodes,
    ClauseKind kind)
{
  bv::AigBitblaster::aig_node_ref_vector visit;
  std::unordered_set<int64_t> cache;
  for (const auto& node : nodes)
  {
    const auto& bits = d_bitblaster->bits(node);
    assert(!bits.empty());
    for (const auto& aig : bits)
    {
      visit.push_back(aig);
      // Enforce A/B labeling for unit clauses (top-level assertions).
      clause_labels[aig.get_id()] = kind;
    }
  }
  do
  {
    const bitblast::AigNode& cur = visit.back();
    int64_t id                   = cur.get_id();
    visit.pop_back();

    auto [it, inserted] = cache.insert(id);
    if (!inserted)
    {
      continue;
    }

    if (cur.is_and())
    {
      visit.push_back(cur[0]);
      visit.push_back(cur[1]);
    }

    clause_labels.emplace(id, kind);
    if (cur.is_true() || cur.is_false())
    {
      clause_labels.emplace(-id, kind);
    }
  } while (!visit.empty());
}

void
BvInterpolationSolver::label_lemma(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    std::unordered_map<int64_t, sat::interpolants::ClauseKind>& clause_labels,
    const Node& node)
{
  const auto& bits = d_bitblaster->bits(node);
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    for (const auto& aig : bits)
    {
      ss << " " << aig;
    }
    Log(2) << "label_lemma: (" << ss.str() << ")";
  }

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

    auto it = var_labels.find(var);
    if (it == var_labels.end())
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
#ifndef NDEBUG
    auto [it, inserted] =
#endif
        var_labels.emplace(var, kind);
    assert(inserted);
  }

  label_clauses(clause_labels,
                {node},
                kind == VariableKind::GLOBAL || kind == VariableKind::A
                    ? ClauseKind::A
                    : ClauseKind::B);
}

void
BvInterpolationSolver::label_var(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    const bitblast::AigBitblaster::Bits& bits,
    sat::interpolants::VariableKind kind)
{
  assert(!bits.empty());
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

    if (cur.is_and())
    {
      visit.push_back(cur[0]);
      visit.push_back(cur[1]);
    }

    auto [it, inserted] = var_labels.emplace(var, kind);
    assert(kind == VariableKind::B || inserted
           || it->second == VariableKind::GLOBAL || kind == it->second);

    if (!inserted && it->second != kind && it->second != VariableKind::GLOBAL)
    {
      it->second = VariableKind::GLOBAL;
    }
  } while (!visit.empty());
}

void
BvInterpolationSolver::label_consts(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    std::unordered_map<Node, VariableKind>& term_labels,
    const std::vector<Node>& nodes,
    sat::interpolants::VariableKind kind)
{
  std::unordered_map<Node, bool> cache;
  const auto& word_blaster = d_solver_state.fp_solver().word_blaster();
  std::vector<Node> visit(nodes.begin(), nodes.end());
  do
  {
    Node cur            = visit.back();
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
        auto [it, inserted] = term_labels.emplace(cur, kind);
        if (!inserted && it->second != VariableKind::GLOBAL
            && it->second != kind)
        {
          it->second = VariableKind::GLOBAL;
        }
        if (cur.type().is_bool() || cur.type().is_bv())
        {
          const auto& bits = d_bitblaster->bits(cur);
          if (!bits.empty())
          {
            label_var(var_labels, bits, kind);
          }
          // If not bit-blasted, it is not relevant for interpolant.
        }
        else if (cur.type().is_fp())
        {
          if (word_blaster.is_word_blasted(cur))
          {
            visit.pop_back();
            visit.push_back(word_blaster.word_blasted(cur));
            continue;
          }
          // If not word-blasted or bit-blasted, it is not relevant for
          // interpolant.
        }
#ifndef NDEBUG
        else
        {
          assert(d_bitblaster->bits(cur).empty());
        }
#endif
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

void
BvInterpolationSolver::label_leafs(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    std::unordered_map<Node, VariableKind>& term_labels,
    const std::vector<Node>& nodes)
{
  const auto& word_blaster = d_solver_state.fp_solver().word_blaster();
  std::unordered_map<Node, bool> cache;
  std::vector<Node> visit(nodes.begin(), nodes.end());
  do
  {
    Node cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      if (BvSolver::is_leaf(cur) && cur.type().is_fp()
          && word_blaster.is_word_blasted(cur))
      {
        visit.push_back(word_blaster.word_blasted(cur));
      }
      continue;
    }
    else if (it->second)
    {
      it->second = false;
      if (!cur.is_const())
      {
        VariableKind k = VariableKind::GLOBAL;
        for (const auto& c : cur)
        {
          auto it = term_labels.find(c);
          assert(it != term_labels.end());
          if (it->second != VariableKind::GLOBAL)
          {
            assert(k == VariableKind::GLOBAL || k == it->second);
            k = it->second;
#ifdef NDEBUG
            break;
#endif
          }
        }
        auto [it, inserted] = term_labels.emplace(cur, k);
        if (!inserted && it->second != VariableKind::GLOBAL && it->second != k)
        {
          it->second = VariableKind::GLOBAL;
        }
      }
    }

    if (BvSolver::is_leaf(cur) && !cur.is_const())
    {
      auto it = term_labels.find(cur);
      assert(it != term_labels.end());
      const auto& bits = d_bitblaster->bits(cur);
      if (!bits.empty())
      {
        label_var(var_labels, bits, it->second);
      }
      // If not bit-blasted, it is not relevant for interpolant.
    }
    visit.pop_back();
  } while (!visit.empty());
}

void
BvInterpolationSolver::label_vars(
    std::unordered_map<int64_t, VariableKind>& var_labels,
    const std::vector<Node>& A,
    const std::vector<Node>& B)
{
  std::unordered_map<Node, VariableKind> term_labels;
  // First, explicitly label all consts (leafs) that occur in `node`. This is
  // necessary as we need to step all the way down in case of abstracted
  // terms. Else, if we only traversed through the bits of a node, we would
  // cut off above the consts that occur in the abstracted term.
  label_consts(var_labels, term_labels, A, VariableKind::A);
  label_consts(var_labels, term_labels, B, VariableKind::B);

  // map terms that are not bit-blasted to label, this is necessary to determine
  // the label of abstracted terms
  label_leafs(var_labels, term_labels, A);
  label_leafs(var_labels, term_labels, B);

  // Now, label all SAT vars while traversing from the bits of all nodes. This
  // is necessary to ensure that no AIGS associated with bits of consts that are
  // not shared between A and B get pulled into the interpolant.
  bv::AigBitblaster::aig_node_ref_vector visit;
  std::unordered_map<int64_t, bool> cache;
  for (const auto& a : A)
  {
    const auto& bits = d_bitblaster->bits(a);
    assert(!bits.empty());
    for (const auto& aig : bits)
    {
      visit.push_back(aig);
    }
  }
  for (const auto& a : B)
  {
    const auto& bits = d_bitblaster->bits(a);
    assert(!bits.empty());
    for (const auto& aig : bits)
    {
      visit.push_back(aig);
    }
  }
  do
  {
    const bitblast::AigNode& cur = visit.back();
    int64_t id                   = cur.get_id();
    int64_t var                  = std::abs(id);

    auto [it, inserted] = cache.emplace(var, true);
    if (inserted)
    {
      if (cur.is_and())
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
      continue;
    }
    else if (it->second)
    {
      it->second = false;

      auto [iit, inserted] = var_labels.emplace(var, VariableKind::GLOBAL);
      if (inserted)
      {
        assert(cur.is_and());
        VariableKind k0 = var_labels.at(std::abs(cur[0].get_id()));
        VariableKind k1 = var_labels.at(std::abs(cur[1].get_id()));
        assert(k0 == VariableKind::GLOBAL || k1 == VariableKind::GLOBAL
               || k0 == k1);
        iit->second = k0 != VariableKind::GLOBAL ? k0 : k1;
      }
    }

    visit.pop_back();
  } while (!visit.empty());
}

void
BvInterpolationSolver::log_bitblaster_cache(uint64_t level) const
{
  if (d_logger.is_log_enabled(level))
  {
    Log(level);
    Log(level) << "Bitblaster cache: "
               << d_bitblaster->bitblaster_cache().size() << " entries";
    Log(level);
    for (const auto& p : d_bitblaster->bitblaster_cache())
    {
      std::stringstream ss;
      ss << "@t" << p.first.id() << ": " << p.first << ": (";
      for (const auto& a : p.second)
      {
        ss << " " << a.get_id();
      }
      ss << " )";
      Log(level) << ss.str();
    }
  }
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
