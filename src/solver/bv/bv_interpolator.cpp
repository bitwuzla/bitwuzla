/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_interpolator.h"

#include <cstdint>
#include <unordered_set>

#include "env.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"
#include "sat/cadical.h"
#include "sat/interpolants/tracer.h"
#include "sat/interpolants/tracer_kinds.h"
#include "solver/bv/aig_bitblaster.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solver/bv/bv_solver.h"
#include "solver/fp/fp_solver.h"
#include "util/exceptions.h"

using namespace bzla::node;
using namespace bzla::sat::interpolants;

namespace bzla::bv {

/* --- BvInterpolator public ---------------------------------------- */

BvInterpolator::BvInterpolator(Env& env,
                               SolverState& state,
                               BvBitblastSolver& bb_solver)
    : d_stats(env.statistics(), "solver::bv::interpolator::"),
      d_env(env),
      d_logger(env.logger()),
      d_lemmas(state.lemma_cache()),
      d_bitblaster(bb_solver.bitblaster()),
      d_tracer(reinterpret_cast<sat::CadicalInterpol*>(bb_solver.sat_solver())
                   ->tracer()),
      d_word_blaster(state.fp_solver().word_blaster())
{
}

BvInterpolator::~BvInterpolator() {}

Node
BvInterpolator::interpolant(const std::vector<Node>& ppA,
                            const std::vector<Node>& ppB)
{
  // A set empty after preprocessing
  if (ppA.empty())
  {
    return d_env.nm().mk_value(true);
  }
  // B set empty after preprocessing
  if (ppB.empty())
  {
    return d_env.nm().mk_value(false);
  }

  // map SAT var to label
  std::unordered_map<int64_t, VariableKind> var_labels;
  // map SAT clause to label
  std::unordered_map<int64_t, ClauseKind> clause_labels;

  // SAT variable with id 1 represents true/false. We always label it as GLOBAL.
  var_labels[1] = VariableKind::GLOBAL;

  std::unordered_map<Node, VariableKind> term_labels;
  {
    util::Timer timer(d_stats.time_label);
    label_clauses(clause_labels, ppA, ClauseKind::A);
    label_clauses(clause_labels, ppB, ClauseKind::B);

    label_vars(var_labels, term_labels, ppA, ppB);

    for (const auto& a : d_lemmas)
    {
      label_lemma(var_labels, clause_labels, term_labels, a);
    }
  }

  log_bitblaster_cache(2);

  util::Timer timer(d_stats.time_interpol);
  Node res = d_tracer->get_interpolant(var_labels, clause_labels, term_labels);
  assert(!res.is_null());
  res = d_env.rewriter().rewrite(res);
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

#ifndef NDEBUG
  {
    node_ref_vector visit{ppA.begin(), ppA.end()};
    visit.insert(visit.end(), ppB.begin(), ppB.end());
    visit.insert(visit.end(), d_lemmas.begin(), d_lemmas.end());
    unordered_node_ref_set cache;
    do
    {
      const Node& cur = visit.back();
      visit.pop_back();
      cache.insert(cur);
      assert(term_labels.find(cur) != term_labels.end());
    } while (!visit.empty());
  }
#endif

  return res;
}

/* --- BvInterpolator private ---------------------------------------- */

void
BvInterpolator::label_clauses(
    std::unordered_map<int64_t, ClauseKind>& clause_labels,
    const std::vector<Node>& nodes,
    ClauseKind kind)
{
  bv::AigBitblaster::aig_node_ref_vector visit;
  std::unordered_set<int64_t> cache;
  for (const auto& node : nodes)
  {
    const auto& bits = d_bitblaster.bits(node);
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
    // We always add (1 0) to the SAT solver to enforce correct true/false
    // handling. However, this clause is not necessarily added as clause with
    // id 1. Thus, we need to explicitly add the labeling of this clause and its
    // negation here. Note that if the clause or its negation is a top-level
    // unit in A or B, its labeling will be reset above when enforcing A/B
    // labeling for units to ensure correct assignment of clauses to A/B.
    if (cur.is_true() || cur.is_false())
    {
      clause_labels.emplace(-id, kind);
    }
  } while (!visit.empty());
}

void
BvInterpolator::label_lemma(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    std::unordered_map<int64_t, sat::interpolants::ClauseKind>& clause_labels,
    std::unordered_map<Node, sat::interpolants::VariableKind>& term_labels,
    const Node& node)
{
  // label SAT variables
  const auto& bits = d_bitblaster.bits(node);
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

    auto [it, inserted] = var_labels.emplace(var, VariableKind::NONE);
    if (inserted)
    {
      if (cur.is_and())
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
      continue;
    }
    else if (it->second == VariableKind::NONE)
    {
      if (!cur.is_and())
      {
        throw Unsupported(
            "interpolation queries with lemmas that use fresh variables not "
            "supported");
      }
      // not labeled, label based on children
      VariableKind k0 = var_labels.at(std::abs(cur[0].get_id()));
      VariableKind k1 = var_labels.at(std::abs(cur[1].get_id()));
      if (k0 != k1 && k0 != VariableKind::GLOBAL && k1 != VariableKind::GLOBAL)
      {
        throw Unsupported(
            "interpolation queries with mixed lemmas not supported");
      }
      it->second = k0 == VariableKind::GLOBAL ? k1 : k0;
    }

    visit.pop_back();
  } while (!visit.empty());

  // the determined kind of the lemma
  VariableKind kind = var_labels.at(std::abs(bits[0].get_id()));

  // label unlabeled terms
  std::unordered_map<Node, bool> ncache;
  std::vector<Node> nvisit{node};
  do
  {
    Node cur            = nvisit.back();
    auto [it, inserted] = ncache.emplace(cur, true);
    if (inserted)
    {
      nvisit.insert(nvisit.end(), cur.begin(), cur.end());
      // we don't need to push word-blasted terms here as they should appear
      // in lemmas if relevant
      continue;
    }
    else if (it->second)
    {
      it->second          = false;
      auto [it, inserted] = term_labels.emplace(cur, VariableKind::GLOBAL);
      if (!inserted)
      {
        continue;
      }
      assert(!cur.is_const());
      VariableKind k = VariableKind::GLOBAL;
      for (const auto& c : cur)
      {
        auto it = term_labels.find(c);
        assert(it != term_labels.end());
        if (it->second != VariableKind::GLOBAL)
        {
          if (k != VariableKind::GLOBAL && k != it->second)
          {
            throw Unsupported(
                "interpolation queries with mixed lemmas not supported");
          }
          k = it->second;
#ifdef NDEBUG
          break;
#endif
        }
      }
      if (!inserted && it->second != VariableKind::GLOBAL && it->second != k)
      {
        it->second = VariableKind::GLOBAL;
      }
    }
    nvisit.pop_back();
  } while (!nvisit.empty());

  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    for (const auto& aig : bits)
    {
      ss << " " << aig;
    }
    Log(2) << "label lemma: " << node << " ["
           << (kind == VariableKind::GLOBAL || kind == VariableKind::A
                   ? ClauseKind::A
                   : ClauseKind::B)
           << "]: aig: " << ss.str();
  }

  label_clauses(clause_labels,
                {node},
                kind == VariableKind::GLOBAL || kind == VariableKind::A
                    ? ClauseKind::A
                    : ClauseKind::B);
}

void
BvInterpolator::label_var(
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
BvInterpolator::label_consts(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    std::unordered_map<Node, VariableKind>& term_labels,
    const std::vector<Node>& nodes,
    sat::interpolants::VariableKind kind)
{
  std::unordered_map<Node, bool> cache;
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
          const auto& bits = d_bitblaster.bits(cur);
          if (!bits.empty())
          {
            label_var(var_labels, bits, kind);
          }
          // If not bit-blasted, it is not relevant for interpolant.
        }
        else if (cur.type().is_fp() || cur.type().is_rm())
        {
          if (d_word_blaster.is_word_blasted(cur))
          {
            visit.pop_back();
            visit.push_back(d_word_blaster.word_blasted(cur));
            continue;
          }
          // If not word-blasted or bit-blasted, it is not relevant for
          // interpolant.
        }
#ifndef NDEBUG
        else
        {
          assert(d_bitblaster.bits(cur).empty());
        }
#endif
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

void
BvInterpolator::label_terms_and_leafs(
    std::unordered_map<int64_t, sat::interpolants::VariableKind>& var_labels,
    std::unordered_map<Node, VariableKind>& term_labels,
    const std::vector<Node>& nodes)
{
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
          && d_word_blaster.is_word_blasted(cur))
      {
        visit.push_back(d_word_blaster.word_blasted(cur));
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
            break;
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
      const auto& bits = d_bitblaster.bits(cur);
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
BvInterpolator::label_vars(
    std::unordered_map<int64_t, VariableKind>& var_labels,
    std::unordered_map<Node, VariableKind>& term_labels,
    const std::vector<Node>& ppA,
    const std::vector<Node>& ppB)
{
  // First, explicitly label all consts (leafs) that occur in `node` based on
  // their occurrence in the original assertions.
  // This is necessary as we need to step all the way down in case of abstracted
  // terms. Else, if we only traversed through the bits of a node, we would cut
  // off above the consts that occur in the abstracted term.
  // We do this with respect to the preprocessed assertions, which is safe since
  // we only allow assertion-local simplifications in preprocessing when
  // interpolants generation is enabled. Simplifications due to assertion-local
  // preprocessing will not transform assertions such that the label and/or
  // shared-ness of symbols will change across A/B (if shared-ness is simplified
  // away, the shared symbol is not relevant for the interpolant).
  label_consts(var_labels, term_labels, ppA, VariableKind::A);
  label_consts(var_labels, term_labels, ppB, VariableKind::B);

  // Map terms that are not bit-blasted to a label. This is necessary to
  // determine the label of abstracted terms.
  label_terms_and_leafs(var_labels, term_labels, ppA);
  label_terms_and_leafs(var_labels, term_labels, ppB);

  // Now, label all SAT vars while traversing from the bits of all nodes. This
  // is necessary to ensure that no AIGS associated with bits of consts that are
  // not shared between A and B get pulled into the interpolant.
  bv::AigBitblaster::aig_node_ref_vector visit;
  std::unordered_map<int64_t, bool> cache;
  for (const auto& a : ppA)
  {
    const auto& bits = d_bitblaster.bits(a);
    assert(!bits.empty());
    for (const auto& aig : bits)
    {
      visit.push_back(aig);
    }
  }
  for (const auto& a : ppB)
  {
    const auto& bits = d_bitblaster.bits(a);
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
BvInterpolator::log_bitblaster_cache(uint64_t level) const
{
  if (d_logger.is_log_enabled(level))
  {
    Log(level);
    Log(level) << "Bitblaster cache: " << d_bitblaster.bitblaster_cache().size()
               << " entries";
    Log(level);
    for (const auto& p : d_bitblaster.bitblaster_cache())
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

BvInterpolator::Statistics::Statistics(util::Statistics& stats,
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
