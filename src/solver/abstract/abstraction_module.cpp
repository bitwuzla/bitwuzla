/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/abstract/abstraction_module.h"

#include <algorithm>

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "solver/abstract/abstraction_lemmas.h"
#include "util/hash.h"

namespace bzla::abstract {

using namespace node;

/* --- AbstractionModule public --------------------------------------------- */

AbstractionModule::AbstractionModule(Env& env, SolverState& state)
    : d_env(env),
      d_logger(env.logger()),
      d_solver_state(state),
      d_rewriter(env.rewriter()),
      d_active_term_abstractions(state.backtrack_mgr()),
      d_active_assertion_abstractions(state.backtrack_mgr()),
      d_assertion_abstractions_cache(state.backtrack_mgr()),
      d_lemma_cache(state.backtrack_mgr()),
      // Some lemmas are not valid for bit-vectors of size 1 or 2. Hence, we
      // only start abstracting from size 3+ instead of guarding each lemma
      // separately.
      d_opt_minimum_size(std::max(env.options().abstraction_bv_size(),
                                  static_cast<uint64_t>(3))),
      d_opt_eager_refine(env.options().abstraction_eager_refine()),
      d_opt_value_inst_limit(env.options().abstraction_value_limit()),
      d_opt_value_inst_only(env.options().abstraction_value_only()),
      d_opt_abstract_assertions(env.options().abstraction_assert()),
      d_opt_assertion_refinements(env.options().abstraction_assert_refs()),
      d_opt_inc_bitblast(env.options().abstraction_inc_bitblast()),
      d_stats(env.statistics(), "solver::abstract::")
{
  bool opt_initial_lemmas = env.options().abstraction_initial_lemmas();

  NodeManager& nm = d_env.nm();
  if (env.options().abstraction_bv_mul())
  {
    d_abstr_lemmas[Kind::BV_MUL] =
        mk_lemmas(nm, Kind::BV_MUL, opt_initial_lemmas);
  }

  if (env.options().abstraction_bv_udiv())
  {
    d_abstr_lemmas[Kind::BV_UDIV] =
        mk_lemmas(nm, Kind::BV_UDIV, opt_initial_lemmas);
  }

  if (env.options().abstraction_bv_urem())
  {
    d_abstr_lemmas[Kind::BV_UREM] =
        mk_lemmas(nm, Kind::BV_UREM, opt_initial_lemmas);
  }

  if (env.options().abstraction_ite())
  {
    d_abstr_lemmas.try_emplace(Kind::ITE);
  }

  if (env.options().abstraction_bv_add())
  {
    d_abstr_lemmas[Kind::BV_ADD] =
        mk_lemmas(nm, Kind::BV_ADD, opt_initial_lemmas);
  }
}

AbstractionModule::~AbstractionModule() {}

void
AbstractionModule::register_abstraction(const Node& node)
{
  assert(is_abstraction(node));
  if (d_opt_abstract_assertions
      && d_abstraction_cache_assertions.find(node)
             != d_abstraction_cache_assertions.end())
  {
    d_active_assertion_abstractions.push_back(node);
  }
  else
  {
    d_active_term_abstractions.push_back(node);
  }
}

bool
AbstractionModule::is_abstraction(const Node& node)
{
  return node.kind() == Kind::AM_ABSTRACT;
}

void
AbstractionModule::check()
{
  Log(1);
  Log(1) << "*** check abstractions";
  util::Timer timer(d_stats.time_check);
  ++d_stats.num_checks;

  d_added_lemma = false;

  // New abstraction may be added while checking
  for (size_t i = 0; i < d_active_term_abstractions.size(); ++i)
  {
    // Do not use reference here, since d_active_abstractions may change when
    // calling check_term_abstraction().
    const Node abstr_term = d_active_term_abstractions[i];
    check_term_abstraction(abstr_term);
  }

  // Check abstracted assertions.
  // Assertion abstractions must be checked after we are done checking that
  // all term abstractions are consistent.
  if (!d_added_lemma && d_opt_abstract_assertions)
  {
    check_assertion_abstractions();
  }

  // Abstraction refinements that are added as "last resort" are only added if
  // we expanded all violated assertions.
  // This includes:
  //   - value instantiation lemmas
  //   - bit-blasting lemmas
  if (!d_added_lemma)
  {
    for (const auto& [node, lemma, lk] : d_lemma_buffer)
    {
      if (lemma_no_abstract(lemma, lk))
      {
        // Increment counter for value instantiations
        if (is_lemma_kind_value(lk))
        {
          ++d_value_insts[node];
        }
      }
    }
  }
  d_lemma_buffer.clear();
}

const Node&
AbstractionModule::process(const Node& term)
{
  NodeManager& nm = d_env.nm();

  node_ref_vector visit{term};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_abstraction_cache.try_emplace(cur);
    if (inserted)
    {
      // No need to go below quantifiers since abstraction will happen when
      // quantifier instantiation is added.
      if (cur.kind() == Kind::FORALL || cur.kind() == Kind::AM_ABSTRACT)
      {
        it->second = cur;
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      Node rebuilt = d_env.rewriter().rewrite(
          utils::rebuild_node(nm, cur, d_abstraction_cache));

      if (abstract(rebuilt))
      {
        it->second = nm.mk_node(Kind::AM_ABSTRACT, {rebuilt});
        ++d_stats.num_terms;
        d_stats.terms << rebuilt.kind();
      }
      else
      {
        it->second = rebuilt;
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return d_abstraction_cache.at(term);
}

const Node&
AbstractionModule::process_assertion(const Node& assertion, bool is_lemma)
{
  Log(2) << "process assertion: " << assertion << " (" << is_lemma << ")";
  const Node& processed = process(assertion);

  // Do not abstract assertions that are values, consts or lemmas.
  if (d_opt_abstract_assertions && !processed.is_value()
      && !processed.is_const() && !is_lemma)
  {
    if (processed.kind() != Kind::AM_ABSTRACT)
    {
      Node abstr = d_env.nm().mk_node(Kind::AM_ABSTRACT, {processed});
      Log(2) << "abstract assertion: " << processed << " (abstr: " << abstr
             << ", orig: " << assertion << ")";
      d_abstraction_cache[abstr] = abstr;
      d_abstraction_cache_assertions.emplace(abstr, assertion);
      return d_abstraction_cache.at(abstr);
    }
    return processed;
  }

  // Map original assertion to processed assertion for unsat cores.
  if (processed != assertion)
  {
    d_abstraction_cache_assertions.emplace(processed, assertion);
  }

  return processed;
}

bool
AbstractionModule::is_assertion_with_abstractions(const Node& assertion)
{
  auto it = d_abstraction_cache_assertions.find(assertion);
  return it != d_abstraction_cache_assertions.end() && it->second != assertion;
}

const Node&
AbstractionModule::get_original_assertion(const Node& processed_assertion)
{
  auto it = d_abstraction_cache_assertions.find(processed_assertion);
  assert(it != d_abstraction_cache_assertions.end());
  return it->second;
}

bool
AbstractionModule::is_processed(const Node& node)
{
  auto it = d_abstraction_cache.find(node);
  return it != d_abstraction_cache.end() && it->second != node;
}

const Node&
AbstractionModule::get_processed(const Node& node)
{
  auto it = d_abstraction_cache.find(node);
  assert(it != d_abstraction_cache.end());
  return it->second;
}

Node
AbstractionModule::remove_abstractions(const Node& node) const
{
  NodeManager& nm = d_env.nm();

  std::unordered_map<Node, Node> cache;
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.try_emplace(cur);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.kind() == Kind::AM_ABSTRACT)
      {
        it->second = cache.at(cur[0]);
      }
      else
      {
        it->second = utils::rebuild_node(nm, cur, cache);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(node);
}

/* --- AbstractionModule private -------------------------------------------- */

bool
AbstractionModule::abstract(const Node& node) const
{
  Kind k = node.kind();
  assert(d_abstr_lemmas.find(k) == d_abstr_lemmas.end()
         || KindInfo::num_children(k) > 1);
  return d_abstr_lemmas.find(k) != d_abstr_lemmas.end()
         && d_opt_minimum_size > 0 && node[1].type().is_bv()
         && node[1].type().bv_size() >= d_opt_minimum_size;
}

bool
AbstractionModule::check_lemma(const AbstractionLemma* lem,
                               const Node& val_x,
                               const Node& val_s,
                               const Node& val_t,
                               const Node& x,
                               const Node& s,
                               const Node& t)
{
  Node inst = lem->instance(val_x, val_s, val_t);
  Node lemma;
  if (!inst.is_null())
  {
    inst = d_rewriter.eval(inst);
    assert(inst.is_value());
    if (!inst.value<bool>())
    {
      lemma = lem->instance(x, s, t);
    }
  }
  else
  {
    inst = lem->instance(val_x, val_s, val_t, val_x, val_s, val_t);
    if (!inst.is_null())
    {
      inst = d_rewriter.eval(inst);
      assert(inst.is_value());
      if (!inst.value<bool>())
      {
        lemma = lem->instance(val_x, val_s, val_t, x, s, t);
      }
    }
  }

  if (!lemma.is_null())
  {
    Log(2) << lem->kind() << " inconsistent";
    return lemma_no_abstract(lemma, lem->kind());
  }

  return false;
}

void
AbstractionModule::check_term_abstraction(const Node& abstr)
{
  assert(abstr.kind() == Kind::AM_ABSTRACT);

  const Node& node = abstr[0];
  Log(2) << "check abstraction: " << abstr;
  Log(2) << "abstracted node: " << abstr[0];

  Kind kind = node.kind();
  assert(d_abstr_lemmas.find(kind) != d_abstr_lemmas.end());

  if (kind == Kind::ITE)
  {
    check_term_abstraction_ite(abstr, node);
    return;
  }

  NodeManager& nm   = d_env.nm();
  const Node& x     = node[0];
  const Node& s     = node[1];
  const Node& t     = abstr;
  Node val_x        = d_solver_state.value(x);
  Node val_s        = d_solver_state.value(s);
  Node val_t        = d_solver_state.value(t);
  Node val_expected = d_rewriter.eval(nm.mk_node(kind, {val_x, val_s}));

  if (val_t == val_expected)
  {
    Log(2) << "skip: assignment correct";
    return;
  }

  Log(2) << "x: " << x;
  Log(2) << "s: " << s;
  Log(2) << "t: " << t;
  Log(2) << "val_x: " << val_x;
  Log(2) << "val_s: " << val_s;
  Log(2) << "val_t: " << val_t;

  bool added_lemma = false;
  if (!d_opt_value_inst_only)
  {
    auto it = d_abstr_lemmas.find(kind);
    assert(it != d_abstr_lemmas.end());
    const auto& to_check = it->second;
    for (const auto& lem : to_check)
    {
      added_lemma = check_lemma(lem.get(), val_x, val_s, val_t, x, s, t);
      if (!added_lemma && KindInfo::is_commutative(kind))
      {
        added_lemma = check_lemma(lem.get(), val_s, val_x, val_t, s, x, t);
      }
      if (added_lemma && !d_opt_eager_refine)
      {
        break;
      }
    }
  }

  // Inconsistent value, but no lemma violated, add value-based lemma.
  if (!added_lemma)
  {
    uint64_t limit = d_opt_value_inst_limit > 0
                         ? val_x.type().bv_size() / d_opt_value_inst_limit
                         : 0;
    if (d_value_insts[node] < limit)
    {
      assert(kind == Kind::BV_MUL || kind == Kind::BV_UDIV
             || kind == Kind::BV_UREM || kind == Kind::BV_ADD);
      LemmaKind lk = lemma_kind_value(kind);
      Log(2) << lk << " inconsistent";
      Node lemma =
          nm.mk_node(Kind::IMPLIES,
                     {nm.mk_node(Kind::AND,
                                 {
                                     nm.mk_node(Kind::EQUAL, {x, val_x}),
                                     nm.mk_node(Kind::EQUAL, {s, val_s}),
                                 }),
                      nm.mk_node(Kind::EQUAL, {t, val_expected})});
      d_lemma_buffer.emplace_back(node, lemma, lk);
      if (kind == Kind::BV_MUL && val_x == val_s)
      {
        ++d_value_insts_square[node];
      }
    }
    // Incrementally bit-blast abstracted term starting from LSB
    else if (d_opt_inc_bitblast
             && (kind == Kind::BV_MUL || kind == Kind::BV_ADD))
    {
      constexpr uint64_t increment = 32;
      const auto& bv_t = val_t.value<BitVector>();
      const auto& bv_e = val_expected.value<BitVector>();
      auto bv_xor      = bv_t.bvxor(bv_e);
      uint64_t upper               = bv_xor.count_trailing_zeros() + increment;
      uint64_t size                = bv_t.size();
      upper = std::min(upper, size) - 1;

      Node extr_x = nm.mk_node(Kind::BV_EXTRACT, {x}, {upper, 0});
      Node extr_s = nm.mk_node(Kind::BV_EXTRACT, {s}, {upper, 0});
      Node extr_t = nm.mk_node(Kind::BV_EXTRACT, {t}, {upper, 0});
      Node term   = nm.mk_node(kind, {extr_x, extr_s});
      Node lemma  = nm.mk_node(Kind::EQUAL, {extr_t, term});
      d_lemma_buffer.emplace_back(node,
                                  lemma,
                                  upper + 1 == size ? LemmaKind::BITBLAST_FULL
                                                    : LemmaKind::BITBLAST_INC);
    }
    // Use special square encoding for BV_MUL if value instantiations were all
    // square instantiations.
    else if (kind == Kind::BV_MUL && d_value_insts_square[node] > 0
             && d_value_insts_square[node] >= d_value_insts[node]
             && val_x == val_s)
    {
      d_lemma_buffer.emplace_back(
          node,
          nm.mk_node(
              Kind::IMPLIES,
              {nm.mk_node(Kind::EQUAL, {x, s}),
               nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_MUL, {x, x})})}),
          LemmaKind::BITBLAST_BV_MUL_SQUARE);
      d_value_insts_square[node] = 0;  // Reset, next time we fully bit-blast
    }
    else
    {
      // Fully bit-blast abstracted term
      Node term  = nm.mk_node(kind, {x, s});
      Node lemma = nm.mk_node(Kind::EQUAL, {t, term});
      LemmaKind lk;
      switch (kind)
      {
        case Kind::BV_MUL: lk = LemmaKind::BITBLAST_BV_MUL; break;
        case Kind::BV_UDIV: lk = LemmaKind::BITBLAST_BV_UDIV; break;
        case Kind::BV_UREM: lk = LemmaKind::BITBLAST_BV_UREM; break;
        default: lk = LemmaKind::BITBLAST_FULL;
      }
      d_lemma_buffer.emplace_back(node, lemma, lk);
    }
  }
}

void
AbstractionModule::check_term_abstraction_ite(const Node& abstr,
                                              const Node& node)
{
  const Node& c  = node[0];
  const Node& bt = node[1];
  const Node& bf = node[2];
  Node val_c     = d_solver_state.value(c);
  Node val_t     = d_solver_state.value(abstr);

  bool cond = val_c.value<bool>();
  if (cond)
  {
    Node val_bt = d_solver_state.value(bt);
    if (val_t == val_bt)
    {
      Log(2) << "skip: assignment correct";
      return;
    }
  }
  else
  {
    Node val_bf = d_solver_state.value(bf);
    if (val_t == val_bf)
    {
      Log(2) << "skip: assignment correct";
      return;
    }
  }

  NodeManager& nm = d_env.nm();
  if (cond)
  {
    lemma_no_abstract(
        nm.mk_node(Kind::IMPLIES, {c, nm.mk_node(Kind::EQUAL, {abstr, bt})}),
        LemmaKind::ITE_EXPAND);
  }
  else
  {
    lemma_no_abstract(nm.mk_node(Kind::IMPLIES,
                                 {nm.mk_node(Kind::NOT, {c}),
                                  nm.mk_node(Kind::EQUAL, {abstr, bf})}),
                      LemmaKind::ITE_EXPAND);
  }
}

bool
AbstractionModule::check_assertion_abstractions()
{
  uint64_t nadded = 0;
  NodeManager& nm = d_env.nm();
  for (size_t i = 0, size = d_active_assertion_abstractions.size(); i < size;
       ++i)
  {
    const Node& abstr = d_active_assertion_abstractions[i];
    auto it           = d_assertion_abstractions_cache.find(abstr);
    if (it != d_assertion_abstractions_cache.end())
    {
      continue;
    }
    assert(abstr.kind() == Kind::AM_ABSTRACT);
    const Node& assertion = abstr[0];
    Node val              = d_solver_state.value(assertion);
    if (!val.value<bool>())
    {
      Log(2) << "violated assertion: " << abstr;
      Log(2) << "abstr assertion:    " << assertion;
      Node lemma = nm.mk_node(Kind::EQUAL, {assertion, abstr});
      lemma_no_abstract(lemma, LemmaKind::ASSERTION);
      d_assertion_abstractions_cache.insert(abstr);
      ++nadded;
      if (nadded >= d_opt_assertion_refinements)
      {
        break;
      }
    }
  }
  return nadded > 0;
}

bool
AbstractionModule::lemma_no_abstract(const Node& lemma, LemmaKind lk)
{
  // Make sure that lemma is rewritten before adding to the cache.
  Node lem = d_rewriter.rewrite(lemma);
  // Cache lemma so that we won't consider it for abstraction.
  d_abstraction_cache.emplace(lem, lem);
  auto [it, inserted] = d_lemma_cache.insert(lem);
  assert(inserted || d_opt_eager_refine);
  if (inserted && d_solver_state.lemma(lem))
  {
    d_added_lemma = true;
    d_stats.lemmas << lk;
    return true;
  }
  return false;
}

bool
AbstractionModule::lemma_abstract(const Node& lemma, LemmaKind lk)
{
  if (d_solver_state.lemma(lemma))
  {
    d_added_lemma = true;
    d_stats.lemmas << lk;
    return true;
  }
  return false;
}

AbstractionModule::Statistics::Statistics(util::Statistics& stats,
                                          const std::string& prefix)
    : num_terms(stats.new_stat<uint64_t>(prefix + "terms::total")),
      num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      terms(stats.new_stat<util::HistogramStatistic>(prefix + "terms")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
{
}

}  // namespace bzla::abstract
