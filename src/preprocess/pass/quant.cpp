/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/quant.h"

#include <set>

#include "node/node.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* --- PassQuant public ----------------------------------------------------- */

PassQuant::PassQuant(Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "q", "quant"),
      d_bv_inverter(env),
      d_stats(env.statistics())
{
}

void
PassQuant::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  d_cache.clear();
  // First, alpha normalize all assertions.
  if (d_env.options().pp_quant_alpha())
  {
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      const Node& assertion = assertions[i];
      if (!processed(assertion))
      {
        if (assertion.node_info().quantifier)
        {
          alpha_normalize(assertions[i]);
        }
      }
    }
    std::unordered_map<Node, std::set<Node>> alpha_quants;
    std::vector<Node> quants;
    for (const auto& c : d_cache)
    {
      if (c.first.kind() == Kind::FORALL)
      {
        auto [it, _] = alpha_quants.emplace(c.second, std::set<Node>{});
        it->second.insert(c.first);
        quants.push_back(c.first);
      }
    }
    std::unordered_map<Node, Node> substs;
    for (auto& q : quants)
    {
      const Node& norm = d_cache.at(q);
      auto it          = alpha_quants.find(norm);
      assert(it != alpha_quants.end());
      if (it->second.size() > 1)
      {
        substs.emplace(q, *it->second.begin());
        d_stats.num_alpha_elim += 1;
      }
    }
    std::unordered_map<Node, Node> subst_cache;
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      const Node& assertion = assertions[i];
      if (!processed(assertion))
      {
        if (assertion.node_info().quantifier)
        {
          const Node& subst =
              utils::substitute(d_env.nm(), assertion, substs, subst_cache);
          assertions.replace(i, subst);
        }
      }
    }
    d_cache.clear();
  }
  // Then try to further simplify.
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (!processed(assertion))
    {
      if (assertion.node_info().quantifier)
      {
        const Node& processed = process(assertion);
        assertions.replace(i, processed);
        cache_assertion(processed);
      }
      cache_assertion(assertion);
    }
  }
  d_cache.clear();
}

Node
PassQuant::process(const Node& node)
{
  node_ref_vector visit{node};

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());

    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      it->second = d_env.rewriter().rewrite(
          utils::rebuild_node(d_env.nm(), cur, d_cache));
      if (it->second.kind() == Kind::FORALL)
      {
        Node elim = eliminate(it->second);
        if (elim != it->second)
        {
          assert(!elim.is_null());
          it->second = elim;
          ++d_stats.num_inv_elim;
        }
      }
    }

    visit.pop_back();
  } while (!visit.empty());

  return d_cache.at(node);
}

/* --- PassQuant private ---------------------------------------------------- */

bool
PassQuant::has_var(const Node& node, const Node& var) const
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur);
    visit.pop_back();
    if (cur == var)
    {
      return true;
    }
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

std::pair<bool, std::unordered_set<Node>>
PassQuant::has_free_vars(const Node& node) const
{
  assert(node.kind() == Kind::FORALL);
  std::unordered_set<Node> quants;
  std::vector<Node> vars;
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur);
    visit.pop_back();
    if (inserted)
    {
      if (cur.kind() == Kind::VARIABLE)
      {
        vars.push_back(cur);
      }
      else if (cur.kind() == Kind::FORALL)
      {
        quants.insert(cur[0]);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  for (const auto& v : vars)
  {
    if (quants.find(v) == quants.end())
    {
      return {true, {}};
    }
  }
  return {false, quants};
}

Node
PassQuant::find_inverse(const Node& body, const Node& var, bool negated)
{
  Node cur  = body;
  Kind kind = cur.kind();

  while (kind == Kind::NOT)
  {
    cur     = cur[0];
    kind    = cur.kind();
    negated = !negated;
  }

  if (kind == Kind::AND && !negated)
  {
    for (const Node& c : cur)
    {
      Node n = find_inverse(c, var, negated);
      if (!n.is_null())
      {
        return n;
      }
    }
    return Node();
  }

  if (kind == Kind::EQUAL && !negated && has_var(cur, var))
  {
    auto [inv, conds] = d_bv_inverter.invert(cur, var);
    if (!inv.is_null() && conds.empty() && !has_var(inv, var))
    {
      return inv;
    }
  }
  return Node();
}

Node
PassQuant::eliminate(const Node& node)
{
  util::Timer timer(d_stats.time_inv_elim);

  assert(node.kind() == Kind::FORALL);

  const Node& var = node[0];
  if (!var.type().is_bv())
  {
    return node;
  }

  Node body = node[1];
  std::vector<Node> quants;
  while (body.kind() == Kind::FORALL)
  {
    quants.push_back(body[0]);
    body = body[1];
  }

  // Given a formula (forall x. (or (not A) B)), if we find a non-negated
  // equality a = b in A (where x appears in either a or b) and can derive an
  // inverse x = t for this equality and x does not occur in t, we can replace
  // the body C with C[x/t].
  //
  // This is a more general version of destructive equality resolution (DER)
  // where a body (or (not (= x t) B) can be simplified to B[x/t] if x does not
  // occur in t.
  //
  // Hence, when trying to find such equalities, we start with negated = true.
  Node inv = find_inverse(body, var);
  if (inv.is_null())
  {
    return node;
  }
  std::unordered_map<Node, Node> substs{{var, inv}};
  std::unordered_map<Node, Node> cache;
  NodeManager& nm = d_env.nm();
  Node res        = utils::substitute(nm, body, substs, cache);
  for (auto it = quants.rbegin(); it != quants.rend(); ++it)
  {
    res = nm.mk_node(Kind::FORALL, {*it, res});
  }
  return res;
}

Node
PassQuant::get_canonical_var(const Node& var)
{
  Type type = var.type();
  auto [it, _] =
      d_alpha_vars.emplace(type, std::vector<std::pair<Node, bool>>{});
  if (it->second.empty() || it->second.back().second)
  {
    Node cvar = d_env.nm().mk_var(type);
    it->second.push_back({cvar, true});
    return cvar;
  }
  it->second.back().second = true;
  return it->second.back().first;
}

void
PassQuant::release_canonical_var(const Node& var)
{
  Type type = var.type();
  assert(d_alpha_vars.at(type).size());
  d_alpha_vars.at(type).back().second = false;
}

Node
PassQuant::substitute(const Node& node,
                      const std::unordered_map<Node, Node>& substitutions,
                      std::unordered_map<Node, Node>& cache)
{
  NodeManager& nm = d_env.nm();
  node::node_ref_vector visit{node};

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      auto its = substitutions.find(cur);
      if (its != substitutions.end() && its->second != cur)
      {
        it->second = its->second;
      }
      else
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto itc = cache.find(child);
          assert(itc != cache.end());
          assert(!itc->second.is_null());
          children.push_back(itc->second);
        }
        it->second = node::utils::rebuild_node(nm, cur, children);
        assert(!it->second.is_null());
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  auto it = cache.find(node);
  assert(it != cache.end());
  return it->second;
}
void
PassQuant::alpha_normalize(const Node& node)
{
  NodeManager& nm = d_env.nm();
  std::unordered_map<Node, Node> substs;
  std::unordered_set<Node> top_quants;
  std::vector<Node> visit{node};
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());

    if (inserted)
    {
      if (cur.kind() == Kind::FORALL)
      {
        top_quants.insert(cur);
        while (cur[0].kind() == Kind::FORALL)
        {
          // skip nested quants
          cur = cur[1];
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      it->second = d_env.rewriter().rewrite(
          utils::rebuild_node(d_env.nm(), cur, d_cache));
      if (cur.kind() == Kind::FORALL)
      {
        assert(top_quants.find(cur) != top_quants.end());
        cur = it->second;
        // Get canonical variables for all quantiers in chain.
        Node ccur = cur;
        while (ccur.kind() == Kind::FORALL)
        {
          Node q = get_canonical_var(cur[0]);
          substs.emplace(cur[0], q);
          ccur = cur[1];
        }
        // Substitute and cache.
        std::unordered_map<Node, Node> subst_cache;
        Node norm = d_env.rewriter().rewrite(
            utils::substitute(nm, cur, substs, subst_cache));
        it->second              = norm;
        auto [has_free, quants] = has_free_vars(cur);
        if (!has_free)
        {
          for (const auto& q : quants)
          {
            release_canonical_var(q);
          }
        }
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

PassQuant::Statistics::Statistics(util::Statistics& stats)
    : num_inv_elim(stats.new_stat<uint64_t>("preprocess::quant::num_inv_elim")),
      num_alpha_elim(
          stats.new_stat<uint64_t>("preprocess::quant::num_alpha_elim")),
      time_alpha(
          stats.new_stat<util::TimerStatistic>("preprocess:quant::time_alpha")),
      time_inv_elim(stats.new_stat<util::TimerStatistic>(
          "preprocess:quant::time_inv_elim"))
{
}

}  // namespace bzla::preprocess::pass
