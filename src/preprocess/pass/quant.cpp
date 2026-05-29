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
      std::vector<Node> children;
      for (const Node& child : cur)
      {
        auto iit = d_cache.find(child);
        assert(iit != d_cache.end());
        children.push_back(iit->second);
      }

      it->second = d_env.rewriter().rewrite(
          utils::rebuild_node(d_env.nm(), cur, children));
      if (it->second.kind() == Kind::FORALL)
      {
        Node elim = eliminate(it->second);
        if (elim != it->second)
        {
          assert(!elim.is_null());
          it->second = elim;
          ++d_stats.num_elim;
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

PassQuant::Statistics::Statistics(util::Statistics& stats)
    : num_elim(stats.new_stat<uint64_t>("preprocess::quant::num_elim"))
{
}

}  // namespace bzla::preprocess::pass
