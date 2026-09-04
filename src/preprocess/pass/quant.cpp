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

#include "node/node.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* --- PassQuant public ----------------------------------------------------- */

PassQuant::PassQuant(Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "q", "quant"),
      d_bv_inverter(env),
      d_bound_vars(backtrack_mgr),
      d_opt_quant_alpha(env.options().pp_quant_alpha()),
      d_stats(env.statistics())
{
}

void
PassQuant::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  d_cache.clear();
  d_alpha_cache.clear();
  d_alpha_reps.clear();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    Node assertion = assertions[i];
    if (!processed(assertion))
    {
      if (assertion.node_info().quantifier)
      {
        Node processed = process(assertion);
        assertions.replace(i, processed);
        // Cache the result, not the original, else duplicates are skipped.
        cache_assertion(processed);
      }
      else
      {
        cache_assertion(assertion);
      }
    }
  }
  d_cache.clear();
  d_alpha_cache.clear();
  d_alpha_reps.clear();
}

namespace {
Node
mk_fresh_var(NodeManager& nm, const Node& var)
{
  assert(var.kind() == Kind::VARIABLE);
  return nm.mk_var(var.type(), var.symbol());
}
}  // namespace

Node
PassQuant::process(const Node& node)
{
  NodeManager& nm    = d_env.nm();
  Rewriter& rewriter = d_env.rewriter();
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
      Node res = rewriter.rewrite(utils::rebuild_node(nm, cur, d_cache));

      // Make binding of quantified variables unique, i.e., no binders are
      // shared, neither nested nor across assertions. Note that unique binders
      // are already guaranteed through the parser, but via the API, sharing
      // binders is not disallowed.
      if (cur.kind() == Kind::FORALL)
      {
        d_stats.num_quants += 1;
        auto [_, vinserted] = d_bound_vars.insert(cur[0].id());
        if (!vinserted)
        {
          // Shared binder, uniquify.
          // Note: The fresh variable must not be mapped to d_cache[cur[0]].
          //       The mapping is only valid below this binder, whereas
          //       d_cache[cur[0]] is used to rebuild the nodes of the
          //       binder that keeps the original variable.
          Node fresh_var = mk_fresh_var(nm, cur[0]);
          d_bound_vars.insert(fresh_var.id());
          res            = uniquify_variable(cur, fresh_var);
          assert(!res.is_null());
          assert(res.kind() == Kind::FORALL);
          assert(cur != node || !has_free_vars(res).first);
        }
      }

      if (res.kind() == Kind::FORALL)
      {
        Node elim = eliminate(res);
        if (elim != res)
        {
          assert(!elim.is_null());
          res = elim;
          ++d_stats.num_inv_elim;
        }
      }
      it->second = res;
    }

    visit.pop_back();
  } while (!visit.empty());

  auto it = d_cache.find(node);
  assert(it != d_cache.end());
  if (d_opt_quant_alpha && it->second.node_info().quantifier)
  {
    it->second = alpha_normalize(it->second);
  }
  return d_cache.at(node);
}

/* --- PassQuant private ---------------------------------------------------- */

Node
PassQuant::uniquify_variable(const Node& node, const Node& fresh_var)
{
  util::Timer timer(d_stats.time_uniquify);

  assert(node.kind() == Kind::FORALL);

  NodeManager& nm    = d_env.nm();
  Rewriter& rewriter = d_env.rewriter();
  const Node& var    = node[0];
  const Node& body   = d_cache.at(node[1]);  // may already be rewritten

  // Map nodes to true if they reference `var`. These are the nodes that need
  // to be rebuilt with `fresh_var`.
  // Note: We do not descend into binders that rebind `var` (shadowing). Every
  //       occurrence of `var` below such a binder is bound by that binder, and
  //       substituting it would move it into the scope of `fresh_var`, changing
  //       the semantics of `node` (not shadowing anymore).
  //       Shadowed subterms are thus unaffected by the substitution and are
  //       not rebuilt with `fresh_var`. Shadowing binders are uniquified by
  //       process(), which uniquifies every binder whose variable is already
  //       bound elsewhere.
  std::unordered_map<Node, bool> references;
  std::vector<Node> visit{body};
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = references.emplace(cur, false);

    if (inserted)
    {
      if (cur.num_children() && (cur.kind() != Kind::FORALL || cur[0] != var))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      if (cur == var)
      {
        it->second = true;
      }
    }
    else if (!it->second && cur.num_children()
             && (cur.kind() != Kind::FORALL || cur[0] != var))
    {
      for (const Node& child : cur)
      {
        if (references.at(child))
        {
          it->second = true;
          break;
        }
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  // A binder that references `var` is copied with a fresh variable (see
  // below), and that requires rebuilding its *entire* body: occurrences of its
  // variable may sit in subterms that do not reference `var`, which would
  // otherwise be left on the original variable.
  {
    std::unordered_set<Node> cache;
    for (const auto& [n, refs] : references)
    {
      // As above, we do not descend into binders that rebind `var`.
      if (refs && n.kind() == Kind::FORALL)
      {
        assert(n[0] != var);
        visit.push_back(n[1]);
      }
      while (!visit.empty())
      {
        Node cur = visit.back();
        visit.pop_back();
        // As above, we do not descend into binders that rebind `var`.
        if (cur.kind() == Kind::FORALL && cur[0] == var)
        {
          continue;
        }
        if (!cache.insert(cur).second)
        {
          continue;
        }
        references.at(cur) = true;
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }

  // Rebuild with `fresh_var`.
  std::unordered_map<Node, Node> cache{{var, fresh_var}};
  visit.push_back(body);
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());

    if (inserted)
    {
      if (!references.at(cur))
      {
        it->second = cur;
      }
      else
      {
        if (cur.kind() == Kind::FORALL)
        {
          // The DAG below this binder references `var` and is thus rebuilt,
          // while the original binder stays in use elsewhere. Uniquify its
          // variable to not introduce a new shared binder.
          auto [vit, vinserted] = cache.emplace(cur[0], Node());
          if (vinserted)
          {
            vit->second = mk_fresh_var(nm, cur[0]);
            d_bound_vars.insert(vit->second.id());
          }
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
    }
    else if (it->second.is_null())
    {
      it->second = rewriter.rewrite(utils::rebuild_node(nm, cur, cache));
    }
    visit.pop_back();
  } while (!visit.empty());

  return rewriter.rewrite(
      nm.mk_node(Kind::FORALL, {fresh_var, cache.at(body)}));
}

std::pair<bool, std::unordered_set<Node>>
PassQuant::has_free_vars(const Node& node) const
{
  std::unordered_set<Node> quants;
  std::vector<Node> vars;
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur = visit.back();
    visit.pop_back();
    if (cur != node && d_alpha_reps.find(cur) != d_alpha_reps.end())
    {
      continue;
    }
    auto [it, inserted] = cache.emplace(cur);
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
  util::Timer timer(d_stats.time_inv_elim_find_inv);

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

  // Given a formula (forall x. (or (not A) B)), if we find a non-negated
  // equality x = t in A  and x does not occur in t, we can replace the body
  // C with C[x/t]. This is also referred to as destructive equality resolution
  // (DER) in the literature.
  //
  // If x is a bit-vector variable, we can generalize by means of inverse
  // computation: if we find a non-negated equality a = b in A (where x appears
  // in either a or b) and can derive an inverse x = t for this equality and x
  // does not occur in t, we can replace the body C with C[x/t].

  if (kind == Kind::EQUAL && !negated && utils::has_x(cur, var))
  {
    if (var.type().is_bv() || var.type().is_bool())
    {
      auto [inv, conds] = d_bv_inverter.invert(cur, var);
      assert(!utils::has_x(inv, var));
      if (!inv.is_null() && conds.empty())
      {
        return inv;
      }
    }
    else
    {
      if (cur[0] == var && !utils::has_x(cur[1], var))
      {
        return cur[1];
      }
      if (cur[1] == var && !utils::has_x(cur[0], var))
      {
        return cur[0];
      }
    }
  }
  return Node();
}

Node
PassQuant::eliminate(const Node& node)
{
  util::Timer timer_inv_elim(d_stats.time_inv_elim);

  assert(node.kind() == Kind::FORALL);

  const Node& var = node[0];
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
  // Note: find_inverse() also handles the common DER case for non-BV vars.
  Node inv = find_inverse(body, var);
  if (inv.is_null())
  {
    return node;
  }
  assert(!utils::has_x(inv, var));
  util::Timer timer_inv_elim_subst(d_stats.time_inv_elim_subst);
  std::unordered_map<Node, Node> substs{{var, inv}};
  std::unordered_map<Node, Node> cache;
  NodeManager& nm = d_env.nm();
  Node res        = utils::substitute(nm, body, substs, cache);
  for (auto it = quants.rbegin(); it != quants.rend(); ++it)
  {
    res = nm.mk_node(Kind::FORALL, {*it, res});
  }
  return d_env.rewriter().rewrite(res);
}

Node
PassQuant::get_canonical_var(const Node& var)
{
  Type type = var.type();
  auto [it, _] =
      d_alpha_vars.emplace(type, std::vector<std::pair<Node, bool>>{});
  for (auto& v : it->second)
  {
    if (!v.second)
    {
      v.second = true;
      return v.first;
    }
  }
  Node cvar = d_env.nm().mk_var(type);
  it->second.push_back({cvar, true});
  return cvar;
}

void
PassQuant::release_canonical_var(const Node& var)
{
  Type type = var.type();
  assert(d_alpha_vars.at(type).size());
  auto& vars = d_alpha_vars.at(type);
  for (size_t i = 0, size = vars.size(); i < size; ++i)
  {
    auto& v = vars[size - i - 1];
    if (v.first == var && v.second)
    {
      v.second = false;
      return;
    }
  }
}

Node
PassQuant::alpha_normalize(const Node& node)
{
  util::Timer timer(d_stats.time_alpha_elim);

  NodeManager& nm    = d_env.nm();
  Rewriter& rewriter = d_env.rewriter();
  std::unordered_map<Node, Node> substs;
  std::unordered_map<Node, Node> repr_substs;
  std::unordered_set<Node> top_quants;
  std::vector<Node> visit{node};

  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = d_alpha_cache.emplace(cur, Node());

    if (inserted)
    {
      if (cur.kind() == Kind::FORALL)
      {
        top_quants.insert(cur);
        while (cur[1].kind() == Kind::FORALL)
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
      if (cur.kind() == Kind::FORALL)
      {
        assert(top_quants.find(cur) != top_quants.end());
        // Get canonical variables for all quantiers in chain.
        Node body = cur;
        std::vector<Node> args;
        while (body.kind() == Kind::FORALL)
        {
          Node var = get_canonical_var(body[0]);
          args.push_back(var);
          substs.emplace(body[0], var);
          body = body[1];
        }
        // Substitute and cache.
        std::unordered_map<Node, Node> subst_cache;
        Node norm = rewriter.rewrite(
            utils::substitute(nm, d_alpha_cache.at(body), substs, subst_cache));
        args.push_back(norm);
        it->second              = utils::mk_nary(nm, Kind::FORALL, args);
        auto [has_free, quants] = has_free_vars(it->second);
        if (!has_free)
        {
          // Alpha equivalent quantifiers are mapped to the first one
          // encountered. Note: `node` is registered below, after substituting
          // the alpha-equivalent quants in its body with their representatives.
          if (cur != node)
          {
            auto [ait, ainserted] = d_alpha_reps.emplace(it->second, cur);
            if (!ainserted && ait->second != cur)
            {
              repr_substs.emplace(cur, ait->second);
              d_stats.num_alpha_elim += 1;
            }
          }
          for (const auto& q : quants)
          {
            release_canonical_var(q);
          }
        }
      }
      else
      {
        it->second =
            rewriter.rewrite(utils::rebuild_node(nm, cur, d_alpha_cache));
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  const Node& norm = d_alpha_cache.at(node);
  assert(!has_free_vars(norm).first);
  // Substitute alpha-equivalent quantifiers with their representatives.
  std::unordered_map<Node, Node> subst_cache;
  Node res =
      rewriter.rewrite(utils::substitute(nm, node, repr_substs, subst_cache));
  auto [it, inserted] = d_alpha_reps.emplace(norm, res);
  if (!inserted && it->second != res)
  {
    d_stats.num_alpha_elim += 1;
  }
  return it->second;
}

PassQuant::Statistics::Statistics(util::Statistics& stats)
    : num_alpha_elim(
          stats.new_stat<uint64_t>("preprocess::quant::num_alpha_elim")),
      num_inv_elim(stats.new_stat<uint64_t>("preprocess::quant::num_inv_elim")),
      num_quants(stats.new_stat<uint64_t>("preprocess::quant::num_quants")),
      time_alpha_elim(stats.new_stat<util::TimerStatistic>(
          "preprocess::quant::time_alpha_elim")),
      time_inv_elim(stats.new_stat<util::TimerStatistic>(
          "preprocess::quant::time_inv_elim")),
      time_inv_elim_find_inv(stats.new_stat<util::TimerStatistic>(
          "preprocess::quant::time_inv_elim_find_inv")),
      time_inv_elim_subst(stats.new_stat<util::TimerStatistic>(
          "preprocess::quant::time_inv_elim_subst")),
      time_uniquify(stats.new_stat<util::TimerStatistic>(
          "preprocess::quant::time_uniquify"))
{
}

}  // namespace bzla::preprocess::pass
