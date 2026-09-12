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

#include "node/kind_info.h"
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

/** @return True if `node` is a binder that binds `var`. */
bool
rebinds(const Node& node, const Node& var)
{
  return KindInfo::is_binder(node.kind()) && node[0] == var;
}
}  // namespace

Node
PassQuant::process(const Node& node)
{
  NodeManager& nm    = d_env.nm();
  Rewriter& rewriter = d_env.rewriter();

  node_ref_vector visit{node};
  std::unordered_set<Node> inner_quants;

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());

    if (inserted)
    {
      if (cur.kind() == Kind::FORALL && cur[1].kind() == Kind::FORALL)
      {
        inner_quants.insert(cur[1]);
      }

      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      assert(cur.kind() != Kind::EXISTS);

      Node res = rewriter.rewrite(utils::rebuild_node(nm, cur, d_cache));

      // Make binding of variables unique, i.e., no binders are shared,
      // neither nested nor across assertions. Note that unique binders are
      // already guaranteed through the parser, but via the API, sharing
      // binders is not disallowed.
      if (KindInfo::is_binder(cur.kind()))
      {
        if (KindInfo::is_quant(cur.kind()))
        {
          d_stats.num_quants += 1;
        }
        // Record the binder that owns `cur[0]`. Reaching the same binder node
        // again (e.g., a quantifier shared between assertions that are
        // processed in different calls to apply(), where d_cache does not
        // persist) is not sharing and must not be uniquified.
        auto [itv, vinserted] = d_bound_vars.emplace(cur[0].id(), cur.id());
        if (!vinserted && itv->second != cur.id())
        {
          // Shared binder, uniquify.
          // Note: The fresh variable must not be mapped to d_cache[cur[0]].
          //       The mapping is only valid below this binder, whereas
          //       d_cache[cur[0]] is used to rebuild the nodes of the
          //       binder that keeps the original variable.
          // Note: The fresh variable is not recorded in d_bound_vars here.
          //       It is bound by exactly one, newly created binder, which is
          //       not part of the DAG we are traversing. It is recorded if
          //       that binder is processed again in a later call to apply().
          Node fresh_var = mk_fresh_var(nm, cur[0]);
          res = uniquify_variable(cur, fresh_var);
          assert(!res.is_null());
          assert(res.kind() == cur.kind());
          assert(cur != node || !has_free_vars(res).first);
        }
      }

      // We do not call eliminate on each quantifier in a chain, bottom up, but
      // process such chains in batch in eliminate(). This avoids quadratic
      // overhead on quantifiers with large prefix.
      if (res.kind() == Kind::FORALL
          && inner_quants.find(cur) == inner_quants.end())
      {
        Node elim = eliminate(res);
        if (elim != res)
        {
          assert(!elim.is_null());
          res = elim;
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

  assert(KindInfo::is_binder(node.kind()));

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
      if (cur.num_children() && !rebinds(cur, var))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      if (cur == var)
      {
        it->second = true;
      }
    }
    else if (!it->second && cur.num_children() && !rebinds(cur, var))
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
      if (refs && KindInfo::is_binder(n.kind()))
      {
        assert(n[0] != var);
        visit.push_back(n[1]);
      }
      while (!visit.empty())
      {
        Node cur = visit.back();
        visit.pop_back();
        // As above, we do not descend into binders that rebind `var`.
        if (rebinds(cur, var))
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
        if (KindInfo::is_binder(cur.kind()))
        {
          // The DAG below this binder references `var` and is thus rebuilt,
          // while the original binder stays in use elsewhere. Uniquify its
          // variable to not introduce a new shared binder.
          auto [vit, vinserted] = cache.emplace(cur[0], Node());
          if (vinserted)
          {
            vit->second = mk_fresh_var(nm, cur[0]);
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
      nm.mk_node(node.kind(), {fresh_var, cache.at(body)}));
}

std::pair<bool, std::unordered_set<Node>>
PassQuant::has_free_vars(const Node& node) const
{
  std::unordered_set<Node> bound_vars;
  std::unordered_set<Node> quant_vars;
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
      else if (KindInfo::is_binder(cur.kind()))
      {
        bound_vars.insert(cur[0]);
        if (KindInfo::is_quant(cur.kind()))
        {
          quant_vars.insert(cur[0]);
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  for (const auto& v : vars)
  {
    if (bound_vars.find(v) == bound_vars.end())
    {
      return {true, {}};
    }
  }
  return {false, quant_vars};
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

namespace {
/**
 * Determine which variables in `vars` occur in `node`.
 * @param node The node to check.
 * @param vars The variables to check for.
 * @return The set of variables that occur in `node`.
 */
std::vector<Node>
collect_vars(const Node& node, const std::unordered_set<Node>& vars)
{
  std::vector<Node> res;
  std::unordered_set<Node> cache;
  node_ref_vector visit{node};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();
    if (!cache.insert(cur).second)
    {
      continue;
    }
    if (cur.kind() == Kind::VARIABLE)
    {
      if (vars.find(cur) != vars.end())
      {
        res.push_back(cur);
      }
      continue;
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
  return res;
}
}  // namespace

Node
PassQuant::eliminate(const Node& node)
{
  util::Timer timer_inv_elim(d_stats.time_inv_elim);

  assert(node.kind() == Kind::FORALL);

  NodeManager& nm    = d_env.nm();
  Rewriter& rewriter = d_env.rewriter();

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
  //
  // For deep quantifier chains, we get a quadratic overhead if eliminate()
  // processes each quantifier sequentially. Thus, we process such chains in
  // batch, and substitute all quantified variables that can be eliminated
  // at once. Note that processing in batch can result in cyclic substitutions,
  // hence we process in rounds and break such cycles by deferring all but one
  // (for each cycle) to later rounds.

  std::vector<Node> vars;
  std::unordered_set<Node> eliminated;
  Node body = node;

  while (body.kind() == Kind::FORALL)
  {
    vars.push_back(body[0]);
    body = body[1];
  }

  for (;;)
  {
    std::vector<std::pair<Node, Node>> inverses;  // innermost variable first
    std::unordered_set<Node> candidates;
    for (size_t i = 0, n = vars.size(); i < n; ++i)
    {
      const Node& var = vars[n - i - 1];
      if (eliminated.find(var) != eliminated.end())
      {
        continue;
      }
      Node inv = find_inverse(body, var);
      if (!inv.is_null())
      {
        assert(!utils::has_x(inv, var));
        inverses.emplace_back(var, inv);
        candidates.insert(var);
      }
    }
    if (inverses.empty())
    {
      break;
    }

    // An inverse may reference other candidate variables, e.g., an equality
    // (= (bvadd x y) t) yields an inverse for both x and y, which may result
    // in a cyclic substition map, but it must be acyclic (utils::substitute()
    // also substitutes in the substituted terms).
    //
    // We break such cycles by determining the dependencies between the
    // elimination candidates and deferring the source of every back edge
    // found by a depth-first search over the resulting graph to the next round.
    // This is guaranteed to hit every cycle.
    //
    // Deferred candidates are eliminated in one of the next rounds, where
    // their inverse is recomputed w.r.t. the substituted body.
    std::unordered_map<Node, std::vector<Node>> deps;
    for (const auto& [var, inv] : inverses)
    {
      assert(deps.find(var) == deps.end());
      deps[var] = collect_vars(inv, candidates);
    }

    std::unordered_set<Node> dropped;
    // Marks for processing status: 0: unvisited, 1: open, 2: done
    std::unordered_map<Node, uint8_t> marked;
    // Visit stack, maps nodes to be visited to the next deps index to process.
    // Note: We cannot process deps per node sequentially, we must process them
    //       in strict DFS order. The visit stack faciliates this.
    std::vector<std::pair<Node, size_t>> visit;
    for (const auto& p : inverses)
    {
      const Node& cur     = p.first;
      auto [it, inserted] = marked.emplace(cur, 0);
      if (!inserted)
      {
        assert(it->second == 2);
        continue;
      }
      it->second = 1;

      visit.emplace_back(cur, 0);
      do
      {
        auto& [ccur, idx]     = visit.back();
        const auto& ccur_deps = deps.at(ccur);
        if (idx == ccur_deps.size() || dropped.find(ccur) != dropped.end())
        {
          assert(marked.find(ccur) != marked.end());
          marked[ccur] = 2;
          visit.pop_back();
          continue;
        }
        const Node& dep = ccur_deps[idx++];
        if (dropped.find(dep) != dropped.end())
        {
          continue;
        }
        auto [itm, _] = marked.emplace(dep, 0);
        if (itm->second == 1)
        {
          // Back edge, break the cycle by not eliminating `ccur`. Note that
          // this keeps the candidate that comes first in the (innermost
          // variable first) elimination order.
          dropped.insert(ccur);
        }
        else if (itm->second == 0)
        {
          itm->second = 1;
          visit.emplace_back(dep, 0);
        }
      } while (!visit.empty());
    }

    std::unordered_map<Node, Node> substs;
    for (const auto& [var, inv] : inverses)
    {
      if (dropped.find(var) == dropped.end())
      {
        substs.emplace(var, inv);
      }
    }
    assert(!substs.empty());
    {
      util::Timer timer_inv_elim_subst(d_stats.time_inv_elim_subst);
      std::unordered_map<Node, Node> cache;
      body = rewriter.rewrite(utils::substitute(nm, body, substs, cache));
    }
    d_stats.num_inv_elim += substs.size();
    for (const auto& [var, inv] : substs)
    {
      eliminated.insert(var);
    }
  }

  if (eliminated.empty())
  {
    return node;
  }
  Node res = body;
  for (auto it = vars.rbegin(); it != vars.rend(); ++it)
  {
    if (eliminated.find(*it) != eliminated.end())
    {
      continue;
    }
    res = nm.mk_node(Kind::FORALL, {*it, res});
  }
  return rewriter.rewrite(res);
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
  std::unordered_map<Node, Node> repr_substs;
  std::unordered_set<Node> top_quants;

  // Map quantifiers to their parents count.
  // Note that a quantifier with more than one parent is 'shared' and must not
  // be treated as part of an enclosing binder chain. It is normalized as a
  // chain of its own, and the enclosing chain uses that normal form. This
  // guarantees that the variable of a binder belongs to exactly one chain.
  std::unordered_map<Node, size_t> nparents;
  {
    std::vector<Node> pvisit{node};
    std::unordered_set<Node> pcache;
    do
    {
      Node cur = pvisit.back();
      pvisit.pop_back();
      if (!pcache.insert(cur).second)
      {
        continue;
      }
      for (const Node& child : cur)
      {
        if (child.kind() == Kind::FORALL)
        {
          nparents[child] += 1;
        }
        pvisit.push_back(child);
      }
    } while (!pvisit.empty());
  }
  auto shared = [&nparents](const Node& n) {
    auto it = nparents.find(n);
    return it != nparents.end() && it->second > 1;
  };

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
        while (cur[1].kind() == Kind::FORALL && !shared(cur[1]))
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
        //
        // We normalize bottom-up, hence the only variables that still occur
        // free in the (already normalized) body are the ones bound by enclosing
        // chains, which are yet unmapped since we use one substitution map per
        // chain. Keeping the map per chain further ensures that a variable that
        // is the binder of two distinct chains cannot pick up the other chain's
        // canonical variable when a quantifier is shared between a nested and a
        // non-nested position.
        std::unordered_map<Node, Node> substs;
        Node body = cur;
        std::vector<Node> args;
        do
        {
          Node var = get_canonical_var(body[0]);
          args.push_back(var);
          substs.emplace(body[0], var);
          body = body[1];
        } while (body.kind() == Kind::FORALL && !shared(body));
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
