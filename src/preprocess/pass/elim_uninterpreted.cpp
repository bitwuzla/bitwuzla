/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/elim_uninterpreted.h"

#include <cmath>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* -------------------------------------------------------------------------- */

namespace {
uint64_t
bv_size_from_value(uint64_t value)
{
  assert(value);
  return value > 1 ? std::ceil(std::log2l(value)) : 1;
}
}  // namespace

/* --- PassElimUninterpreted public ----------------------------------------- */

PassElimUninterpreted::PassElimUninterpreted(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr),
      d_substitutions(backtrack_mgr),
      d_stats(env.statistics())
{
}

void
PassElimUninterpreted::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  node_ref_vector visit;
  unordered_node_ref_set visited;
  std::unordered_map<std::reference_wrapper<const Type>,
                     uint64_t,
                     std::hash<Type>>
      cnt;
  unordered_node_ref_set uns;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    visit.push_back(assertions[i]);
  }

  if (visit.empty())
  {
    return;
  }

  do
  {
    const Node& cur     = visit.back();
    auto [vit, vinserted] = visited.emplace(cur);
    visit.pop_back();
    if (vinserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      if (cur.type().is_uninterpreted())
      {
        auto [cit, cinserted] = cnt.emplace(cur.type(), 1);
        if (!cinserted)
        {
          cit->second += 1;
        }
        uns.emplace(cur);
      }
      // don't increase count but cache nodes that need a type substitution
      else if (cur.is_const())
      {
        if (cur.type().is_fun())
        {
          for (auto& t : cur.type().fun_types())
          {
            if (t.is_uninterpreted())
            {
              uns.emplace(cur);
              break;
            }
          }
        }
        else if (cur.type().is_array())
        {
          assert(!cur.type().array_element().is_uninterpreted());
          if (cur.type().array_index().is_uninterpreted())
          {
            uns.emplace(cur);
          }
        }
      }
    }
  } while (!visit.empty());

  NodeManager& nm = NodeManager::get();
  for (auto& un : uns)
  {
    const Node& u = un.get();
    assert(u.is_const());
    if (u.type().is_uninterpreted())
    {
      auto it = cnt.find(u.type());
      assert(it != cnt.end());
      d_substitutions.emplace(
          u, nm.mk_const(nm.mk_bv_type(bv_size_from_value(it->second))));
    }
    else if (u.type().is_fun())
    {
      std::vector<Type> types = u.type().fun_types();
      for (size_t i = 0, n = types.size(); i < n; ++i)
      {
        if (types[i].is_uninterpreted())
        {
          auto it = cnt.find(types[i]);
          assert(it != cnt.end());
          types[i] = nm.mk_bv_type(bv_size_from_value(it->second));
        }
      }
      d_substitutions.emplace(u, nm.mk_const(nm.mk_fun_type(types)));
    }
    else
    {
      assert(u.type().is_array());
      Type index   = u.type().array_index();
      Type element = u.type().array_element();
      assert(index.is_uninterpreted() || element.is_uninterpreted());
      if (index.is_uninterpreted())
      {
        auto it = cnt.find(index);
        assert(it != cnt.end());
        index = nm.mk_bv_type(bv_size_from_value(it->second));
      }
      if (element.is_uninterpreted())
      {
        auto it = cnt.find(element);
        assert(it != cnt.end());
        element = nm.mk_bv_type(bv_size_from_value(it->second));
      }
      d_substitutions.emplace(u, nm.mk_const(nm.mk_array_type(index, element)));
    }
  }

  if (d_substitutions.empty())
  {
    return;
  }

  d_cache.clear();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (processed(assertion))
    {
      continue;
    }
    const Node& ass       = assertion.is_inverted() ? assertion[0] : assertion;
    if (ass.num_children() > 0)
    {
      std::vector<Node> children;
      for (const Node& child : ass)
      {
        children.push_back(process(child));
      }
      Node rewritten = ass.num_indices() > 0
                           ? nm.mk_node(ass.kind(), children, ass.indices())
                           : nm.mk_node(ass.kind(), children);
      if (assertion.is_inverted())
      {
        rewritten = nm.invert_node(rewritten);
      }
      assertions.replace(i, rewritten);
      cache_assertion(rewritten);
    }
  }
  d_cache.clear();
}

Node
PassElimUninterpreted::process(const Node& node)
{
  auto [res, num_substs] = substitute(node, d_substitutions, d_cache);
  res                    = d_env.rewriter().rewrite(res);
  d_stats.num_substs += num_substs;
  return res;
}

/* --- PassEmbeddedConstraints private -------------------------------------- */

PassElimUninterpreted::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::uninterpreted::time_apply")),
      num_substs(
          stats.new_stat<uint64_t>("preprocess::uninterpreted::num_substs"))
{
}

}  // namespace bzla::preprocess::pass
