/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/contradicting_ands.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* --- PassContradictingAnds public ----------------------------------------- */

PassContradictingAnds::PassContradictingAnds(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr),
      d_substitutions(backtrack_mgr),
      d_stats(env.statistics())
{
}

std::pair<unordered_node_ref_set, bool>
PassContradictingAnds::is_contradicting_and(const Node& node,
                                            unordered_node_ref_set& visited)
{
  assert(node.kind() == Kind::BV_AND);
  assert(visited.find(node) != visited.end());
  node_ref_vector visit(node.begin(), node.end());
  unordered_node_ref_set leafs;
  unordered_node_ref_map<bool> children;
  do
  {
    const Node& cur = visit.back();
    visited.emplace(cur);
    visit.pop_back();
    bool inverted = cur.is_inverted();

    auto [it, inserted] = children.emplace(inverted ? cur[0] : cur, !inverted);
    if (inserted)
    {
      if (cur.kind() == Kind::BV_AND)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        leafs.insert(cur);
      }
    }
    else
    {
      if (it->second == inverted)
      {
        return std::make_pair(unordered_node_ref_set(), true);
      }
    }
  } while (!visit.empty());
  return std::make_pair(leafs, false);
}

void
PassContradictingAnds::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  node_ref_vector visit;
  unordered_node_ref_set visited;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (!processed(assertion))
    {
      visit.push_back(assertions[i]);
    }
  }

  if (visit.empty())
  {
    return;
  }

  NodeManager& nm = NodeManager::get();
  do
  {
    const Node& cur       = visit.back();
    auto [vit, vinserted] = visited.emplace(cur);
    visit.pop_back();
    if (vinserted)
    {
      if (cur.kind() == Kind::BV_AND)
      {
        auto [leafs, is_contradicting] = is_contradicting_and(cur, visited);
        if (is_contradicting)
        {
          d_substitutions.emplace(
              cur, nm.mk_value(BitVector::mk_zero(cur.type().bv_size())));
        }
        else
        {
          visit.insert(visit.end(), leafs.begin(), leafs.end());
        }
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());

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
PassContradictingAnds::process(const Node& node)
{
  auto [res, num_substs] = substitute(node, d_substitutions, d_cache);
  res                    = d_env.rewriter().rewrite(res);
  d_stats.num_substs += num_substs;
  return res;
}

/* --- PassContradictingAnds pricate----------------------------------------- */

PassContradictingAnds::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::contradicting::time_apply")),
      num_substs(
          stats.new_stat<uint64_t>("preprocess::contradicting::num_substs"))
{
}

}  // namespace bzla::preprocess::pass
