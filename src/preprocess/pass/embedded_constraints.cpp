/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/embedded_constraints.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;
using namespace bzla::node::utils;

/* --- PassEmbeddedConstraints public --------------------------------------- */

PassEmbeddedConstraints::PassEmbeddedConstraints(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "ec", "embedded_constraints"),
      d_substitutions(backtrack_mgr),
      d_batch_min_id(backtrack_mgr),
      d_cache(backtrack_mgr),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

void
PassEmbeddedConstraints::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);

  // Disabled if unsat cores enabled.
  if (d_env.options().produce_unsat_cores())
  {
    return;
  }
  // Disabled if interpolants generation is enabled.
  if (d_env.options().produce_interpolants())
  {
    return;
  }

  Log(1) << "Apply embedded constraints preprocessing pass";

  NodeManager& nm   = d_env.nm();
  uint64_t n_substs = 0;
  uint64_t min_id   = UINT64_MAX;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value()) continue;
    bool inverted     = assertion.is_inverted();
    const Node& subst = inverted ? assertion[0] : assertion;
    assert(!subst.is_variable());
    if (d_substitutions.emplace(subst, nm.mk_value(!inverted)).second)
    {
      n_substs += 1;
      min_id = std::min(min_id, subst.id());
    }
  }
  Log(1) << "Found " << n_substs << " new substitutions";
  if (d_substitutions.empty())
  {
    return;
  }
  if (n_substs > 0)
  {
    d_batch_min_id.push_back(min_id);
    d_num_batches_added += 1;
    d_min_subst_id = std::min(d_min_subst_id, min_id);
  }

  uint64_t num_substs = d_stats.num_substs;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    const Node& ass       = assertion.is_inverted() ? assertion[0] : assertion;
    if (ass.num_children() > 0)
    {
      std::vector<Node> children;
      for (const Node& child : ass)
      {
        children.push_back(substitute(child));
      }
      Node rewritten = ass.num_indices() > 0
                           ? nm.mk_node(ass.kind(), children, ass.indices())
                           : nm.mk_node(ass.kind(), children);
      if (assertion.is_inverted())
      {
        rewritten = invert_node(nm, rewritten);
      }
      assertions.replace(i, rewritten);
    }
  }
  Log(1) << d_stats.num_substs - num_substs
         << " embedded constraint substitutions";
}

Node
PassEmbeddedConstraints::process(const Node& node)
{
  return substitute(d_env.rewriter().rewrite(node));
}

/* --- PassEmbeddedConstraints private -------------------------------------- */

Node
PassEmbeddedConstraints::substitute(const Node& node)
{
  if (d_substitutions.empty())
  {
    return node;
  }

  // Recompute d_later_min_id if batches were popped (size) or replaced by new
  // batches (version) since it was computed.
  size_t num_batches = d_batch_min_id.size();
  if (d_later_min_id.size() != num_batches + 1
      || d_later_min_id_version != d_num_batches_added)
  {
    d_later_min_id.resize(num_batches + 1);
    d_later_min_id[num_batches] = UINT64_MAX;
    for (size_t i = num_batches; i > 0; --i)
    {
      d_later_min_id[i - 1] =
          std::min(d_later_min_id[i], d_batch_min_id[i - 1]);
    }
    d_later_min_id_version = d_num_batches_added;
  }

  // Get result of node processed with the current substitutions, if any.
  auto get_result = [&](const Node& n) -> const Node* {
    if (n.id() < d_min_subst_id)
    {
      return &n;
    }
    const Cache::Entry* entry = d_cache.find(n);
    // Entries of popped scope levels are removed together with the batches
    // they were computed for.
    assert(!entry || entry->num_batches <= num_batches);
    if (entry && entry->num_batches <= num_batches
        && n.id() < d_later_min_id[entry->num_batches])
    {
      return &entry->result;
    }
    return nullptr;
  };

  Rewriter& rw = d_env.rewriter();
  std::vector<std::pair<ConstNodeRef, bool>> visit{{node, false}};
  std::vector<Node> children;
  do
  {
    const Node& cur = visit.back().first;

    // Pre-order visit. Completed nodes have a valid cached result, hence nodes
    // reachable via several paths are only expanded once.
    if (!visit.back().second)
    {
      if (get_result(cur))
      {
        visit.pop_back();
        continue;
      }
      auto it = d_substitutions.find(cur);
      if (it != d_substitutions.end())
      {
        d_cache.insert(cur, it->second, num_batches);
        d_stats.num_substs += 1;
        visit.pop_back();
        continue;
      }
      visit.back().second = true;
      for (const Node& child : cur)
      {
        visit.emplace_back(child, false);
      }
      continue;
    }

    children.clear();
    for (const Node& child : cur)
    {
      const Node* res = get_result(child);
      assert(res);
      children.push_back(*res);
    }
    // Children are already rewritten, only rewrite the rebuilt node.
    d_cache.insert(cur, rw.rebuild_node(cur, children), num_batches);
    visit.pop_back();
  } while (!visit.empty());

  const Node* res = get_result(node);
  assert(res);
  return *res;
}

PassEmbeddedConstraints::Statistics::Statistics(util::Statistics& stats,
                                                const std::string& prefix)
    : num_substs(stats.new_stat<uint64_t>(prefix + "num_substs"))
{
}

}  // namespace bzla::preprocess::pass
