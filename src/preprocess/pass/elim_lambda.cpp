/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/elim_lambda.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"

namespace bzla::preprocess::pass {

using namespace node;

/* --- PassElimLambda public ------------------------------------------------ */

PassElimLambda::PassElimLambda(Env& env,
                               backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "el", "elim_lambda"),
      d_stats(env.statistics())
{
}

void
PassElimLambda::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  d_cache.clear();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (!processed(assertion))
    {
      if (assertion.node_info().lambda)
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
PassElimLambda::process(const Node& term)
{
  node::node_ref_vector visit{term};

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

      // Eliminate function applications on lambdas
      if (cur.kind() == Kind::APPLY && cur[0].kind() == Kind::LAMBDA)
      {
        ++d_stats.num_elim;
        it->second = reduce(cur);
      }
      else
      {
        it->second = utils::rebuild_node(d_env.nm(), cur, children);
      }
    }

    visit.pop_back();
  } while (!visit.empty());

  return d_cache.at(term);
}

/* --- PassElimLambda private ----------------------------------------------- */

Node
PassElimLambda::reduce(const Node& node) const
{
  assert(node.kind() == Kind::APPLY);
  assert(node[0].kind() == Kind::LAMBDA);

  std::unordered_map<Node, Node> substitutions;
  auto it   = node.begin();
  Node body = *it++;
  for (; it != node.end(); ++it)
  {
    const Node& var = body[0];
    substitutions.emplace(var, d_cache.at(*it));
    body = body[1];
  }
  assert(body.kind() != Kind::LAMBDA);

  std::unordered_map<Node, Node> cache;
  node::node_ref_vector visit{body};
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      if (cur.kind() == Kind::APPLY && cur[0].kind() == Kind::LAMBDA)
      {
        assert(d_cache.find(cur) != d_cache.end());
        visit.push_back(d_cache.at(cur));
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.kind() == Kind::APPLY && cur[0].kind() == Kind::LAMBDA)
      {
        assert(d_cache.find(cur) != d_cache.end());
        it->second = cache.at(d_cache.at(cur));
      }
      else if (substitutions.find(cur) != substitutions.end())
      {
        assert(cur.kind() == Kind::VARIABLE);
        it->second = substitutions.at(cur);
      }
      else
      {
        it->second = utils::rebuild_node(d_env.nm(), cur, cache);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(body);
}

PassElimLambda::Statistics::Statistics(util::Statistics& stats)
    : num_elim(stats.new_stat<uint64_t>("preprocess::lambda::num_elim"))
{
}

}  // namespace bzla::preprocess::pass
