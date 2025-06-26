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

#include <unordered_map>

#include "env.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"

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
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.node_info().lambda)
    {
      const Node& processed = process(assertion);
      assertions.replace(i, processed);
    }
  }
}

Node
PassElimLambda::process(const Node& term)
{
  node::node_ref_vector visit{term};
  std::unordered_map<Node, bool> cache;

  do
  {
    const Node& cur = visit.back();

    if (d_preproc_cache.cached(cur, SimplifyCache::Cacher::ELIM_LAMBDA)
        || !cur.node_info().lambda)
    {
      cache.emplace(cur, true);
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (!it->second)
    {
      it->second = true;
      Node res;
      // Eliminate function applications on lambdas
      if (cur.kind() == Kind::APPLY && cur[0].kind() == Kind::LAMBDA)
      {
        ++d_stats.num_elim;
        res = reduce(cur);
      }
      else
      {
        res = d_preproc_cache.rebuild_node(d_env.nm(), cur);
      }
      d_preproc_cache.add(cur, res, SimplifyCache::Cacher::ELIM_LAMBDA);
    }
    visit.pop_back();
  } while (!visit.empty());

  return d_preproc_cache.get(term);
}

/* --- PassElimLambda private ----------------------------------------------- */

Node
PassElimLambda::reduce(const Node& node) const
{
  assert(node.kind() == Kind::APPLY);
  assert(node[0].kind() == Kind::LAMBDA);

  std::unordered_map<Node, Node> cache;
  auto it   = node.begin();
  Node body = *it++;
  for (; it != node.end(); ++it)
  {
    const Node& var = body[0];
    cache.emplace(var, d_preproc_cache.get(*it));
    body = body[1];
  }
  assert(body.kind() != Kind::LAMBDA);

  node::node_ref_vector visit{body};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      if (d_preproc_cache.cached(cur, SimplifyCache::Cacher::ELIM_LAMBDA))
      {
        visit.push_back(d_preproc_cache.get(cur));
      }
      else
      {
        // Lambdas below already reduced and cached.
        assert(cur.kind() != Kind::APPLY || cur[0].kind() != Kind::LAMBDA);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      if (d_preproc_cache.cached(cur, SimplifyCache::Cacher::ELIM_LAMBDA))
      {
        it->second = cache.at(d_preproc_cache.get(cur));
      }
      else
      {
        // Lambdas below already reduced and cached.
        assert(cur.kind() != Kind::APPLY || cur[0].kind() != Kind::LAMBDA);
        it->second = utils::rebuild_node(d_env.nm(), cur, cache);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(body);
}

PassElimLambda::Statistics::Statistics(util::Statistics& stats)
    : num_elim(stats.new_stat<uint64_t>("preprocess::elim_lambda::num_elim"))
{
}

}  // namespace bzla::preprocess::pass
