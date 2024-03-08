/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/flatten_and.h"

#include <unordered_set>
#include <vector>

#include "env.h"
#include "node/node_manager.h"

namespace bzla::preprocess::pass {

using namespace node;

PassFlattenAnd::PassFlattenAnd(Env& env,
                               backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "fa", "flatten_and"),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

void
PassFlattenAnd::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  std::vector<Node> visit;
  std::unordered_set<Node> cache;

  NodeManager& nm = d_env.nm();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    Node assertion = assertions[i];
    if (assertion.kind() == Kind::AND)
    {
      visit.insert(visit.end(), assertion.rbegin(), assertion.rend());
      assertions.replace(i, nm.mk_value(true));
      ++d_stats.num_flattened;
    }
    while (!visit.empty())
    {
      Node cur = visit.back();
      visit.pop_back();
      auto [it, inserted] = cache.insert(cur);
      if (inserted)
      {
        if (cur.kind() == Kind::AND)
        {
          visit.insert(visit.end(), cur.rbegin(), cur.rend());
          ++d_stats.num_flattened;
        }
        else
        {
          assertions.push_back(cur, assertion);
          ++d_stats.num_assertions;
        }
      }
    }
  }
}

PassFlattenAnd::Statistics::Statistics(util::Statistics& stats,
                                       const std::string& prefix)
    : num_flattened(stats.new_stat<uint64_t>(prefix + "num_flattened")),
      num_assertions(stats.new_stat<uint64_t>(prefix + "num_assertions"))
{
}

}  // namespace bzla::preprocess::pass
