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
#include "node/node_ref_vector.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* --- PassEmbeddedConstraints public --------------------------------------- */

PassEmbeddedConstraints::PassEmbeddedConstraints(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr),
      d_substitutions(backtrack_mgr),
      d_stats(env.statistics())
{
}

void
PassEmbeddedConstraints::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  // Disabled if unsat cores enabled.
  if (d_env.options().produce_unsat_cores())
  {
    return;
  }

  Log(1) << "Apply embedded constraints preprocessing pass";

  NodeManager& nm = NodeManager::get();
  uint64_t n_substs = 0;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value()) continue;
    if (assertion.is_inverted())
    {
      assert(!assertion[0].is_variable());
      n_substs += 1;
      d_substitutions.emplace(assertion[0], nm.mk_value(false));
    }
    else
    {
      assert(!assertion.is_variable());
      n_substs += 1;
      d_substitutions.emplace(assertion, nm.mk_value(true));
    }
  }
  Log(1) << "Found " << n_substs << " new substitutions";
  if (d_substitutions.empty())
  {
    return;
  }

  d_cache.clear();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
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
    }
  }
  d_cache.clear();
  Log(1) << d_stats.num_substs << " embedded constraint substitutions";
}

Node
PassEmbeddedConstraints::process(const Node& node)
{
  auto [res, num_substs] = substitute(node, d_substitutions, d_cache);
  res                    = d_env.rewriter().rewrite(res);
  d_stats.num_substs += num_substs;
  return res;
}

/* --- PassEmbeddedConstraints private -------------------------------------- */

PassEmbeddedConstraints::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::embedded::time_apply")),
      num_substs(stats.new_stat<uint64_t>("preprocess::embedded::num_substs"))
{
}

}  // namespace bzla::preprocess::pass
