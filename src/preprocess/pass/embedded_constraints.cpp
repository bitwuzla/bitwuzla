#include "preprocess/pass/embedded_constraints.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* --- PassEmbeddedConstraints public --------------------------------------- */

PassEmbeddedConstraints::PassEmbeddedConstraints(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env),
      d_stats(env.statistics()),
      d_backtrack_mgr(backtrack_mgr),
      d_substitutions(backtrack_mgr)
{
}

void
PassEmbeddedConstraints::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  NodeManager& nm = NodeManager::get();

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value()) continue;
    if (assertion.is_inverted())
    {
      d_substitutions.emplace(assertion[0], nm.mk_value(false));
    }
    else
    {
      d_substitutions.emplace(assertion, nm.mk_value(true));
    }
  }
  if (d_substitutions.empty())
  {
    return;
  }

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
}

Node
PassEmbeddedConstraints::process(const Node& node)
{
  return d_env.rewriter().rewrite(substitute(node));
}

/* --- PassEmbeddedConstraints private -------------------------------------- */

Node
PassEmbeddedConstraints::substitute(const Node& node)
{
  NodeManager& nm = NodeManager::get();
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
      auto its = d_substitutions.find(cur);
      if (its != d_substitutions.end())
      {
        it->second = its->second;
        d_stats.num_substs += 1;
      }
      else if (cur.num_children() > 0)
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto itc = d_cache.find(child);
          assert(itc != d_cache.end());
          assert(!itc->second.is_null());
          children.push_back(itc->second);
        }
        if (cur.num_indices() > 0)
        {
          it->second = nm.mk_node(cur.kind(), children, cur.indices());
        }
        else
        {
          it->second = nm.mk_node(cur.kind(), children);
        }
      }
      else
      {
        it->second = cur;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  auto it = d_cache.find(node);
  assert(it != d_cache.end());
  return it->second;
}

PassEmbeddedConstraints::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::embedded::time_apply")),
      num_substs(stats.new_stat<uint64_t>("preprocess::embedded::num_substs"))
{
}

}  // namespace bzla::preprocess::pass
