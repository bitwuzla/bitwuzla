#include "preprocess/pass/variable_substitution.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

using namespace node;

namespace {

std::pair<Node, Node>
get_var_term(const Node& assertion)
{
  NodeManager& nm = NodeManager::get();
  if (assertion.kind() == Kind::EQUAL)
  {
    if (assertion[0].kind() == Kind::CONSTANT)
    {
      return std::make_pair(assertion[0], assertion[1]);
    }
    else if (assertion[1].kind() == Kind::CONSTANT)
    {
      return std::make_pair(assertion[1], assertion[0]);
    }
  }
  else if (assertion.is_const())
  {
    return std::make_pair(assertion, nm.mk_value(true));
  }
  else if (assertion.is_inverted() && assertion[0].is_const())
  {
    return std::make_pair(assertion[0], nm.mk_value(false));
  }
  // TODO: more substitution normalizations
  return std::make_pair(Node(), Node());
}

}  // namespace

/* --- PassVariableSubstitution public -------------------------------------- */

PassVariableSubstitution::PassVariableSubstitution(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env),
      d_backtrack_mgr(backtrack_mgr),
      d_substitutions(backtrack_mgr),
      d_substitution_assertions(backtrack_mgr),
      d_cache(backtrack_mgr),
      d_stats(env.statistics())
{
}

void
PassVariableSubstitution::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);
  Log(1) << "Apply variable substitution";

  auto& substitution_map = d_cache.substitutions();
  bool process_term      = !substitution_map.empty();

  // Check current set of assertions for variable substitutions
  std::unordered_map<Node, Node> new_substs;
  {
    util::Timer timer(d_stats.time_register);
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      const Node& assertion  = assertions[i];
      const auto [var, term] = get_var_term(assertion);
      // Either no variable substitution or already have a substitution
      if (var.is_null() || d_substitutions.find(var) != d_substitutions.end())
      {
        continue;
      }

      // If we already have substitutions, process the term first to ensure
      // that all variables in this term are substituted before we check for
      // cycles. This allows us to incrementally add new substitutions and
      // check for cycles.
      Node term_processed = process_term ? process(term) : term;

      // Do not add direct substitution cycles
      if (!is_direct_cycle(var, term_processed))
      {
        d_substitutions.emplace(var, term_processed);
        d_substitution_assertions.insert(assertion);
        new_substs.emplace(var, term_processed);
      }
    }
    Log(1) << "Found " << new_substs.size() << " new substitutions";
  }

  // Remove substitution cycles
  {
    util::Timer timer_cycles(d_stats.time_remove_cycles);
    remove_indirect_cycles(new_substs);
    Log(1) << new_substs.size() << " substitutions after cycle removal";
  }

  // Add new substitutions to substitution map
  substitution_map.insert(new_substs.begin(), new_substs.end());
  d_stats.num_substs = substitution_map.size();

  // No substitutions
  if (substitution_map.empty())
  {
    return;
  }

  // Reset substitution cache since we have new substitutions
  d_cache.cache().clear();

  // Apply substitutions.
  //
  // Note: For non-top-level substitution assertions, we only process the term
  // side of the assertion and do not eliminate the assertion itself since we
  // have to keep the variable equality for cases where the variable still
  // occurs in lower levels (if variable substitution assertion was added in a
  // scope > 0). We could check whether the variable occurs in lower levels,
  // but for now we keep the assertion since this makes it simpler overall.
  bool top_level  = d_backtrack_mgr->num_levels() == 0;
  NodeManager& nm = NodeManager::get();
  Rewriter& rewriter = d_env.rewriter();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    // Keep non-top-level variable substitution assertion, but apply
    // substitutions in term.
    if (!top_level
        && d_substitution_assertions.find(assertion)
               != d_substitution_assertions.end())
    {
      auto [var, term] = get_var_term(assertion);
      assert(!var.is_null());
      // Make sure to rewrite the assertion, otherwise we may run into loops
      // with rewriter pass due to the substitution normalizations in
      // get_var_term(), e.g., a -- subst --> a = true -- rewrite --> a.
      Node rewritten =
          rewriter.rewrite(nm.mk_node(Kind::EQUAL, {var, process(term)}));
      assertions.replace(i, rewritten);
      // Add new substitution assertion to cache in order to avoid that this
      // new assertion will be eliminated by variable substitution.
      d_substitution_assertions.insert(rewritten);
    }
    else
    {
      assertions.replace(i, process(assertion));
    }
  }
}

Node
PassVariableSubstitution::process(const Node& term)
{
  return d_env.rewriter().rewrite(
      substitute(term, d_cache.substitutions(), d_cache.cache()));
}

/* --- PassVariableSubstitution private ------------------------------------- */

void
PassVariableSubstitution::remove_indirect_cycles(
    std::unordered_map<Node, Node>& substitutions) const
{
  int64_t order_num = 1;
  std::unordered_map<Node, int64_t> order;
  node::unordered_node_ref_map<bool> cache;
  node::node_ref_vector visit, nodes;
  std::vector<size_t> marker{0};

  // Compute topological order of substitutions. Assumes that direct cycles
  // were already removed.
  for (const auto& [var, term] : substitutions)
  {
    visit.push_back(var);
    do
    {
      const Node& cur = visit.back();

      auto [it, inserted] = cache.emplace(cur, false);
      if (inserted)
      {
        if (cur.kind() == Kind::CONSTANT)
        {
          auto its = substitutions.find(cur);
          if (its != substitutions.end())
          {
            // Mark first occurrence of substituted constant on the stack
            marker.push_back(visit.size());
            visit.push_back(its->second);
          }
        }
        else
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
        continue;
      }
      // Check if constant is first occurrence on the stack (i.e., marked)
      else if (marker.back() == visit.size())
      {
        assert(cur.kind() == Kind::CONSTANT);
        assert(substitutions.find(cur) != substitutions.end());
        marker.pop_back();
        // Assign substitution rank
        assert(order.find(cur) == order.end());
        order.emplace(cur, order_num++);
      }
      else if (!it->second)
      {
        // Save node for computing rank in next phase
        it->second = true;
        nodes.push_back(cur);
      }
      visit.pop_back();
    } while (!visit.empty());
  }

  // Compute ranking for all remaining nodes. Nodes on the vector are in
  // post-order DFS.
  for (const Node& cur : nodes)
  {
    int64_t max = 0;
    for (const Node& child : cur)
    {
      auto iit = order.find(child);
      assert(iit != order.end());
      if (iit->second > max)
      {
        max = iit->second;
      }
    }
    order.emplace(cur, max);
  }

  // Remove substitutions to break cycles.
  auto it = substitutions.begin();
  while (it != substitutions.end())
  {
    auto itv = order.find(it->first);
    auto itt = order.find(it->second);
    assert(itv != order.end());
    assert(itt != order.end());

    // Found cycle if the rank of the term > rank of substituted constant.
    // Remove cyclic substitution.
    if (itt->second > itv->second)
    {
      it = substitutions.erase(it);
    }
    else
    {
      ++it;
    }
  }
}

bool
PassVariableSubstitution::is_direct_cycle(const Node& var,
                                          const Node& term) const
{
  util::Timer timer(d_stats.time_direct_cycle_check);
  node::unordered_node_ref_set cache;
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.front();
    visit.erase(visit.begin());

    // var cannot be in cur
    if (cur.id() < var.id())
    {
      continue;
    }

    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      if (cur == var)
      {
        return true;
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

Node
PassVariableSubstitution::substitute(
    const Node& term,
    const std::unordered_map<Node, Node>& substitutions,
    std::unordered_map<Node, Node>& cache) const
{
  node::node_ref_vector visit{term};
  NodeManager& nm = NodeManager::get();

  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      auto its = substitutions.find(cur);
      if (its != substitutions.end())
      {
        visit.push_back(its->second);
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      auto its = substitutions.find(cur);
      if (its != substitutions.end())
      {
        auto iit = cache.find(its->second);
        assert(iit != cache.end());
        it->second = iit->second;
      }
      else if (cur.num_children() > 0)
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto iit = cache.find(child);
          assert(iit != cache.end());
          assert(!iit->second.is_null());
          children.push_back(iit->second);
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

  return cache.at(term);
}

PassVariableSubstitution::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::varsubst::time_apply")),
      time_register(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_register")),
      time_direct_cycle_check(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_direct_cycle_check")),
      time_remove_cycles(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_remove_cycles")),
      num_substs(stats.new_stat<uint64_t>("preprocess::varsubst::num_substs"))
{
}

/* --- PassVariableSubstitution::Cache -------------------------------------- */

PassVariableSubstitution::Cache::Cache(backtrack::BacktrackManager* mgr)
    : Backtrackable(mgr), d_map(mgr), d_cache(mgr)
{
  d_map.emplace_back();
  d_cache.emplace_back();
}

void
PassVariableSubstitution::Cache::push()
{
  // Make copy of previous level to allow calling process() after a pop()
  // without calling preprocess().
  d_map.emplace_back(d_map.back());
  d_cache.emplace_back(d_cache.back());
}

std::unordered_map<Node, Node>&
PassVariableSubstitution::Cache::substitutions()
{
  return d_map.back();
}

std::unordered_map<Node, Node>&
PassVariableSubstitution::Cache::cache()
{
  return d_cache.back();
}

}  // namespace bzla::preprocess::pass
