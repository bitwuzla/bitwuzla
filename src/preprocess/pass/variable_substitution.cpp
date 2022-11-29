#include "preprocess/pass/variable_substitution.h"

#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"

namespace bzla::preprocess::pass {

using namespace node;

namespace {

std::pair<Node, Node>
get_var_term(const Node& assertion)
{
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
  return std::make_pair(Node(), Node());
}

}  // namespace

void
PassVariableSubstitution::apply(AssertionVector& assertions)
{
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (register_assertion(assertion))
    {
      d_substitution_assertions.insert(assertion);
    }
  }

  if (d_substitutions.empty())
  {
    return;
  }

  auto& substitution_map = d_cache.substitutions();

  // Substitutions and cache will be repopulated below
  substitution_map.clear();
  d_cache.cache().clear();

  // Compute substitution map and remove cycles
  substitution_map.insert(d_substitutions.begin(), d_substitutions.end());
  remove_indirect_cycles(substitution_map);

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
      Node rewritten = nm.mk_node(Kind::EQUAL, {var, process(term)});
      assertions.replace(i, rewritten);
      // Add new substitution assertion to cache in order to avoid that this
      // new assertion will be eliminated.
      d_substitution_assertions.insert(rewritten);
    }
    else
    {
      assertions.replace(i, process(assertion));
    }
  }
}

bool
PassVariableSubstitution::register_assertion(const Node& assertion)
{
  const auto [var, term] = get_var_term(assertion);
  if (!var.is_null())
  {
    if (d_substitutions.find(var) != d_substitutions.end())
    {
      return false;
    }
    if (!is_direct_cycle(var, term))
    {
      d_substitutions.emplace(var, term);
      return true;
    }
  }
  return false;
}

Node
PassVariableSubstitution::process(const Node& term)
{
  return d_rewriter.rewrite(
      substitute(term, d_cache.substitutions(), d_cache.cache()));
}

/* --- PassVariableSubstitution private ------------------------------------- */

void
PassVariableSubstitution::remove_indirect_cycles(
    std::unordered_map<Node, Node>& substitutions) const
{
  int64_t order_num = 1;
  std::unordered_map<Node, int64_t> order;
  node::unordered_node_ref_set cache;
  node::node_ref_vector visit;

  for (const auto& [var, term] : substitutions)
  {
    visit.push_back(var);
    do
    {
      const Node& cur = visit.back();

      auto [it, inserted] = order.emplace(cur, -1);
      if (inserted)
      {
        if (cur.kind() == Kind::CONSTANT)
        {
          auto its = substitutions.find(cur);
          if (its != substitutions.end())
          {
            visit.push_back(its->second);
          }
        }
        else
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
        continue;
      }
      else if (it->second == -1)
      {
        if (cur.kind() == Kind::CONSTANT
            && substitutions.find(cur) != substitutions.end())
        {
          it->second = order_num++;
        }
        else
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
          it->second = max;
        }
      }
      visit.pop_back();
    } while (!visit.empty());
  }

  auto it = substitutions.begin();
  while (it != substitutions.end())
  {
    auto itv = order.find(it->first);
    auto itt = order.find(it->second);
    assert(itv != order.end());
    assert(itt != order.end());

    // Found cycle, remove this substitution.
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
  node::unordered_node_ref_set cache;
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.front();
    visit.erase(visit.begin());

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
