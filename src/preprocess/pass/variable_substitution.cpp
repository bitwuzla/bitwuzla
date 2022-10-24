#include "preprocess/pass/variable_substitution.h"

#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"

namespace bzla::preprocess::pass {

using namespace node;

void
PassVariableSubstitution::apply(backtrack::AssertionView& assertions)
{
  if (d_substitutions.empty())
  {
    return;
  }

  NodeManager& nm = NodeManager::get();
  d_substitution_map.clear();
  std::unordered_set<Node> skip_subst;
  size_t num_levels = d_substitutions.cur_level();
  size_t is         = 0;
  size_t ia         = 0;
  for (size_t level = 0; level <= num_levels; ++level)
  {
    for (size_t size = d_substitutions.size(); is < size; ++is)
    {
      const auto& [var, term, slevel] = d_substitutions[is];
      if (slevel != level)
      {
        break;
      }
      d_substitution_map.emplace(var, term);
    }

    remove_indirect_cycles(d_substitution_map);

    // Process assertions for current level.
    d_substitution_cache.clear();
    for (size_t size = assertions.size(); ia < size; ++ia)
    {
      const auto& [assertion, alevel] = assertions[ia];
      // Only process assertions of current level.
      if (alevel != level)
      {
        break;
      }
      // Skip substitution assertions if still needed.
      if (skip_subst.find(assertion) != skip_subst.end())
      {
        continue;
      }
      const Node& preprocessed =
          substitute(assertion, d_substitution_map, d_substitution_cache);
      const Node& rewritten = d_rewriter.rewrite(preprocessed);
      assertions.replace(ia, rewritten);
    }

    // If variable still occurs in previous levels we need to keep the variable
    // substitution assertion.
    for (size_t i = is, size = d_substitutions.size(); i < size; ++i)
    {
      const auto& [var, term, slevel] = d_substitutions[i];
      assert(slevel > level);
      auto it = d_substitution_cache.find(var);
      if (it != d_substitution_cache.end() && it->second == var)
      {
        skip_subst.insert(nm.mk_node(Kind::EQUAL, {var, term}));
      }
    }
  }
  assert(is == d_substitutions.size());

  // TODO: add new variable substitutions
}

void
PassVariableSubstitution::register_assertion(const Node& assertion)
{
  if (assertion.kind() == Kind::EQUAL)
  {
    if (assertion[0].kind() == Kind::CONSTANT)
    {
      if (!is_direct_cycle(assertion[0], assertion[1]))
      {
        d_substitutions.emplace_back(
            assertion[0], assertion[1], d_substitutions.cur_level());
      }
    }
    else if (assertion[1].kind() == Kind::CONSTANT)
    {
      if (!is_direct_cycle(assertion[1], assertion[0]))
      {
        d_substitutions.emplace_back(
            assertion[1], assertion[0], d_substitutions.cur_level());
      }
    }
  }
}

Node
PassVariableSubstitution::process(const Node& term)
{
  return d_rewriter.rewrite(
      substitute(term, d_substitution_map, d_substitution_cache));
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
    const Node& assertion,
    const std::unordered_map<Node, Node>& substitutions,
    std::unordered_map<Node, Node>& cache) const
{
  node::node_ref_vector visit{assertion};
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
        auto iit   = cache.find(its->second);
        it->second = iit->second;
      }
      else if (cur.num_children() > 0)
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto iit = cache.find(child);
          assert(iit != cache.end());
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

  return cache.at(assertion);
}

}  // namespace bzla::preprocess::pass
