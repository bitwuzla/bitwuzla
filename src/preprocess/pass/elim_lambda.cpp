#include "preprocess/pass/elim_lambda.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"

namespace bzla::preprocess::pass {

using namespace node;

/* --- PassElimLambda public ------------------------------------------------ */

void
PassElimLambda::apply(AssertionVector& assertions)
{
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    assertions.replace(i, process(assertions[i]));
  }
}

Node
PassElimLambda::process(const Node& term)
{
  NodeManager& nm = NodeManager::get();
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
        it->second = reduce(cur);
      }
      else if (children.size() > 0)
      {
        it->second = nm.mk_node(cur.kind(), children, cur.indices());
      }
      else
      {
        it->second = cur;
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

  NodeManager& nm = NodeManager::get();
  node::unordered_node_ref_map<Node> cache;
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
      else
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto iit = cache.find(child);
          assert(iit != cache.end());
          children.push_back(iit->second);
        }

        if (children.size() > 0)
        {
          it->second = nm.mk_node(cur.kind(), children, cur.indices());
        }
        else if (substitutions.find(cur) != substitutions.end())
        {
          assert(cur.kind() == Kind::VARIABLE);
          it->second = substitutions.at(cur);
        }
        else
        {
          it->second = cur;
        }
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(body);
}

}  // namespace bzla::preprocess::pass
