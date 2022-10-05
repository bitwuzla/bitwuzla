#include "preprocess/pass/elim_lambda.h"

#include "node/node_manager.h"

namespace bzla::preprocess::pass {

using namespace node;

using ConstNodeRef = std::reference_wrapper<const Node>;

namespace {

Node
reduce(const Node& node,
       const std::unordered_map<ConstNodeRef, Node, std::hash<Node>>& map)
{
  assert(node.kind() == Kind::APPLY);
  assert(node[0].kind() == Kind::LAMBDA);

  std::unordered_map<Node, Node> substitutions;
  auto it   = node.begin();
  Node body = *it++;
  for (; it != node.end(); ++it)
  {
    const Node& var = body[0];
    substitutions.emplace(var, map.at(*it));
    body = body[1];
  }
  assert(body.kind() != Kind::LAMBDA);

  NodeManager& nm = NodeManager::get();
  std::unordered_map<ConstNodeRef, Node, std::hash<Node>> cache;
  std::vector<ConstNodeRef> visit{body};
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      if (cur.kind() == Kind::APPLY && cur[0].kind() == Kind::LAMBDA)
      {
        visit.push_back(map.at(cur));
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
        it->second = cache.at(map.at(cur));
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
        else if (cur.kind() == Kind::VARIABLE)
        {
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

}  // namespace

void
PassElimLambda::apply()
{
  std::vector<ConstNodeRef> visit;
  std::unordered_map<ConstNodeRef, Node, std::hash<Node>> cache;
  NodeManager& nm = NodeManager::get();

  while (!d_assertions.empty())
  {
    auto [assertion, index] = d_assertions.next_index();

    visit.push_back(assertion);
    do
    {
      const Node& cur     = visit.back();
      auto [it, inserted] = cache.emplace(cur, Node());

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
          auto iit = cache.find(child);
          assert(iit != cache.end());
          children.push_back(iit->second);
        }

        // Eliminate function applications on lambdas
        if (cur.kind() == Kind::APPLY && cur[0].kind() == Kind::LAMBDA)
        {
          it->second = reduce(cur, cache);
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

    d_assertions.replace(index, d_rewriter.rewrite(cache.at(assertion)));
  }
}

}  // namespace bzla::preprocess::pass
