#include "preprocess/pass/flatten_and.h"

#include <unordered_set>
#include <vector>

#include "node/node_manager.h"

namespace bzla::preprocess::pass {

using namespace node;

void
PassFlattenAnd::apply(backtrack::AssertionView& assertions)
{
  std::vector<Node> visit;
  std::unordered_set<Node> cache;
  std::vector<std::pair<Node, size_t>> new_assertions;

  NodeManager& nm = NodeManager::get();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const auto [assertion, level] = assertions[i];
    if (assertion.kind() == Kind::AND)
    {
      visit.insert(visit.end(), assertion.rbegin(), assertion.rend());
      assertions.replace(assertion, nm.mk_value(true));
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
        }
        else
        {
          new_assertions.emplace_back(cur, level);
        }
      }
    }
  }
  for (const auto& [assertion, level] : new_assertions)
  {
    assertions.insert_at_level(level, assertion);
  }
}

}  // namespace bzla::preprocess::pass
