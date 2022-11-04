#include "preprocess/pass/flatten_and.h"

#include <unordered_set>
#include <vector>

#include "node/node_manager.h"

namespace bzla::preprocess::pass {

using namespace node;

void
PassFlattenAnd::apply(AssertionVector& assertions)
{
  std::vector<Node> visit;
  std::unordered_set<Node> cache;

  NodeManager& nm = NodeManager::get();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.kind() == Kind::AND)
    {
      visit.insert(visit.end(), assertion.rbegin(), assertion.rend());
      assertions.replace(i, nm.mk_value(true));
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
          assertions.push_back(cur);
        }
      }
    }
  }
}

}  // namespace bzla::preprocess::pass
