#include "preprocess/assertion_tracker.h"

namespace bzla::preprocess {

/* --- AssertionTracker public ---------------------------------------------- */

AssertionTracker::AssertionTracker(backtrack::BacktrackManager* mgr)
    : d_tracked_assertions(mgr)
{
}

void
AssertionTracker::track(const Node& assertion,
                        const Node& parent,
                        const std::vector<Node>& parents)
{
  assert(!parent.is_null());
  assert(std::find(parents.begin(), parents.end(), assertion)
         == std::end(parents));

  // Only track first occurence of assertion
  auto [it, inserted] = d_tracked_assertions.emplace(assertion, parents);
  if (inserted)
  {
    it->second.insert(it->second.begin(), parent);
  }
}

std::vector<Node>
AssertionTracker::parents(const std::vector<Node>& assertions) const
{
  // Trace back to original assertion
  std::unordered_set<Node> cache;
  std::vector<Node> res;
  std::vector<Node> visit = assertions;
  for (size_t i = 0; i < visit.size(); ++i)
  {
    Node n  = visit[i];
    auto it = d_tracked_assertions.find(n);

    if (!cache.insert(n).second)
    {
      continue;
    }

    // Found original assertion
    if (it == d_tracked_assertions.end())
    {
      res.push_back(n);
      continue;
    }

    visit.insert(visit.end(), it->second.begin(), it->second.end());
  }

  assert(!res.empty());
  return res;
}

}  // namespace bzla::preprocess
