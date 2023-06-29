/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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

void
AssertionTracker::find_original(
    const std::vector<Node>& assertions,
    const std::unordered_set<Node>& original_assertions,
    std::vector<Node>& res) const
{
  // Trace back to original assertion
  std::unordered_set<Node> cache;
  std::vector<Node> visit = assertions;
  for (size_t i = 0; i < visit.size(); ++i)
  {
    Node n = visit[i];
    if (!cache.insert(n).second)
    {
      continue;
    }

    // Found original assertion
    if (original_assertions.find(n) != original_assertions.end())
    {
      res.push_back(n);
      continue;
    }

    // Trace parents
    auto it = d_tracked_assertions.find(n);
    if (it != d_tracked_assertions.end())
    {
      visit.insert(visit.end(), it->second.begin(), it->second.end());
    }
  }
  assert(!res.empty());
}

}  // namespace bzla::preprocess
