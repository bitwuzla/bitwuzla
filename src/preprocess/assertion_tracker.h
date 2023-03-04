#ifndef BZLA_PREPROCESS_ASSERTION_TRACKER_H_INCLUDED
#define BZLA_PREPROCESS_ASSERTION_TRACKER_H_INCLUDED

#include <vector>

#include "backtrack/unordered_map.h"
#include "node/node_manager.h"

namespace bzla::preprocess {

class AssertionTracker
{
 public:
  AssertionTracker() = delete;
  AssertionTracker(backtrack::BacktrackManager* mgr);

  void track(const Node& assertion,
             const Node& parent,
             const std::vector<Node>& parents = {});
  std::vector<Node> parents(const std::vector<Node>& assertions) const;

 private:
  backtrack::unordered_map<Node, std::vector<Node>> d_tracked_assertions;
};

}  // namespace bzla::preprocess

#endif
