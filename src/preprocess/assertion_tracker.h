/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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

  void track(const Node& assertion, const Node& parent);
  void find_original(const std::vector<Node>& assertions,
                     const std::unordered_set<Node>& original_assertions,
                     std::vector<Node>& res) const;

 private:
  backtrack::unordered_map<Node, Node> d_tracked_assertions;
};

}  // namespace bzla::preprocess

#endif
