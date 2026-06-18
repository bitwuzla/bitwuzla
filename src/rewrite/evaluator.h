/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_EVALUATOR_H_INCLUDED
#define BZLA_REWRITE_EVALUATOR_H_INCLUDED

#include <span>

#include "node/node.h"

namespace bzla {

class Evaluator
{
 public:
  static Node evaluate(NodeManager& nm,
                       node::Kind kind,
                       const std::vector<Node>& values,
                       std::span<const uint64_t> indices = {});
};

}  // namespace bzla

#endif
