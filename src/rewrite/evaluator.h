/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node.h"

namespace bzla {

class Evaluator
{
 public:
  static Node evaluate(node::Kind kind,
                       const std::vector<Node>& values,
                       const std::vector<uint64_t>& indices = {});
};

}  // namespace bzla
