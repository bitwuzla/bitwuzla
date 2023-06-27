/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_UNORDERED_NODE_REF_SET_H_INCLUDED
#define BZLA_NODE_UNORDERED_NODE_REF_SET_H_INCLUDED

#include <unordered_set>

#include "node/node.h"

namespace bzla::node {

using unordered_node_ref_set =
    std::unordered_set<ConstNodeRef, std::hash<Node>>;

}

#endif
