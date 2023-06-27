/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_UNORDERED_NODE_REF_MAP_H_INCLUDED
#define BZLA_NODE_UNORDERED_NODE_REF_MAP_H_INCLUDED

#include <unordered_map>

#include "node/node.h"

namespace bzla::node {

template <class T>
using unordered_node_ref_map =
    std::unordered_map<ConstNodeRef, T, std::hash<Node>>;

}

#endif
