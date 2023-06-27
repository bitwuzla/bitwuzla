/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_NODE_REF_VECTOR_H_INCLUDED
#define BZLA_NODE_NODE_REF_VECTOR_H_INCLUDED

#include <vector>

#include "node/node.h"

namespace bzla::node {

using node_ref_vector = std::vector<ConstNodeRef>;

}

#endif
