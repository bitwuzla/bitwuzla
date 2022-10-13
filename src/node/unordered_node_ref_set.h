#ifndef BZLA_NODE_UNORDERED_NODE_REF_SET_H_INCLUDED
#define BZLA_NODE_UNORDERED_NODE_REF_SET_H_INCLUDED

#include <unordered_set>

#include "node/node.h"

namespace bzla::node {

using unordered_node_ref_set =
    std::unordered_set<ConstNodeRef, std::hash<Node>>;

}

#endif
