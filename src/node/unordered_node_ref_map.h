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
