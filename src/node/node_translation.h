#ifndef BZLA_NODE_NODE_TRANSLATION_H_INCLUDED
#define BZLA_NODE_NODE_TRANSLATION_H_INCLUDED

extern "C" {
#include "bzlanode.h"
}

#include "node/node.h"
#include "node/node_manager.h"

namespace bzla::node {

Node translate_bzla_node(NodeManager& nm, BzlaNode* node);

}

#endif
