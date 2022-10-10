#ifndef BZLA_NODE_NODE_UTILS_H_INCLUDED
#define BZLA_NODE_NODE_UTILS_H_INCLUDED

#include "node/node.h"

namespace bzla::node::utils {
/**
 * @return True if given node corresponds to a (rewritten) BV_XNOR node.
 * @param node The node to check.
 */
bool is_bv_xnor(const Node& node);
/**
 * @return True if given node corresponds to a (rewritten) BV_NEG node.
 * @param node The node to check.
 */
bool is_bv_neg(const Node& node);
}

#endif
