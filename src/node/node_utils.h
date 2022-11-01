#ifndef BZLA_NODE_NODE_UTILS_H_INCLUDED
#define BZLA_NODE_NODE_UTILS_H_INCLUDED

#include "node/node.h"

namespace bzla::node::utils {

/**
 * @return True if given node corresponds to a (rewritten) OR node.
 * @param node   The node to check.
 * @param child0 The (resulting) first child of the extracted or node.
 * @param child1 The (resulting) second child of the extracted or node.
 */
bool is_or(const Node& node, Node& child0, Node& child1);
/**
 * @return True if given node corresponds to a (rewritten) XOR node.
 * @param node   The node to check.
 * @param child0 The (resulting) first child of the extracted xor node.
 * @param child1 The (resulting) second child of the extracted xor node.
 */
bool is_xor(const Node& node, Node& child0, Node& child1);
/**
 * @return True if given node corresponds to a (rewritten) XNOR node.
 * @param node   The node to check.
 * @param child0 The (resulting) first child of the extracted xnor node.
 * @param child1 The (resulting) second child of the extracted xnor node.
 */
bool is_xnor(const Node& node, Node& child0, Node& child1);

/**
 * @return True if given node corresponds to a (rewritten) BV_NEG node.
 * @param node  The node to check.
 * @param child The (resulting) child of the extracted bvneg node.
 */
bool is_bv_neg(const Node& node, Node& child);
/**
 * @return True if given node corresponds to a (rewritten) BV_OR node.
 * @param node   The node to check.
 * @param child0 The (resulting) first child of the extracted bvor node.
 * @param child1 The (resulting) second child of the extracted bvor node.
 */
bool is_bv_or(const Node& node, Node& child0, Node& child1);
/**
 * @return True if given node corresponds to a (rewritten) BV_SIGN_EXTEND node.
 * @param node  The node to check.
 * @param child The (resulting) child of the extracted sign_extend node.
 */
bool is_bv_sext(const Node& node, Node& child);
/**
 * @return True if given node corresponds to a (rewritten) BV_OR node.
 * @param node   The node to check.
 * @param child0 The (resulting) first child of the extracted bvsub node.
 * @param child1 The (resulting) second child of the extracted bvsub node.
 */
bool is_bv_sub(const Node& node, Node& child0, Node& child1);
/**
 * @return True if given node corresponds to a (rewritten) BV_XNOR node.
 * @param node   The node to check.
 * @param child0 The (resulting) first child of the extracted bvxnor node.
 * @param child1 The (resulting) second child of the extracted bvxnor node.
 */
bool is_bv_xnor(const Node& node, Node& child0, Node& child1);
}

#endif
