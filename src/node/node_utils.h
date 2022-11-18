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

/**
 * @return n-ary node of given kind.
 * @param kind The node kind.
 * @param terms The children of the node.
 * @param left_assoc Indicates whether to create left-assoc or right-assoc node.
 */
Node mk_nary(Kind kind, const std::vector<Node>& terms, bool left_assoc = true);

/**
 * @return Default value for given type.
 * @param type Type of default value.
 */
Node mk_default_value(const Type& type);

/**
 * @return Binder node of given kind.
 * @param kind Binder kind.
 * @param terms The children of the binder node, the terms[size - 1]
 *              is the body of the binder and terms[0]...terms[size - 2]
 *              are variables.
 */
Node mk_binder(Kind kind, const std::vector<Node>& terms);
}

#endif
