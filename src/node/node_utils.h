/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_NODE_UTILS_H_INCLUDED
#define BZLA_NODE_NODE_UTILS_H_INCLUDED

#include <unordered_map>

#include "node/node.h"

namespace bzla::node::utils {

/**
 * @return True if given node corresponds to a (rewritten) BV_SIGN_EXTEND
 * node.
 * @param node  The node to check.
 * @param child The (resulting) child of the extracted sign_extend node.
 */
bool is_bv_sext(const Node& node, Node& child);

/**
 * @return n-ary node of given kind.
 * @param kind The node kind.
 * @param terms The children of the node.
 */
Node mk_nary(Kind kind, const std::vector<Node>& terms);

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

/**
 * Create a node that represents the conversion from a bit-vector node
 * of size 1 to a Boolean node.
 * @param node The node to convert.
 * @return The conversion node.
 */
Node bv1_to_bool(const Node& node);

/**
 * Create a node that represents the conversion from a Boolean node to a
 * bit-vector node of size 1.
 * @param node The node to convert.
 * @return The conversion node.
 */
Node bool_to_bv1(const Node& node);

/**
 * Rebuild node with same kind and indices but new vector of children.
 *
 * @param node The node to rebuild.
 * @param children The new children of the node.
 * @return Rebuilt node.
 */
Node rebuild_node(const Node& node, const std::vector<Node>& children);

/**
 * Rebuild node with same kind and indices but new children taken from cache.
 *
 * @param node The node to rebuild.
 * @param cache The node cache for children.
 * @return Rebuilt node.
 */
Node rebuild_node(const Node& node,
                  const std::unordered_map<Node, Node>& cache);
}

#endif
