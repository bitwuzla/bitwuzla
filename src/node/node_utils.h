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

#include <memory>
#include <unordered_map>
#include <unordered_set>

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
 * @return True if x occurs in the given node.
 * @param node The node to check for x.
 * @param x    The node to check for.
 */
bool has_x(const Node& node, const Node& x);

/**
 * Determine the free variables of the given node.
 *
 * Free variables are determined bottom up per node, i.e., independently of
 * where a node occurs. Collecting all variables bound anywhere in `node` into
 * a single set instead considers a variable bound even if it also occurs free
 * in `node`, which is the case whenever the same variable node is bound at two
 * nested levels.
 *
 * @param node The node to determine the free variables of.
 * @param fvs  Output parameter. The free variables are inserted into this set,
 *             it is not cleared.
 * @return True if the node has free variables.
 */
bool free_vars(const Node& node, std::unordered_set<Node>* fvs = nullptr);

/**
 * Determine the free variables of the given node, reusing the given cache.
 *
 * The free variables of a node never change, thus the cache stays valid and
 * may be shared across calls. Pass the same cache when querying nodes that
 * share subterms, e.g., the assertions of a formula, to avoid traversing the
 * shared subterms once per query.
 *
 * @param node  The node to determine the free variables of.
 * @param fvs   Output parameter. The free variables are inserted into this
 *              set, it is not cleared.
 * @param cache Maps a node to its free variables. A node present in the cache
 *              is fully computed, its set of free variables may be empty.
 * @return True if the node has free variables.
 */
bool free_vars(const Node& node,
               std::unordered_set<Node>* fvs,
               std::unordered_map<Node, std::unordered_set<Node>>& cache);

/**
 * @return n-ary node of given kind.
 * @param kind The node kind.
 * @param terms The children of the node.
 */
Node mk_nary(NodeManager& nm, Kind kind, const std::vector<Node>& terms);

/**
 * @return Default value for given type.
 * @param type Type of default value.
 */
Node mk_default_value(NodeManager& nm, const Type& type);

/**
 * @return Successor of given value. Returns null node if no successor exists.
 * @param value Computes successor of this value.
 */
Node next_value(NodeManager& nm, const Node& value);

/**
 * @return Binder node of given kind.
 * @param kind Binder kind.
 * @param terms The children of the binder node, the terms[size - 1]
 *              is the body of the binder and terms[0]...terms[size - 2]
 *              are variables.
 */
Node mk_binder(NodeManager& nm, Kind kind, const std::vector<Node>& terms);

/**
 * Create a node that represents the conversion from a bit-vector node
 * of size 1 to a Boolean node.
 * @param node The node to convert.
 * @return The conversion node.
 */
Node bv1_to_bool(NodeManager& nm, const Node& node);

/**
 * Create a node that represents the conversion from a Boolean node to a
 * bit-vector node of size 1.
 * @param node The node to convert.
 * @return The conversion node.
 */
Node bool_to_bv1(NodeManager& nm, const Node& node);

/**
 * Rebuild node with same kind and indices but new vector of children.
 *
 * @param node The node to rebuild.
 * @param children The new children of the node.
 * @return Rebuilt node.
 */
Node rebuild_node(NodeManager& nm,
                  const Node& node,
                  const std::vector<Node>& children);

/**
 * Rebuild node with same kind and indices but new children taken from cache.
 *
 * @param node The node to rebuild.
 * @param cache The node cache for children.
 * @return Rebuilt node.
 */
Node rebuild_node(NodeManager& nm,
                  const Node& node,
                  const std::unordered_map<Node, Node>& cache);

/**
 * Applies a substitution map to nodes.
 *
 * Substitutions are applied to the *free* occurrences of the substituted
 * nodes, i.e., a node passed to substitute() has to be the term in whose scope
 * the substitutions are meant to apply. In particular, substituting the
 * variable of a binder in the binder itself is a no-op, since the binder is
 * its binding occurrence: instantiating a binder requires passing its body,
 * not the binder.
 *
 * Substituting a variable is capture-avoiding: a binder that rebinds the
 * variable shadows it, and a binder whose variable occurs free in the term the
 * variable is substituted with is renamed so that it cannot capture it. The
 * variables of the binders in the result are thus not necessarily the ones in
 * the given node.
 *
 * The substitution cache is shared across calls to substitute(), and the
 * information needed to avoid capture is computed only once, when the first
 * binder is encountered.
 *
 * @note Requires the substitutions to be type preserving. The substituter
 *       refers to the substitution map, which must outlive it and must not be
 *       modified during its lifetime.
 */
class Substituter
{
 public:
  /**
   * Constructor.
   *
   * @param nm The associated node manager.
   * @param substitutions The substitution map to apply.
   * @param follow_substs Apply substitutions to substituted terms. Requires
   *                      the substitution map to be acyclic.
   */
  Substituter(NodeManager& nm,
              const std::unordered_map<Node, Node>& substitutions,
              bool follow_substs = true);
  /** The substitution map must outlive the substituter. */
  Substituter(NodeManager& nm,
              std::unordered_map<Node, Node>&& substitutions,
              bool follow_substs = true) = delete;
  ~Substituter();

  /**
   * Apply the substitutions to `node`.
   *
   * @param node The node to process.
   * @return The node with substitutions applied. The given node if no
   *         substitutions given.
   */
  Node substitute(const Node& node);

  /**
   * @return The number of nodes replaced by their substitution in all calls
   *         to substitute() so far. Nodes cached by a previous call are not
   *         counted again.
   */
  uint64_t num_substs() const { return d_num_substs; }

 private:
  struct Capture;

  /**
   * Apply `substitutions` to `node`, caching the results in `cache`.
   *
   * Binders that need a scope of their own are processed by
   * substitute_binder(), which recurses with the substitution map and the
   * cache of that scope.
   */
  Node substitute_aux(const Node& node,
                      const std::unordered_map<Node, Node>& substitutions,
                      std::unordered_map<Node, Node>& cache);

  /** Apply substitutions to the body of a binder that needs its own scope. */
  Node substitute_binder(const Node& binder,
                         const std::unordered_map<Node, Node>& substitutions,
                         bool captured);

  /** @return True if `binder` captures a substitution. */
  bool is_captured(const Node& binder);

  /** The associated node manager. */
  NodeManager& d_nm;
  /** The substitution map. */
  const std::unordered_map<Node, Node>& d_substitutions;
  /** True to apply substitutions to substituted terms. */
  bool d_follow_substs;
  /**
   * The substitution cache. Only nodes in the scope of the nodes passed to
   * substitute() are cached, nodes below a binder that shadows or renames a
   * variable are not.
   */
  std::unordered_map<Node, Node> d_cache;
  /**
   * Determines whether a binder captures a substitution. Created when the
   * first binder is encountered, nodes without binders do not need it.
   */
  std::unique_ptr<Capture> d_capture;
  /** The number of nodes replaced by their substitution. */
  uint64_t d_num_substs = 0;
};

/**
 * Apply substitutions to node.
 *
 * Convenience function for a single node, see Substituter for the semantics.
 *
 * @param node The node to process.
 * @param substitutions The substitution map to apply.
 * @param follow_substs Apply substitutions to substituted terms, see
 *                      Substituter::Substituter().
 * @return The node with substitutions applied. The given node if no
 *         substitutions given.
 */
Node substitute(NodeManager& nm,
                const Node& node,
                const std::unordered_map<Node, Node>& substitutions,
                bool follow_substs = true);

/**
 * Invert Boolean or bit-vector node.
 *
 * @param node The node to invert.
 * @return The inverted node.
 */
Node invert_node(NodeManager& nm, const Node& node);

}  // namespace bzla::node::utils
#endif
