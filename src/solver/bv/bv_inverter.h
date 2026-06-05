/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_BV_INVERTER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_INVERTER_H_INCLUDED

#include "env.h"
#include "node/node.h"
#include "node/node_kind.h"

namespace bzla {

using namespace node;

namespace bv {

class BvInverter
{
 public:
  /** Constructor. */
  BvInverter(Env& env);
  /** Destructor. */
  ~BvInverter();

  /**
   * Compute the inverse of a given node with respect to x.
   * @param node The node.
   * @param x    The x node.
   * @return A pair of inverse and conditions. If conditions is not empty,
   *         the resulting inverse is a conditional inverse. Returns a null
   *         node as inverse with empty conditions if x does not occur in
   *         node, or if it occurs multiple times.
   * @note Neither the inverse nor the conditions will contain x.
   */
  std::pair<Node, std::vector<Node>> invert(const Node& node, const Node& x);
  /**
   * Compute the inverse of a given node and path with respect to x.
   * @param node The node.
   * @param x    The x node.
   * @param path The path to x, given as a map from node to index of the
   *             child to follow along the path.
   * @return A pair of inverse and conditions. If conditions is not empty,
   *         the resulting inverse is a conditional inverse. Returns a null
   *         node as inverse with empty conditions if x does not occur in
   *         node, or if it occurs multiple times.
   * @note Neither the inverse nor the conditions will contain x.
   */
  std::pair<Node, std::vector<Node>> invert(
      const Node& node,
      const Node& x,
      const std::unordered_map<Node, size_t>& path);

  /**
   * Compute the invertibility condition for a given node with respect to
   * t and x = node[idx].
   * @param node The node.
   * @param t    The t node.
   * @param idx  The idx of x.
   */
  Node ic(const Node& node, const Node& t, size_t idx);

  /**
   * Compute the path from the given `node` to `x`.
   * @param node The node to start from.
   * @param x    The node to compute the path to.
   * @return The path as a map from node to index of the child to follow. May
   *         be empty if x does not occur in node.
   */
  std::unordered_map<Node, size_t> compute_path(const Node& node,
                                                const Node& x) const;

 private:
  /** @return True if given node is of a kind that can be inverted. */
  bool is_invertible(const Node& node) const;

  /**
   * Compute the inverse of given `node` wrt. to x = node[idx].
   * @note May return an inverse that contains x.
   * @return The inverse, if an inverse be computed, else a null node. Only the
   *         operator kind of the node determines if an inverse can be computed,
   *         hence the resulting inverse may contain x.
   */
  Node inverse(const Node& node, size_t idx, const Node& t);

  std::pair<Node, Node> ic(const Node& node,
                           size_t idx,
                           const std::unordered_map<Node, size_t>& path,
                           bool negate);
  std::pair<Node, Node> ic(Kind predicate,
                           const Node& node,
                           size_t idx,
                           const Node& t,
                           const std::unordered_map<Node, size_t>& path);
  Node ic(Kind predicate,
          const Node& node,
          const Node& t,
          size_t idx,
          size_t idx_x);

  /**
   * Get invertibility condition (IC) for a predicate w.r.t. an AND node.
   *
   * This computes the IC for for (<p> (and x s) t) or (<p> (and s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The AND node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_and(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. an OR node.
   *
   * This computes the IC for for (<p> (or x s) t) or (<p> (or s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The OR node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_or(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_AND node.
   *
   * This computes the IC for for (<p> (bvand x s) t) or (<p> (bvand s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_AND node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_and(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_OR node.
   *
   * This computes the IC for for (<p> (bvor x s) t) or (<p> (bvor s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_OR node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_or(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_ASHR node.
   *
   * This computes the IC for for (<p> (bvashr x s) t) or (<p> (bvashr s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_ASHR node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_ashr(Kind predicate,
                  const Node& node,
                  const Node& t,
                  size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_CONCAT node.
   *
   * This computes the IC for for (<p> (concat x s) t) or (<p> (concat s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_CONCAT node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_concat(Kind predicate,
                    const Node& t,
                    const Node& node,
                    size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_MUL node.
   *
   * This computes the IC for for (<p> (bvmul x s) t) or (<p> (bvmul s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_MUL node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_mul(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_SIGN_EXTEND
   * node.
   *
   * This computes the IC for for (<p> ((_ sign_extend n) x) t) or
   * (<p> ((_sign_extend n) x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_SIGN_EXTEND node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_sext(Kind predicate,
                  const Node& node,
                  const Node& t,
                  size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_SHL node.
   *
   * This computes the IC for for (<p> (bvshl x s) t) or (<p> (bvshl s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_SHL node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_shl(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_SHR node.
   *
   * This computes the IC for for (<p> (bvlshr x s) t) or (<p> (bvlshr s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_SHR node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_shr(Kind predicate, const Node& node, const Node& t, size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_UDIV node.
   *
   * This computes the IC for for (<p> (bvudiv x s) t) or (<p> (bvudiv s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_UDIV node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_udiv(Kind predicate,
                  const Node& node,
                  const Node& t,
                  size_t idx_x);
  /**
   * Get invertibility condition (IC) for a predicate w.r.t. a BV_UREM node.
   *
   * This computes the IC for for (<p> (bvurem x s) t) or (<p> (bvurem s x) t).
   * Here, `x` is the child to solve for.
   *
   * @param predicate The predicate <p>.
   * @param node      The BV_UREM node.
   * @param t         The right-hand-side of the predicate.
   * @param idx_x     The index of x.
   */
  Node ic_bv_urem(Kind predicate,
                  const Node& node,
                  const Node& t,
                  size_t idx_x);

  /** The associated environment. */
  Env& d_env;
  /** The associated node manager. */
  NodeManager& d_nm;
};

}  // namespace bv
}  // namespace bzla
#endif
