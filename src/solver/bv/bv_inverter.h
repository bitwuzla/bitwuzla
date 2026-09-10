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

namespace bv {

class BvInverter
{
 public:
  /**
   * Constructor.
   *
   * Optionally configures inverter to produce under-determined inverses on
   * inverse() and invert() (`underdet` = true).
   *
   * If configured, produces under-determined inverses for BV_EXTRACT and
   * BV_CONCAT. For extract, bits that were sliced away are reconstructed as
   * fresh constants. For concat, instead of a conditional inverse, we compute
   * an inverse while disregarding that it is conditional on s.
   *
   * @note These under-determined inverses may only be used where it is not
   *       required that inverses are exact, e.g., for quantifier instantiation.
   *
   * @param env      The associated environment.
   * @param underdet True to enable under-determined (lossy) inverses for
   *                 extract and concat.
   */
  BvInverter(Env& env, bool underdet = false);
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
   * Compute the invertibility condition (IC) for a given node with respect to
   * `t` (i.e., (= node t)) and x = node[idx].
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

  /**
   * Compute the invertibility condition (IC) for a predicate w.r.t. operand
   * x = node[idx_x] of a given node.
   *
   * This computes the IC for P[x] = (<predicate> node t) if `idx` is 0, and
   * for (<predicate> t node) if `idx` is 1. That is, the resulting condition
   * is satisfied exactly when the predicate is solvable for x, i.e., it is
   * equivalent to (exists x. P[x]).
   *
   * @note If `node` is x itself, `idx_x` is ignored. If it is a bit-vector
   *       inequality, then `predicate` must be Kind::EQUAL as inequalities
   *       are only reachable via equalities on the path when chaining inverses
   *       in invert().
   *
   * @note Assumes that x occurs in neither s = node[1 - idx_x] nor `t`. The
   *       resulting condition is a formula over s and `t`, thus callers that
   *       pass a `t` containing x must check the result for occurrences of x.
   *
   * The ICs computed here and in the ic_*() functions this dispatches to are
   * given in Tables 3-7 of:
   *
   *   A. Niemetz, M. Preiner, A. Reynolds, C. Barrett, C. Tinelli. On Solving
   *   Quantified Bit-Vector Constraints using Invertibility Conditions.
   *   Formal Methods in System Design 57(2), 2021.
   *
   * @param predicate The predicate.
   * @param node      The node containing x. Its kind must be invertible, see
   *                  is_invertible().
   * @param t         The other operand of the predicate.
   * @param idx       The index at which `node` occurs in the predicate.
   * @param idx_x     The index of x in `node`.
   * @return The invertibility condition.
   */
  Node ic(node::Kind predicate,
          const Node& node,
          const Node& t,
          size_t idx,
          size_t idx_x);

  /**
   * Get invertibility condition (IC) for a given predicate node w.r.t. x, along
   * with the subterm of the node the condition was computed for.
   *
   * This computes the IC for `node` if `negate` is false, and for its negation
   * otherwise. Since ICs are defined for a single operator application, this
   * descends at most one level below `node`.
   *
   * The returned subterm is the term the condition was computed for, i.e.,
   * the term that invert() abstracts as a fresh constant in the corresponding
   * choice condition, and from which it continues the inversion chain.
   *
   * @param node   The node
   * @param idx    The index of the operand of `node` that contains x, i.e.,
   *               path.at(node).
   * @param path   The path from `node` to x, see compute_path().
   * @param negate True to compute the IC for the negation of `node`.
   * @return A pair of the invertibility condition and the subterm of `node`
   *         it was computed for.
   */
  std::pair<Node, Node> ic(const Node& node,
                           size_t idx,
                           const std::unordered_map<Node, size_t>& path,
                           bool negate);
  /**
   * Helper for ic() above.
   *
   * Get invertibility condition (IC) for a predicate w.r.t. the operand of a
   * given node on a given path, along with that operand.
   *
   * Same as ic(predicate, node, t, idx, idx_x) with idx_x = path.at(node).
   *
   * @param predicate The predicate <p>.
   * @param node      The node containing x. Must occur on `path`.
   * @param idx       The index at which `node` occurs in the predicate.
   * @param t         The other operand of the predicate.
   * @param path      The path to x, see compute_path().
   * @return A pair of the invertibility condition and the operand of `node`
   *         that contains x.
   */
  std::pair<Node, Node> ic(node::Kind predicate,
                           const Node& node,
                           size_t idx,
                           const Node& t,
                           const std::unordered_map<Node, size_t>& path);
  /**
   * Get invertibility condition (IC) for a predicate (<p> x t) w.r.t x.
   * @param predicate The predicate <p>.
   * @param t         The right-hand-side of the predicate.
   * @return The invertibility condition.
   */
  Node ic_predicate(node::Kind predicate, const Node& t);

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
   * @return The invertibility condition.
   */
  Node ic_and(node::Kind predicate,
              const Node& node,
              const Node& t,
              size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_or(node::Kind predicate,
             const Node& node,
             const Node& t,
             size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_bv_and(node::Kind predicate,
                 const Node& node,
                 const Node& t,
                 size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_bv_or(node::Kind predicate,
                const Node& node,
                const Node& t,
                size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_bv_ashr(node::Kind predicate,
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
   * @return The invertibility condition.
   */
  Node ic_bv_concat(node::Kind predicate,
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
   * @return The invertibility condition.
   */
  Node ic_bv_mul(node::Kind predicate,
                 const Node& node,
                 const Node& t,
                 size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_bv_sext(node::Kind predicate,
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
   * @return The invertibility condition.
   */
  Node ic_bv_shl(node::Kind predicate,
                 const Node& node,
                 const Node& t,
                 size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_bv_shr(node::Kind predicate,
                 const Node& node,
                 const Node& t,
                 size_t idx_x);
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
   * @return The invertibility condition.
   */
  Node ic_bv_udiv(node::Kind predicate,
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
   * @return The invertibility condition.
   */
  Node ic_bv_urem(node::Kind predicate,
                  const Node& node,
                  const Node& t,
                  size_t idx_x);

  /** The associated environment. */
  Env& d_env;
  /** The associated node manager. */
  NodeManager& d_nm;
  /** Enable under-determined (lossy) inverses for extract/concat. */
  bool d_underdet;
};

}  // namespace bv
}  // namespace bzla
#endif
