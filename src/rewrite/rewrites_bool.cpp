/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewrites_bool.h"

#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewrite_utils.h"

namespace bzla {

using namespace node;

/* and ---------------------------------------------------------------------- */

/**
 * Constant folding, matches when all operands are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::AND_EVAL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  return NodeManager::get().mk_value(node[0].value<bool>()
                                     && node[1].value<bool>());
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (and false a) or (and a false)
 * result: false
 *
 * match:  (and true a) or (and a true)
 * result: a
 */
namespace {
Node
_rw_and_special_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && !node[idx1].is_value())
  {
    if (node[idx0].value<bool>())
    {
      return node[idx1];
    }
    return NodeManager::get().mk_value(false);
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  Node res = _rw_and_special_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_special_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and x (and y a)) with x, y constant values
 * result: (and z a) with z = x /\ y
 */
namespace {
Node
_rw_and_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && node[idx1].kind() == Kind::AND)
  {
    BitVector z;
    if (node[idx1][0].is_value())
    {
      bool z = node[idx0].value<bool>() && node[idx1][0].value<bool>();
      return rewriter.mk_node(Kind::AND,
                              {NodeManager::get().mk_value(z), node[idx1][1]});
    }
    if (node[idx1][1].is_value())
    {
      bool z = node[idx0].value<bool>() && node[idx1][1].value<bool>();
      return rewriter.mk_node(Kind::AND,
                              {NodeManager::get().mk_value(z), node[idx1][0]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_CONST>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  Node res = _rw_and_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match;  (and a a)
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::AND_IDEM1>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] == node[1])
  {
    return node[0];
  }
  return node;
}

/**
 * match;  (and (and a b) (and a c))
 * result: (and a (and b c))
 */
namespace {
Node
_rw_and_idem2(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::AND && node[idx1].kind() == Kind::AND)
  {
    if (node[idx0][0] == node[idx1][0] || node[idx0][1] == node[idx1][0])
    {
      return rewriter.mk_node(Kind::AND, {node[idx0], node[idx1][1]});
    }
    if (node[idx0][0] == node[idx1][1] || node[idx0][1] == node[idx1][1])
    {
      return rewriter.mk_node(Kind::AND, {node[idx0], node[idx1][0]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_IDEM2>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  Node res = _rw_and_idem2(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_idem2(rewriter, node, 1);
  }
  return res;
}

/**
 * match;  (and a (and a b))
 * result: (and a b)
 */
namespace {
Node
_rw_and_idem3(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::AND
      && (node[idx0][0] == node[idx1] || node[idx0][1] == node[idx1]))
  {
    return node[idx0];
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_IDEM3>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  Node res = _rw_and_idem3(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_idem3(rewriter, node, 1);
  }
  return res;
}

/**
 * match;  (and a (not a))
 * result: false
 */
namespace {
Node
_rw_and_contra1(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (rewrite::utils::is_inverted_of(node[idx0], node[idx1]))
  {
    return NodeManager::get().mk_value(false);
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_CONTRA1>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_and_contra1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_contra1(rewriter, node, 1);
  }
  return res;
}

/**
 * match;  (and (and a b) (and (not a) c))
 * result: false
 */
namespace {
Node
_rw_and_contra2(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::AND && node[idx1].kind() == Kind::AND)
  {
    if (rewrite::utils::is_inverted_of(node[idx0][0], node[idx1][0])
        || rewrite::utils::is_inverted_of(node[idx0][0], node[idx1][1])
        || rewrite::utils::is_inverted_of(node[idx0][1], node[idx1][0])
        || rewrite::utils::is_inverted_of(node[idx0][1], node[idx1][1]))
    {
      return NodeManager::get().mk_value(false);
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_CONTRA2>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_and_contra2(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_contra2(rewriter, node, 1);
  }
  return res;
}

/**
 * match;  (and a (and (not a) b))
 * result: false
 */
namespace {
Node
_rw_and_contra3(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::AND)
  {
    if (rewrite::utils::is_inverted_of(node[idx0][0], node[idx1])
        || rewrite::utils::is_inverted_of(node[idx0][1], node[idx1]))
    {
      return NodeManager::get().mk_value(false);
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_CONTRA3>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_and_contra3(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_contra3(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and (not (and a b)) (not (and a (not b))))
 *         (and (not (and a b)) (not (and (not b) a)))
 * result: (not a)
 */
namespace {
Node
_rw_and_resol1(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_inverted() && node[idx0][0].kind() == Kind::AND
      && node[idx1].is_inverted() && node[idx1][0].kind() == Kind::AND)
  {
    if ((node[idx0][0][0] == node[idx1][0][0]
         && rewrite::utils::is_inverted_of(node[idx0][0][1], node[idx1][0][1]))
        || (node[idx0][0][0] == node[idx1][0][1]
            && rewrite::utils::is_inverted_of(node[idx0][0][1],
                                              node[idx1][0][0])))
    {
      return rewriter.invert_node(node[idx0][0][0]);
    }
    if ((node[idx0][0][1] == node[idx1][0][0]
         && rewrite::utils::is_inverted_of(node[idx0][0][1], node[idx1][0][1]))
        || (node[idx0][0][1] == node[idx1][0][1]
            && rewrite::utils::is_inverted_of(node[idx0][0][0],
                                              node[idx1][0][0])))
    {
      return rewriter.invert_node(node[idx0][0][1]);
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_RESOL1>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_and_resol1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_resol1(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and (and a b) (not (and a c)))
 * result: (and a b)
 */
namespace {
Node
_rw_and_subsum1(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  Node or0, or1;
  if (node[idx0].kind() == Kind::AND && rewriter.is_or(node[idx1], or0, or1))
  {
    if (node[idx0][0] == or0 || node[idx0][0] == or1 || node[idx][1] == or0
        || node[idx0][1] == or1)
    {
      return node[idx0];
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_SUBSUM1>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_and_subsum1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_subsum1(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and (or a b) a)
 * result: a
 */
namespace {
Node
_rw_and_subsum2(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  Node or0, or1;
  if (rewriter.is_or(node[idx1], or0, or1))
  {
    if (node[idx0] == or0 || node[idx0] == or1)
    {
      return node[idx0];
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_SUBSUM2>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_and_subsum2(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_subsum2(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and (and a b) (not (and a c)))
 * result: (and((and a b) (not c))
 */
namespace {
Node
_rw_and_not_and1(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::AND && node[idx1].is_inverted()
      && node[idx1][0].kind() == Kind::AND)
  {
    if (node[idx0][0] == node[idx1][0][0] || node[idx0][1] == node[idx1][0][0])
    {
      return rewriter.mk_node(
          Kind::AND, {node[idx0], rewriter.invert_node(node[idx1][0][1])});
    }
    if (node[idx0][0] == node[idx1][0][1] || node[idx0][1] == node[idx1][0][1])
    {
      return rewriter.mk_node(
          Kind::AND, {node[idx0], rewriter.invert_node(node[idx1][0][0])});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_NOT_AND1>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_and_not_and1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_not_and1(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and a (not (and a b)))
 * result: (and a (not b))
 */
namespace {
Node
_rw_and_not_and2(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx1].is_inverted() && node[idx1][0].kind() == Kind::AND)
  {
    if (node[idx0] == node[idx1][0][0])
    {
      return rewriter.mk_node(
          Kind::AND, {node[idx0], rewriter.invert_node(node[idx1][0][1])});
    }
    if (node[idx0] == node[idx1][0][1])
    {
      return rewriter.mk_node(
          Kind::AND, {node[idx0], rewriter.invert_node(node[idx1][0][0])});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::AND_NOT_AND2>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_and_not_and2(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_and_not_and2(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (and (bvult a b) (bvult b a))
 *         (and (bvslt a b) (bvslt b a))
 * result: false
 */
template <>
Node
RewriteRule<RewriteRuleKind::AND_BV_LT_FALSE>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (((node[0].kind() == Kind::BV_ULT && node[1].kind() == Kind::BV_ULT)
       || (node[0].kind() == Kind::BV_SLT && node[1].kind() == Kind::BV_SLT))
      && node[0][0] == node[1][1] && node[0][1] == node[1][0])
  {
    return NodeManager::get().mk_value(false);
  }
  return node;
}

/*
 * match:  (and (bvnot (bvult a b)) (bvnot (bvult b a)))
 *         (and (bvnot (bvslt a b)) (bvnot (bvslt b a)))
 * result: (= a b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::AND_BV_LT>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].is_inverted() && node[1].is_inverted()
      && ((node[0][0].kind() == Kind::BV_ULT
           && node[1][0].kind() == Kind::BV_ULT)
          || (node[0][0].kind() == Kind::BV_SLT
              && node[1][0].kind() == Kind::BV_SLT))
      && node[0][0][0] == node[1][0][1] && node[0][0][1] == node[1][0][0])
  {
    return rewriter.mk_node(Kind::EQUAL, {node[0][0][0], node[0][0][1]});
  }
  return node;
}

/* not ---------------------------------------------------------------------- */

/**
 * Constant folding, matches when the operand is a value.
 */
template <>
Node
RewriteRule<RewriteRuleKind::NOT_EVAL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value()) return node;
  return NodeManager::get().mk_value(!node[0].value<bool>());
}

/**
 * match:  (not (not a))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::NOT_NOT>::_apply(Rewriter& rewriter,
                                              const Node& node)
{
  (void) rewriter;
  if (node[0].kind() != Kind::NOT) return node;
  return node[0][0];
}

/**
 * match:  (xnor a b) (rewritten to (not (xor a b)))
 * result: (= a b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::NOT_XOR>::_apply(Rewriter& rewriter,
                                              const Node& node)
{
  assert(node.num_children() == 1);
  Node xnor0, xnor1;
  if (rewriter.is_xnor(node, xnor0, xnor1))
  {
    return rewriter.mk_node(Kind::EQUAL, {xnor0, xnor1});
  }
  return node;
}

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::IMPLIES_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  return rewriter.invert_node(
      rewriter.mk_node(Kind::AND, {node[0], rewriter.invert_node(node[1])}));
}

template <>
Node
RewriteRule<RewriteRuleKind::OR_ELIM>::_apply(Rewriter& rewriter,
                                              const Node& node)
{
  return rewriter.invert_node(rewriter.mk_node(
      Kind::AND,
      {rewriter.invert_node(node[0]), rewriter.invert_node(node[1])}));
}

template <>
Node
RewriteRule<RewriteRuleKind::XOR_ELIM>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  return rewriter.mk_node(
      Kind::AND,
      {rewriter.mk_node(Kind::OR, {node[0], node[1]}),
       rewriter.invert_node(rewriter.mk_node(Kind::AND, {node[0], node[1]}))});
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
