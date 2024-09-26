/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewrites_bv_norm.h"

#include "bv/bitvector.h"

namespace bzla {

using namespace node;

/**
 * match:  (bvadd (bvnot (bvmul a (bvnot b))) (_ bv1 N))
 *         (is the rewritten form of (bvneg (bvmul a (bvnot b))))
 * result: (bvadd a (bvmul a b))
 */
namespace {
Node
_rw_norm_bv_add_mul(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  Node neg0;
  if (rewriter.is_bv_neg(node, neg0) && neg0.kind() == Kind::BV_MUL
      && neg0[idx1].kind() == Kind::BV_NOT)
  {
    return rewriter.mk_node(
        Kind::BV_ADD,
        {neg0[idx0],
         rewriter.mk_node(Kind::BV_MUL, {neg0[idx0], neg0[idx1][0]})});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_ADD_MUL>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  Node res = _rw_norm_bv_add_mul(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_norm_bv_add_mul(rewriter, node, 1);
  }
  return res;
}

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_CONCAT_BV_NOT>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  if (node[0].kind() == Kind::BV_NOT && node[1].kind() == Kind::BV_NOT)
  {
    return rewriter.mk_node(Kind::BV_NOT, {rewriter.mk_node(Kind::BV_CONCAT, {node[0][0], node[1][0]})});
  }
  return node;
}



/**
 * match:  (bvadd (bvnot (bvmul a (bvnot b))) (_ bv1 N))
 *         (is the rewritten form of (bvneg (bvmul a (bvnot b))))
 * result: (bvadd a (bvmul a b))
 */
namespace {
Node
_rw_norm_bv_add_concat(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_CONCAT
      && node[idx1].kind() == Kind::BV_CONCAT)
  {
    // (concat 0 a) + (concat b 0) ==> (concat a b)
    if (node[idx0][0].is_value() && node[idx0][0].value<BitVector>().is_zero()
        && node[idx1][1].is_value()
        && node[idx1][1].value<BitVector>().is_zero()
        && node[idx0][0].type() == node[idx1][0].type())
    {
      return rewriter.mk_node(Kind::BV_CONCAT, {node[idx1][0], node[idx0][1]});
    }
    // (concat a 0) + (concat 0 b) ==> (concat a b)
    if (node[idx0][1].is_value() && node[idx0][1].value<BitVector>().is_zero()
        && node[idx1][0].is_value()
        && node[idx1][0].value<BitVector>().is_zero()
        && node[idx0][1].type() == node[idx1][1].type())
    {
      return rewriter.mk_node(Kind::BV_CONCAT, {node[idx0][0], node[idx1][1]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_ADD_CONCAT>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  Node res = _rw_norm_bv_add_concat(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_norm_bv_add_concat(rewriter, node, 1);
  }
  return res;
}

/*
 * match:  (bvnot (bvand (bvnot a)) (bvnot (bvshl b a)))
 *         (is rewritten form of (bvor a (bvshl b a)))
 * result: (bvadd a (bvshl b a))
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_NOT_OR_SHL>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  Node or0, or1;
  if (rewriter.is_bv_or(node, or0, or1))
  {
    if ((or0.kind() == Kind::BV_SHL && or0[1] == or1)
        || (or1.kind() == Kind::BV_SHL && or1[1] == or0))
    {
      return rewriter.mk_node(Kind::BV_ADD, {or0, or1});
    }
  }
  return node;
}

/**
 * match:  (bvshl (bvneg a) b)
 * result: (bvneg (bvshl a b))
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_SHL_NEG>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  Node neg0;
  if (rewriter.is_bv_neg(node[0], neg0))
  {
    return rewriter.mk_node(Kind::BV_NEG,
                            {rewriter.mk_node(Kind::BV_SHL, {neg0, node[1]})});
  }
  return node;
}

}  // namespace bzla
