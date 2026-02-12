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
#include "node/node_kind.h"
#include "node/node_manager.h"

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
    return rewriter.mk_node(
        Kind::BV_NOT,
        {rewriter.mk_node(Kind::BV_CONCAT, {node[0][0], node[1][0]})});
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

/**
 * match:  (bvor t (bvshl b t))
 * result: (bvadd t (bvshl b t))
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_NOT_OR_SHL>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  //  Note: Do not use rewriter.is_bv_or() here as this may trigger recursive
  //  calls.
  if (node.is_inverted() && node[0].kind() == Kind::BV_AND)
  {
    const Node& or0 = node[0][0];
    const Node& or1 = node[0][1];
    if (or0.is_inverted() && or0[0].kind() == Kind::BV_SHL
        && rewriter.is_inverted_node_of(or0[0][1], or1))
    {
      return rewriter.mk_node(Kind::BV_ADD,
                              {or0[0], rewriter.invert_node(or1)});
    }
    else if (or1.is_inverted() && or1[0].kind() == Kind::BV_SHL
             && rewriter.is_inverted_node_of(or1[0][1], or0))
    {
      return rewriter.mk_node(Kind::BV_ADD,
                              {or1[0], rewriter.invert_node(or0)});
    }
  }
  assert(node[0].kind() != Kind::BV_OR);  // should be eliminated
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

namespace {

Node
_bv_extract_lower_rev(Rewriter& rewriter, const Kind kind, const Node& node)
{
  if (kind == Kind::BV_NOT)
  {
    if (node[0].kind() == Kind::BV_EXTRACT && node[0].index(1) == 0)
    {
      Node bvnot = rewriter.mk_node(Kind::BV_NOT, {node[0][0]});
      return rewriter.mk_node(Kind::BV_EXTRACT, {bvnot}, node[0].indices());
    }
  }
  else if (kind == Kind::BV_ADD || kind == Kind::BV_MUL)
  {
    if (node[0].kind() == Kind::BV_EXTRACT && node[0].index(1) == 0
        && node[1].kind() == Kind::BV_EXTRACT && node[1].index(1) == 0
        && node[0][0].type() == node[1][0].type())
    {
      assert(node[0].index(0) == node[1].index(0));
      Node t = rewriter.mk_node(kind, {node[0][0], node[1][0]});
      return rewriter.mk_node(Kind::BV_EXTRACT, {t}, node[0].indices());
    }
    else if (node[0].is_value() && node[1].kind() == Kind::BV_EXTRACT
             && node[1].index(1) == 0)
    {
      uint64_t ext = node[1][0].type().bv_size() - node[0].type().bv_size();
      Node val = rewriter.nm().mk_value(node[0].value<BitVector>().bvzext(ext));
      Node t   = rewriter.mk_node(kind, {val, node[1][0]});
      return rewriter.mk_node(Kind::BV_EXTRACT, {t}, node[1].indices());
    }
    else if (node[1].is_value() && node[0].kind() == Kind::BV_EXTRACT
             && node[0].index(1) == 0)
    {
      uint64_t ext = node[0][0].type().bv_size() - node[1].type().bv_size();
      Node val = rewriter.nm().mk_value(node[1].value<BitVector>().bvzext(ext));
      Node t   = rewriter.mk_node(kind, {val, node[0][0]});
      return rewriter.mk_node(Kind::BV_EXTRACT, {t}, node[0].indices());
    }
  }
  return node;
}

}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV1>::_apply(
    Rewriter& rewriter, const Node& node)
{
  assert(node.kind() == Kind::BV_NOT);
  return _bv_extract_lower_rev(rewriter, Kind::BV_NOT, node);
}

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV2>::_apply(
    Rewriter& rewriter, const Node& node)
{
  assert(node.kind() == Kind::BV_ADD);
  return _bv_extract_lower_rev(rewriter, Kind::BV_ADD, node);
}

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV3>::_apply(
    Rewriter& rewriter, const Node& node)
{
  assert(node.kind() == Kind::BV_MUL);
  return _bv_extract_lower_rev(rewriter, Kind::BV_MUL, node);
}

template <>
Node
RewriteRule<RewriteRuleKind::NORM_BV_MUL_POW2_REV>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  if (node[1].is_value() && node[1].value<BitVector>().is_zero()
      && node[0].kind() == Kind::BV_EXTRACT && node[0].index(1) == 0
      && node[0][0].type() == node.type())
  {
    uint64_t tz = node[1].type().bv_size();
    assert(tz <= std::numeric_limits<uint32_t>::max());
    auto pow2 = rewriter.nm().mk_value(
        BitVector::mk_one(node.type().bv_size()).ibvshl(tz));
    return rewriter.mk_node(Kind::BV_MUL, {pow2, node[0][0]});
  }
  return node;
}

/**
 * match: (bvadd (bvmul a t1) (bvmul a t2))
 * result: (bvmul a (bvadd t1 t2))
 *
 * match: (bvadd a (bvmul a t2))
 * result: (bvmul a (bvadd 1 t2))
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_FACT_BV_ADD_MUL>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.kind() == Kind::BV_ADD);

  if (node[0].kind() == Kind::BV_MUL && node[1].kind() == Kind::BV_MUL)
  {
    size_t ic, i1;
    if (node[0][0] == node[1][0] || node[0][0] == node[1][1])
    {
      ic = 0;
      i1 = node[0][0] == node[1][0] ? 1 : 0;
    }
    else if (node[0][1] == node[1][0] || node[0][1] == node[1][1])
    {
      ic = 1;
      i1 = node[0][1] == node[1][0] ? 1 : 0;
    }
    else
    {
      return node;
    }

    const Node& c  = node[0][ic];
    const Node& t0 = node[0][1 - ic];
    const Node& t1 = node[1][i1];
    Node add       = rewriter.mk_node(Kind::BV_ADD, {t0, t1});
    auto res       = rewriter.mk_node(Kind::BV_MUL, {c, add});
    return res;
  }
  if (((node[0].kind() == Kind::BV_MUL
        && (node[0][0] == node[1] || node[0][1] == node[1]))
       || (node[1].kind() == Kind::BV_MUL
           && (node[1][0] == node[0] || node[1][1] == node[0]))))
  {
    size_t ic, i0;
    if (node[0].kind() == Kind::BV_MUL)
    {
      ic = 1;
      i0 = node[0][0] == node[1] ? 1 : 0;
    }
    else
    {
      ic = 0;
      i0 = node[1][0] == node[0] ? 1 : 0;
    }
    const Node& c = node[ic];
    if (!c.is_value())
    {
      const Node& t = node[1 - ic][i0];
      Node one = rewriter.nm().mk_value(BitVector::mk_one(c.type().bv_size()));
      Node add = rewriter.mk_node(Kind::BV_ADD, {one, t});
      return rewriter.mk_node(Kind::BV_MUL, {c, add});
    }
  }
  return node;
}

/**
 * match: (bvadd (bvshl a t1) (bvshl a t2))
 * result: (bvmul a (bvadd (bvshl 1 t1) (bvshl 1 t2)))
 *
 * match: (bvadd (bvshl a t1) a)
 * result: (bvmul a (bvadd (bvshl 1 t1) 1))
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_FACT_BV_ADD_SHL>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.kind() == Kind::BV_ADD);

  if (node[0].kind() == Kind::BV_SHL && node[1].kind() == Kind::BV_SHL)
  {
    if (node[0][0] == node[1][0])
    {
      const Node& c = node[0][0];
      if (!c.is_value() || !c.value<BitVector>().is_one())
      {
        Node one =
            rewriter.nm().mk_value(BitVector::mk_one(c.type().bv_size()));
        Node shl1 = rewriter.mk_node(Kind::BV_SHL, {one, node[0][1]});
        Node shl2 = rewriter.mk_node(Kind::BV_SHL, {one, node[1][1]});
        Node add  = rewriter.mk_node(Kind::BV_ADD, {shl1, shl2});
        auto res  = rewriter.mk_node(Kind::BV_MUL, {c, add});
        return res;
      }
    }
  }
  if ((node[0].kind() == Kind::BV_SHL && node[0][0] == node[1])
      || (node[1].kind() == Kind::BV_SHL && node[1][0] == node[0]))
  {
    size_t idx    = node[0].kind() == Kind::BV_SHL ? 0 : 1;
    const Node& c = node[idx][0];
    if (!c.is_value() || !c.value<BitVector>().is_one())
    {
      Node one  = rewriter.nm().mk_value(BitVector::mk_one(c.type().bv_size()));
      Node shl1 = rewriter.mk_node(Kind::BV_SHL, {one, node[idx][1]});
      Node add  = rewriter.mk_node(Kind::BV_ADD, {shl1, one});
      auto res  = rewriter.mk_node(Kind::BV_MUL, {c, add});
      return res;
    }
  }
  return node;
}

/**
 * match: (bvshl (bvmul a t1) t2)
 * result: (bvmul a (bvshl t1 t2)) for a < t1
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_FACT_BV_SHL_MUL>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.kind() == Kind::BV_SHL);

  if (node[0].kind() == Kind::BV_MUL)
  {
    size_t idx = node[0][0] < node[0][1] ? 0 : 1;
    Node bvshl = rewriter.mk_node(Kind::BV_SHL, {node[0][1 - idx], node[1]});
    return rewriter.mk_node(Kind::BV_MUL, {node[0][idx], bvshl});
  }
  return node;
}

/**
 * match: (bvmul (bvshl a t1) t2)
 * result: (bvmul a (bvshl t2 t1)) for a < t2
 */
template <>
Node
RewriteRule<RewriteRuleKind::NORM_FACT_BV_MUL_SHL>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.kind() == Kind::BV_MUL);

  if (node[0].kind() == Kind::BV_SHL || node[1].kind() == Kind::BV_SHL)
  {
    size_t idx        = node[0].kind() == Kind::BV_SHL ? 0 : 1;
    const Node& bvshl = node[idx];
    const Node& other = node[1 - idx];
    if (bvshl[0] < other)
    {
      return rewriter.mk_node(
          Kind::BV_MUL,
          {bvshl[0], rewriter.mk_node(Kind::BV_SHL, {other, bvshl[1]})});
    }
  }
  return node;
}

}  // namespace bzla
