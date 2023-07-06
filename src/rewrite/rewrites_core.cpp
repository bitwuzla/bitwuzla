/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewrites_core.h"

#include <cmath>

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewrite_utils.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla {

using namespace node;

/* equal -------------------------------------------------------------------- */

/**
 * Constant folding, matches when all operands are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_EVAL>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  NodeManager& nm = NodeManager::get();
  if (node[0].type().is_bool())
  {
    return nm.mk_value(node[0].value<bool>() == node[1].value<bool>());
  }
  if (node[0].type().is_bv())
  {
    return nm.mk_value(
        (node[0].value<BitVector>() == node[1].value<BitVector>()));
  }
  if (node[0].type().is_fp())
  {
    return nm.mk_value(
        (node[0].value<FloatingPoint>() == node[1].value<FloatingPoint>()));
  }
  assert(node[0].type().is_rm());
  return nm.mk_value(
      (node[0].value<RoundingMode>() == node[1].value<RoundingMode>()));
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (= (_ bv0 N) (bvxor a b))
 * result: (= a b)
 *
 * match:  (= (_ bv0 N) (bvor a b))
 * result: (and (= (_ bv0 N ) a) (= (_ bv0 N) b))
 *
 * match:  (= (bvnot (_ bv0 N)) (bvand a b))
 * result: (bvand (= (bvnot (_ bv0 N)) a) (= (bvnot (_ bv0 N)) b))
 *
 * match:  (= (bvnot (_ bv0 N)) (bvxnor a b))
 * result: (= a b)
 *
 * match:  (= a true)
 * result: a
 *
 * match:  (= a false)
 * result: (not a)
 */
namespace {

/**
 * match:  (= (_ bv0 N) (bvnot (bvand a b))
 * result: (and (= (bvnot (_ bv0 N )) a) (= (bvnot (_ bv0 N)) b))
 *
 * match:  (= (bvnot (_ bv0 N)) (bvand a b))
 * result: (bvand (= (bvnot (_ bv0 N)) a) (= (bvnot (_ bv0 N)) b))
 *
 * @note: Traverses all leaf nodes of given BV_AND to avoid recursive calls of
 *        _rw_eq_special_const().
 */
Node
_rw_eq_special_push_ones(Rewriter& rewriter, const Node& node)
{
  bool is_or = node.kind() == Kind::BV_NOT;
  assert(!is_or || node[0].kind() == Kind::BV_AND);
  assert(is_or || node.kind() == Kind::BV_AND);

  Node ones =
      NodeManager::get().mk_value(BitVector::mk_ones(node.type().bv_size()));

  std::vector<Node> eqs;
  node::node_ref_vector visit;
  node::unordered_node_ref_set cache;

  visit.push_back(is_or ? node[0] : node);
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      if (cur.kind() == Kind::BV_AND)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        eqs.push_back(rewriter.mk_node(Kind::EQUAL, {cur, ones}));
      }
    }
  } while (!visit.empty());

  assert(eqs.size() > 1);
  Node res = rewriter.mk_node(Kind::AND, {eqs[0], eqs[1]});
  for (size_t i = 2, size = eqs.size(); i < size; ++i)
  {
    res = rewriter.mk_node(Kind::AND, {res, eqs[i]});
  }
  return res;
}

Node
_rw_eq_special_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && !node[idx1].is_value())
  {
    const Type& type0 = node[idx0].type();
    if (type0.is_bv())
    {
      const BitVector& value0 = node[idx0].value<BitVector>();
      if (value0.is_zero())
      {
        if (node[idx1].kind() == Kind::BV_XOR)
        {
          // 0 == a ^ b  --->  a = b
          return rewriter.mk_node(Kind::EQUAL, {node[idx1][0], node[idx1][1]});
        }
        if (node[idx1].kind() == Kind::BV_NOT
            && node[idx1][0].kind() == Kind::BV_AND)
        {
          // 0 == ~(a & b)  ---> a == 1..1 && b == 1..1
          return _rw_eq_special_push_ones(rewriter, node[idx1]);
        }
      }
      else if (value0.is_ones())
      {
        if (node[idx1].kind() == Kind::BV_AND)
        {
          // 1..1 == a & b  ---> a == 1..1 && b == 1..1
          return _rw_eq_special_push_ones(rewriter, node[idx1]);
        }
        Node xnor0, xnor1;
        if (rewriter.is_bv_xnor(node[idx1], xnor0, xnor1))
        {
          // 1..1 == a XNOR b  --->  a = b
          return rewriter.mk_node(Kind::EQUAL, {xnor0, xnor1});
        }
      }
    }
    else if (type0.is_bool())
    {
      if (node[idx0].value<bool>())
      {
        return node[idx1];
      }
      return rewriter.invert_node(node[idx1]);
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                          const Node& node)
{
  Node res = _rw_eq_special_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_special_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvand a b) (_ bvX N))
 * result: (and
 *           (and
 *             (= (bvnot (_ bv0 n)) a[N - 1 - i: N - i - n])
 *             (= (bvnot (_ bv0 n)) b[N - 1 - i: N - i - n])
 *             ...
 *             (= (_ bv0 m) (bvand a[N - 1 - j: N - j - m]
 *                                 b[N - 1 - j: N - j - m))
 *             ...
 *           ))
 *          for ech slice of zeros and ones of size n and m in X.
 *
 * match:  (= (bvor a b) (_ bvX N))
 * result: (and
 *           (and
 *             (= (_ bv0 n) a[N - 1 - i: N - i - n])
 *             (= (_ bv0 n) b[N - 1 - i: N - i - n])
 *             ...
 *             (= (bvnot (_ bv0 m)) (bvand a[N - 1 - j: N - j - m]
 *                                         b[N - 1 - j: N - j - m))
 *             ...
 *           ))
 *          for ech slice of ones and zeros of size n and m in X.
 */
namespace {
Node
_rw_eq_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;

  if (node[idx0].type().is_bv() && node[idx0].is_value())
  {
    BitVector val = node[idx0].value<BitVector>();

    if (!val.is_zero() && !val.is_ones())
    {
      NodeManager& nm = NodeManager::get();
      std::vector<Node> args;
      Node node10, node11;

      if (node[idx1].kind() == Kind::BV_AND)
      {
        for (uint64_t i = 0, cnt = 0, size = val.size(); i < size; i += cnt)
        {
          uint64_t val_size = val.size();
          bool bit          = val.bit(val_size - 1);
          cnt = bit ? val.count_leading_ones() : val.count_leading_zeros();
          Node ext0 = rewriter.mk_node(Kind::BV_EXTRACT,
                                       {node[idx1][0]},
                                       {size - 1 - i, size - i - cnt});
          Node ext1 = rewriter.mk_node(Kind::BV_EXTRACT,
                                       {node[idx1][1]},
                                       {size - 1 - i, size - i - cnt});
          if (bit)
          {
            args.push_back(rewriter.mk_node(
                Kind::EQUAL, {nm.mk_value(BitVector::mk_ones(cnt)), ext0}));
            args.push_back(rewriter.mk_node(
                Kind::EQUAL, {nm.mk_value(BitVector::mk_ones(cnt)), ext1}));
          }
          else
          {
            args.push_back(rewriter.mk_node(
                Kind::EQUAL,
                {nm.mk_value(BitVector::mk_zero(cnt)),
                 rewriter.mk_node(Kind::BV_AND, {ext0, ext1})}));
          }
          if (val_size > cnt)
          {
            val.ibvextract(val_size - 1 - cnt, 0);
          }
        }
      }
      else if (rewriter.is_bv_or(node[idx1], node10, node11))
      {
        assert(!node10.is_null() && !node11.is_null());

        for (uint64_t i = 0, cnt = 0, size = val.size(); i < size; i += cnt)
        {
          uint64_t val_size = val.size();
          bool bit          = val.bit(val_size - 1);
          cnt = bit ? val.count_leading_ones() : val.count_leading_zeros();
          Node ext0 = rewriter.mk_node(
              Kind::BV_EXTRACT, {node10}, {size - 1 - i, size - i - cnt});
          Node ext1 = rewriter.mk_node(
              Kind::BV_EXTRACT, {node11}, {size - 1 - i, size - i - cnt});
          if (!bit)
          {
            args.push_back(rewriter.mk_node(
                Kind::EQUAL, {nm.mk_value(BitVector::mk_zero(cnt)), ext0}));
            args.push_back(rewriter.mk_node(
                Kind::EQUAL, {nm.mk_value(BitVector::mk_zero(cnt)), ext1}));
          }
          else
          {
            args.push_back(rewriter.mk_node(
                Kind::EQUAL,
                {nm.mk_value(BitVector::mk_ones(cnt)),
                 rewriter.mk_node(Kind::BV_OR, {ext0, ext1})}));
          }
          if (val_size > cnt)
          {
            val.ibvextract(val_size - 1 - cnt, 0);
          }
        }
      }
      uint64_t n = args.size();
      if (n > 0)
      {
        Node res =
            n > 1 ? rewriter.mk_node(Kind::AND, {args[0], args[1]}) : args[0];
        for (uint64_t i = 2; i < n; ++i)
        {
          res = rewriter.mk_node(Kind::AND, {res, args[i]});
        }
        return res;
      }
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_CONST>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_eq_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (= a #b1) b)
 * result: (= a (ite b #b1 #b0))
 *
 * match:  (= (= a #b0) b)
 * result: (= a (ite b #b0 #b1))
 */
namespace {
Node
_rw_eq_eq_const_bv1(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;

  if (node[idx0].kind() == Kind::EQUAL && node[idx0][0].type().is_bv()
      && node[idx0][0].type().bv_size() == 1)
  {
    Node a;
    BitVector t_value;
    if (node[idx0][0].is_value())
    {
      a       = node[idx0][1];
      t_value = node[idx0][0].value<BitVector>();
    }
    else if (node[idx0][1].is_value())
    {
      a       = node[idx0][0];
      t_value = node[idx0][1].value<BitVector>();
    }
    else
    {
      return node;
    }
    NodeManager& nm = NodeManager::get();
    BitVector e_value =
        t_value.is_one() ? BitVector::mk_false() : BitVector::mk_true();
    return rewriter.mk_node(
        Kind::EQUAL,
        {a,
         rewriter.mk_node(
             Kind::ITE,
             {node[idx1], nm.mk_value(t_value), nm.mk_value(e_value)})});
  }
  return node;
}
}  // namespace
template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_EQUAL_CONST_BV1>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  Node res = _rw_eq_eq_const_bv1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_eq_const_bv1(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= a a)
 * result: true
 */
template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_TRUE>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] == node[1])
  {
    return NodeManager::get().mk_value(true);
  }
  return node;
}

/**
 * match:  (= a b) where a and b can be determined to be always disequal,
 *         (see rewrite::utils::is_always_disequal()
 * result: false
 */
template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_FALSE>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (rewrite::utils::is_always_disequal(node[0], node[1]))
  {
    return NodeManager::get().mk_value(false);
  }
  return node;
}

/**
 * match:  (= (not a) (not b))
 * result: (= a b)
 *
 * match:  (= (bvnot a) (bvnot b))
 * result: (= a b)
 *
 * match:  (= (bvneg a) (bvneg b))
 * result: (= a b)
 *
 * match:  (= (fp.neg a) (fp.neg b))
 * result: (= a b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_INV>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  assert(node.num_children() == 2);
  if ((node[0].is_inverted() && node[1].is_inverted())
      || (node[0].kind() == Kind::BV_NEG && node[1].kind() == Kind::BV_NEG)
      || (node[0].kind() == Kind::FP_NEG && node[1].kind() == Kind::FP_NEG))
  {
    return rewriter.mk_node(Kind::EQUAL, {node[0][0], node[1][0]});
  }
  return node;
}

/**
 * match:  (= (ite x a b) (ite x c d))
 *         with either a = c or b = d
 * result: (ite x (= a c) (= b d))
 */
namespace {
Node
_rw_eq_ite(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0       = idx;
  size_t idx1       = 1 - idx;
  bool inverted0    = node[idx0].is_inverted();
  bool inverted1    = node[idx1].is_inverted();
  const Node& node0 = inverted0 ? node[idx0][0] : node[idx0];
  const Node& node1 = inverted1 ? node[idx1][0] : node[idx1];
  if (node0.kind() == Kind::ITE && node1.kind() == Kind::ITE
      && node0[0] == node1[0] && (node0[1] == node1[1] || node0[2] == node1[2]))
  {
    Node t = rewriter.mk_node(
        Kind::EQUAL,
        {inverted0 ? rewriter.invert_node(node0[1]) : node0[1],
         inverted1 ? rewriter.invert_node(node1[1]) : node1[1]});
    Node e = rewriter.mk_node(
        Kind::EQUAL,
        {inverted0 ? rewriter.invert_node(node0[2]) : node0[2],
         inverted1 ? rewriter.invert_node(node1[2]) : node1[2]});
    return rewriter.mk_node(Kind::ITE, {node0[0], t, e});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_ITE>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  Node res = _rw_eq_ite(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_ite(rewriter, node, 1);
  }
  return res;
}

/**
 * match: (= a (ite c a b))
 * result: (or c (= a b))
 *
 * match: (= a (ite c b a))
 * result: (or (not c) (= a b))
 */
namespace {
Node
_rw_eq_ite_same(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::ITE)
  {
    if (node[idx0][1] == node[idx1])
    {
      return rewriter.mk_node(
          Kind::OR,
          {node[idx0][0],
           rewriter.mk_node(Kind::EQUAL, {node[idx1], node[idx0][2]})});
    }
    if (node[idx0][2] == node[idx1])
    {
      return rewriter.mk_node(
          Kind::OR,
          {rewriter.invert_node(node[idx0][0]),
           rewriter.mk_node(Kind::EQUAL, {node[idx1], node[idx0][1]})});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_ITE_SAME>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  Node res = _rw_eq_ite_same(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_ite_same(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= a (not (ite c a b)))
 * result: (and (not c) (= a (not b)))
 *
 * match:  (= a (not (ite c b a)))
 * result: (and c (= a (not b)))
 *
 * match:  (= a (bvnot (ite c a b)))
 * result: (and (not c) (= a (bvnot b)))
 *
 * match:  (= a (bvnot (ite c b a)))
 * result: (and c (= a (bvnot b)))
 */
namespace {
Node
_rw_eq_ite_inverted(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_inverted() && node[idx0][0].kind() == Kind::ITE)
  {
    if (node[idx0][0][1] == node[idx1])
    {
      return rewriter.mk_node(
          Kind::AND,
          {rewriter.invert_node(node[idx0][0][0]),
           rewriter.mk_node(
               Kind::EQUAL,
               {node[idx1], rewriter.invert_node(node[idx0][0][2])})});
    }
    if (node[idx0][0][2] == node[idx1])
    {
      return rewriter.mk_node(
          Kind::AND,
          {node[idx0][0][0],
           rewriter.mk_node(
               Kind::EQUAL,
               {node[idx1], rewriter.invert_node(node[idx0][0][1])})});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_ITE_INVERTED>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  Node res = _rw_eq_ite_inverted(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_ite_inverted(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= d (ite c a b)) where a and d can be determined to be always
 *         disequal, (see rewrite::utils::is_always_disequal()
 * result: (and (not c) (= b d))
 *
 * match:  (= d (ite c a b)) where b and d can be determined to be always
 *         disequal, (see rewrite::utils::is_always_disequal()
 * result: (and c (= a d))
 */
namespace {
Node
_rw_eq_ite_dis_bv1(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::ITE && node[idx0].type().is_bool())
  {
    if (rewrite::utils::is_always_disequal(node[idx0][1], node[idx1]))
    {
      return rewriter.mk_node(
          Kind::AND,
          {rewriter.invert_node(node[idx0][0]),
           rewriter.mk_node(Kind::EQUAL, {node[idx0][2], node[idx1]})});
    }
    if (rewrite::utils::is_always_disequal(node[idx0][2], node[idx1]))
    {
      return rewriter.mk_node(
          Kind::AND,
          {node[idx0][0],
           rewriter.mk_node(Kind::EQUAL, {node[idx0][1], node[idx1]})});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_ITE_DIS_BV1>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  Node res = _rw_eq_ite_dis_bv1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_ite_dis_bv1(rewriter, node, 1);
  }
  return res;
}

/**
 * match: (= v (ite c v w)) with v and w being values
 * result: c
 *
 * match: (= v (ite c w v)) with v and w being values
 * result: !c
 */
namespace {
Node
_rw_eq_ite_lift_bv1(Rewriter& rewriter, const Node& node, size_t idx0)
{
  size_t idx1 = 1 - idx0;

  if (node[idx0].is_value() && node[idx1].kind() == Kind::ITE
      && node[idx1][1].is_value() && node[idx1][2].is_value())
  {
    // result: c
    if (node[idx0] == node[idx1][1])
    {
      return node[idx1][0];
    }
    // result: !c
    else if (node[idx0] == node[idx1][2])
    {
      return rewriter.mk_node(Kind::NOT, {node[idx1][0]});
    }
  }
  return node;
}
}

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_ITE_LIFT_COND>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  Node res = _rw_eq_ite_lift_bv1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_ite_lift_bv1(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvadd a (_ bvX N)) (_ bvY N))
 * result: (= a (bvsub (_ bvY N) (_ bvX N)))
 *
 * match:  (= (bvadd (_ bvX N) a) (_ bvY N))
 * result: (= a (bvsub (_ bvY N) (_ bvX N)))
 */
namespace {
Node
_rw_eq_const_bv_add(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_ADD && node[idx1].is_value())
  {
    if (node[idx0][0].is_value())
    {
      return rewriter.mk_node(
          Kind::EQUAL,
          {node[idx0][1],
           NodeManager::get().mk_value(node[idx1].value<BitVector>().bvsub(
               node[idx0][0].value<BitVector>()))});
    }
    if (node[idx0][1].is_value())
    {
      return rewriter.mk_node(
          Kind::EQUAL,
          {node[idx0][0],
           NodeManager::get().mk_value(node[idx1].value<BitVector>().bvsub(
               node[idx0][1].value<BitVector>()))});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_CONST_BV_ADD>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  Node res = _rw_eq_const_bv_add(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_const_bv_add(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvmul a (_ bvX N)) (_ bvY N)) if X is odd
 * result: (= a (bvmul (_ bvY N) inv)) with inv the mod inverse of X
 *
 * match:  (= (bvmul (_ bvX N) a) (_ bvY N)) if X is odd
 * result: (= a (bvmul (_ bvY N) inv)) with inv the mod inverse of X
 */
namespace {
Node
_rw_eq_const_bv_mul(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_MUL && node[idx1].is_value())
  {
    if (node[idx0][0].is_value())
    {
      const BitVector& val = node[idx0][0].value<BitVector>();
      if (val.lsb())
      {
        return rewriter.mk_node(
            Kind::EQUAL,
            {node[idx0][1],
             NodeManager::get().mk_value(
                 node[idx1].value<BitVector>().bvmul(val.bvmodinv()))});
      }
    }
    if (node[idx0][1].is_value())
    {
      const BitVector& val = node[idx0][1].value<BitVector>();
      if (val.lsb())
      {
        return rewriter.mk_node(
            Kind::EQUAL,
            {node[idx0][0],
             NodeManager::get().mk_value(
                 node[idx1].value<BitVector>().bvmul(val.bvmodinv()))});
      }
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_CONST_BV_MUL>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  Node res = _rw_eq_const_bv_mul(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_const_bv_mul(rewriter, node, 1);
  }
  return res;
}

namespace {

Node
_rw_eq_const_bv_not(Rewriter& rewriter, const Node& node, size_t idx)
{
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;

  if (node[idx0].is_value() && node[idx1].kind() == Kind::BV_NOT)
  {
    return rewriter.mk_node(
        Kind::EQUAL,
        {rewriter.mk_node(Kind::BV_NOT, {node[idx0]}), node[idx1][0]});
  }
  return node;
}

}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_CONST_BV_NOT>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  Node res = _rw_eq_const_bv_not(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_const_bv_not(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvadd a b) a)
 * result: (= b (_ bv0 N))
 *
 * Note: This rule will not lead to less variable substitutions since `a` cannot
 *       be substituted (the occurrence check will fail).
 */
namespace {
Node
_rw_eq_bv_add(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_ADD)
  {
    if (node[idx0][0] == node[idx1])
    {
      return rewriter.mk_node(Kind::EQUAL,
                              {node[idx0][1],
                               NodeManager::get().mk_value(BitVector::mk_zero(
                                   node[idx0].type().bv_size()))});
    }
    if (node[idx0][1] == node[idx1])
    {
      return rewriter.mk_node(Kind::EQUAL,
                              {node[idx0][0],
                               NodeManager::get().mk_value(BitVector::mk_zero(
                                   node[idx0].type().bv_size()))});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_BV_ADD>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_eq_bv_add(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_bv_add(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvadd a b) (bvadd a c))
 * result: (= b c)
 */
namespace {
Node
_rw_eq_add_add(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_ADD && node[idx1].kind() == Kind::BV_ADD)
  {
    if (node[idx0][0] == node[idx1][0])
    {
      return rewriter.mk_node(Kind::EQUAL, {node[idx0][1], node[idx1][1]});
    }
    if (node[idx0][0] == node[idx1][1])
    {
      return rewriter.mk_node(Kind::EQUAL, {node[idx0][1], node[idx1][0]});
    }
    if (node[idx0][1] == node[idx1][0])
    {
      return rewriter.mk_node(Kind::EQUAL, {node[idx0][0], node[idx1][1]});
    }
    if (node[idx0][1] == node[idx1][1])
    {
      return rewriter.mk_node(Kind::EQUAL, {node[idx0][0], node[idx1][0]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_BV_ADD_ADD>::_apply(Rewriter& rewriter,
                                                       const Node& node)
{
  Node res = _rw_eq_add_add(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_add_add(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvconcat a_[n] b) c_[m])
 * result: (and
 *           (=
 *             ((_ extract u l) (bvconcat a b))
 *             ((_ extract u l) c))
 *           (=
 *             ((_ extract (l - 1) 0) (bvconcat a b))
 *             ((_ extract (l - 1)  0) c))
 *         with u = m - 1
 *              l = m - n + 1
 */
namespace {
Node
_rw_eq_concat(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_CONCAT)
  {
    uint64_t m = node[idx1].type().bv_size();
    uint64_t u = m - 1;
    uint64_t l = m - node[idx0][0].type().bv_size();

    Node ext1_lhs = rewriter.mk_node(Kind::BV_EXTRACT, {node[idx1]}, {u, l});
    Node ext1_rhs =
        rewriter.mk_node(Kind::BV_EXTRACT, {node[idx1]}, {l - 1, 0});
    // Note: Introducing two extracts on node[idx1] is not necessarily
    //       beneficial. Hence, we only rewrite if an extract on node[idx1]
    //       is rewritten to a non-extract.

    if (ext1_lhs.kind() != Kind::BV_EXTRACT
        || ext1_rhs.kind() != Kind::BV_EXTRACT)
    {
      Node lhs = rewriter.mk_node(
          Kind::EQUAL,
          {rewriter.mk_node(Kind::BV_EXTRACT, {node[idx0]}, {u, l}), ext1_lhs});
      Node rhs = rewriter.mk_node(
          Kind::EQUAL,
          {rewriter.mk_node(Kind::BV_EXTRACT, {node[idx0]}, {l - 1, 0}),
           ext1_rhs});
      return rewriter.mk_node(Kind::AND, {lhs, rhs});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_BV_CONCAT>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  Node res = _rw_eq_concat(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_concat(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (= (bvsub a b) c)
 * result: (= (bvadd b c) a)
 */
namespace {
Node
_rw_eq_bv_sub(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  Node child0, child1;
  if (rewriter.is_bv_sub(node[idx0], child0, child1))
  {
    return rewriter.mk_node(
        Kind::EQUAL,
        {child0, rewriter.mk_node(Kind::BV_ADD, {child1, node[idx1]})});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_BV_SUB>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_eq_bv_sub(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_bv_sub(rewriter, node, 1);
  }
  return res;
}

/* distinct ----------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::DISTINCT_CARD>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  (void) rewriter;
  uint64_t num_children = node.num_children();
  if (num_children > 2)
  {
    const Type& type = node[0].type();
    if ((type.is_bv() && std::log2(num_children) > type.bv_size())
        || (type.is_fp()
            && std::log2(num_children)
                   > (type.fp_exp_size() + type.fp_sig_size())))
    {
      return NodeManager::get().mk_value(false);
    }
  }
  return node;
}

/* distinct ----------------------------------------------------------------- */

/**
 * Constant folding, matches when condition operands is value.
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_EVAL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 3);

  if (node[0].is_value())
  {
    if (node[0].value<bool>())
    {
      return node[1];
    }
    return node[2];
  }
  return node;
}

/**
 * match:  (ite c a a)
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_SAME>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 3);

  if (node[1] == node[2])
  {
    return node[1];
  }
  return node;
}

/**
 * match:  (ite cond (ite cond a b) c)
 * result: (ite cond a c)
 *
 * match:  (ite cond (not (ite cond a b)) c)
 * result: (ite cond (not) a c)
 *
 * match:  (ite cond (bvnot (ite cond a b)) c)
 * result: (ite cond (bvnot) a c)
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_THEN_ITE1>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted     = node[1].is_inverted();
  const Node& node1 = inverted ? node[1][0] : node[1];
  if (node1.kind() == Kind::ITE && node1[0] == node[0])
  {
    return rewriter.mk_node(
        Kind::ITE,
        {node[0],
         inverted ? rewriter.invert_node(node1[1]) : node1[1],
         node[2]});
  }
  return node;
}

/**
 * match:  (ite cond0 (ite cond1 a b) a)
 * result: (ite (and cond0 (not cond1)) b a)
 *
 * match:  (ite cond0 (not (ite cond1 (not a) b)) a)
 * result: (ite (and cond0 (not cond1)) (not b) a)
 *
 * match:  (ite cond0 (bvnot (ite cond1 (bvnot a) b)) a)
 * result: (ite (and cond0 (not cond1)) (bvnot b) a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_THEN_ITE2>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted     = node[1].is_inverted();
  const Node& node1 = inverted ? node[1][0] : node[1];
  if (node1.kind() == Kind::ITE)
  {
    if (inverted && rewrite::utils::is_inverted_of(node1[1], node[2]))
    {
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(Kind::AND,
                            {node[0], rewriter.invert_node(node1[0])}),
           rewriter.invert_node(node1[2]),
           node[2]});
    }
    else if (!inverted && node1[1] == node[2])
    {
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(Kind::AND,
                            {node[0], rewriter.invert_node(node1[0])}),
           node1[2],
           node[2]});
    }
  }
  return node;
}

/**
 * match:  (ite cond0 (ite cond1 b a) a)
 * result: (ite (and cond0 cond1) b a)
 *
 * match:  (ite cond0 (not (ite cond1 b (not a)) a)
 * result: (ite (and cond0 cond1) (not b) a)
 *
 * match:  (ite cond0 (bvnot (ite cond1 b (bvnot a)) a)
 * result: (ite (and cond0 cond1) (bvnot b) a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_THEN_ITE3>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted     = node[1].is_inverted();
  const Node& node1 = inverted ? node[1][0] : node[1];
  if (node1.kind() == Kind::ITE)
  {
    if (inverted && rewrite::utils::is_inverted_of(node1[2], node[2]))
    {
      return rewriter.mk_node(Kind::ITE,
                              {rewriter.mk_node(Kind::AND, {node[0], node1[0]}),
                               rewriter.invert_node(node1[1]),
                               node[2]});
    }
    else if (!inverted && node1[2] == node[2])
    {
      return rewriter.mk_node(Kind::ITE,
                              {rewriter.mk_node(Kind::AND, {node[0], node1[0]}),
                               node1[1],
                               node[2]});
    }
  }
  return node;
}

/**
 * match:  (ite cond a (ite cond b c))
 * result: (ite cond a c)
 *
 * match:  (ite cond a (not (ite cond b c)))
 * result: (ite cond a (not c))
 *
 * match:  (ite cond a (bvnot (ite cond b c)))
 * result: (ite cond a (bvnot c))
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_ELSE_ITE1>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted     = node[2].is_inverted();
  const Node& node2 = inverted ? node[2][0] : node[2];
  if (node2.kind() == Kind::ITE && node[0] == node2[0])
  {
    return rewriter.mk_node(
        Kind::ITE,
        {node[0],
         node[1],
         inverted ? rewriter.invert_node(node2[2]) : node2[2]});
  }
  return node;
}

/**
 * match:  (ite cond0 a (ite cond1 a b))
 * result: (ite (and (not cond0) (not cond1)) b a)
 *
 * match:  (ite cond0 a (not (ite cond1 (not a) b)))
 * result: (ite (and (not cond0) (not cond1)) (not b) a)
 *
 * match:  (ite cond0 a (bvnot (ite cond1 (bvnot a) b)))
 * result: (ite (and (not cond0) (not cond1)) (bvnot b) a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_ELSE_ITE2>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted     = node[2].is_inverted();
  const Node& node2 = inverted ? node[2][0] : node[2];
  if (node2.kind() == Kind::ITE)
  {
    if (inverted && rewrite::utils::is_inverted_of(node2[1], node[1]))
    {
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(
               Kind::AND,
               {rewriter.invert_node(node[0]), rewriter.invert_node(node2[0])}),
           rewriter.invert_node(node2[2]),
           node[1]});
    }
    else if (!inverted && node2[1] == node[1])
    {
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(
               Kind::AND,
               {rewriter.invert_node(node[0]), rewriter.invert_node(node2[0])}),
           node2[2],
           node[1]});
    }
  }
  return node;
}

/**
 * match:  (ite cond0 a (ite cond1 b a))
 * result: (ite (and (not cond0) cond1) b a)
 *
 * match:  (ite cond0 a (not (ite cond1 b (not a)))
 * result: (ite (and (not cond0) cond1) (not b) a)
 *
 * match:  (ite cond0 a (bvnot (ite cond1 b (bvnot a)))
 * result: (ite (and (not cond0) cond1) (bvnot b) a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_ELSE_ITE3>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted     = node[2].is_inverted();
  const Node& node2 = inverted ? node[2][0] : node[2];
  if (node2.kind() == Kind::ITE)
  {
    if (inverted && rewrite::utils::is_inverted_of(node2[2], node[1]))
    {
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(Kind::AND,
                            {rewriter.invert_node(node[0]), node2[0]}),
           rewriter.invert_node(node2[1]),
           node[1]});
    }
    else if (!inverted && node2[2] == node[1])
    {
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(Kind::AND,
                            {rewriter.invert_node(node[0]), node2[0]}),
           node2[1],
           node[1]});
    }
  }
  return node;
}

/**
 * match:  (ite c a b) with a and b of bit-width 1
 * result: (and (or (not c a) (or c b)))
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_BOOL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  assert(node.num_children() == 3);
  if (node[1].type().is_bool())
  {
    return rewriter.mk_node(
        Kind::AND,
        {rewriter.mk_node(Kind::OR, {rewriter.invert_node(node[0]), node[1]}),
         rewriter.mk_node(Kind::OR, {node[0], node[2]})});
  }
  return node;
}

/**
 * match:  (ite c (concat a b) (concat a d))
 * result: (concat a (ite c b d))
 *
 * match:  (ite c (bvnot (concat a b)) (concat (bvnot a) d))
 * result: (concat (bvnot a) (ite c (bvnot b) d))
 *
 * match:  (ite c (concat (bvnot a) b) (bvnot (concat a d)))
 * result: (concat (bvnot a) (ite c b (bvnot d)))
 *
 * match:  (ite c (bvnot (concat a b)) (bvnot (concat a d)))
 * result: (concat (bvnot a) (ite c (bvnot b) (bvnot d)))
 *
 * match:  (ite c (concat a b) (concat d b))
 * result: (concat (ite c a d) b)
 *
 * match:  (ite c (bvnot (concat a b)) (concat d b))
 * result: (concat (ite c (bvnot a) d) (bvnot b))
 *
 * match:  (ite c (concat a b) (bvnot (concat d b)))
 * result: (concat (ite c a (bvnot (d)) (bvnot b))
 *
 * match:  (ite c (bvnot (concat a b)) (bvnot (concat d b)))
 * result: (concat (ite c (bvnot a) (bvnot d)) (bvnot b))
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_BV_CONCAT>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 3);
  bool inverted1    = node[1].is_inverted();
  bool inverted2    = node[2].is_inverted();
  const Node& node1 = inverted1 ? node[1][0] : node[1];
  const Node& node2 = inverted2 ? node[2][0] : node[2];
  if (node1.kind() == Kind::BV_CONCAT && node2.kind() == Kind::BV_CONCAT)
  {
    if ((inverted1 == inverted2
         && (node1[0] == node2[0] || node1[1] == node2[1]))
        || (inverted1 != inverted2
            && (rewrite::utils::is_inverted_of(node1[0], node2[0])
                || rewrite::utils::is_inverted_of(node1[1], node2[1]))))
    {
      return rewriter.mk_node(
          Kind::BV_CONCAT,
          {rewriter.mk_node(
               Kind::ITE,
               {
                   node[0],
                   inverted1 ? rewriter.invert_node(node1[0]) : node1[0],
                   inverted2 ? rewriter.invert_node(node2[0]) : node2[0],
               }),
           rewriter.mk_node(
               Kind::ITE,
               {
                   node[0],
                   inverted1 ? rewriter.invert_node(node1[1]) : node1[1],
                   inverted2 ? rewriter.invert_node(node2[1]) : node2[1],

               })});
    }
  }
  return node;
}

/**
 * match:  (ite c (<op> a b) (<op> a d)
 *         with <op> in {bvadd, bvand, bvmul, bvudiv, bvurem}
 * result: (<op> a (ite c b d))
 *
 * match:  (ite c (<op> a b) (<op> d b)
 *         with <op> in {bvadd, bvand, bvmul, bvudiv, bvurem}
 * result: (<op> (ite c a d) b)
 *
 * match:  (ite c (<op> a b) (<op> d a)
 *         with <op> in {bvadd, bvand, bvmul}
 * result: (<op> a (ite c b d))
 *
 * match:  (ite c (<op> a b) (<op> b d)
 *         with <op> in {bvadd, bvand, bvmul}
 * result: (<op> (ite c a d) b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::ITE_BV_OP>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  assert(node.num_children() == 3);
  Kind kind = node[1].kind();
  if (kind == node[2].kind()
      && (kind == Kind::BV_ADD || kind == Kind::BV_AND || kind == Kind::BV_MUL
          || kind == Kind::BV_UDIV || kind == Kind::BV_UREM))
  {
    if (node[1][0] == node[2][0])
    {
      return rewriter.mk_node(
          kind,
          {node[1][0],
           rewriter.mk_node(Kind::ITE, {node[0], node[1][1], node[2][1]})});
    }
    if (node[1][1] == node[2][1])
    {
      return rewriter.mk_node(
          kind,
          {rewriter.mk_node(Kind::ITE, {node[0], node[1][0], node[2][0]}),
           node[1][1]});
    }
    if (kind != Kind::BV_UDIV && kind != Kind::BV_UREM
        && node[1][0] == node[2][1])
    {
      return rewriter.mk_node(
          kind,
          {node[1][0],
           rewriter.mk_node(Kind::ITE, {node[0], node[1][1], node[2][0]})});
    }
    if (kind != Kind::BV_UDIV && kind != Kind::BV_UREM
        && node[1][1] == node[2][0])
    {
      return rewriter.mk_node(
          kind,
          {rewriter.mk_node(Kind::ITE, {node[0], node[1][0], node[2][1]}),
           node[1][1]});
    }
  }
  return node;
}

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::DISTINCT_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  uint64_t num_children = node.num_children();
  if (num_children == 2)
  {
    return rewriter.invert_node(
        rewriter.mk_node(Kind::EQUAL, {node[0], node[1]}));
  }

  Node res;
  for (size_t i = 0; i < num_children; ++i)
  {
    for (size_t j = i + 1; j < num_children; ++j)
    {
      Node tmp = rewriter.invert_node(
          rewriter.mk_node(Kind::EQUAL, {node[i], node[j]}));
      if (res.is_null())
      {
        res = tmp;
      }
      else
      {
        res = rewriter.mk_node(Kind::AND, {res, tmp});
      }
    }
  }
  assert(!res.is_null());
  return res;
}

/* --- Commutative Operator Normalization ----------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::NORMALIZE_COMM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  Kind k = node.kind();
  // Note: We do not use rewriter.mk_node() here since rewriting will happen
  // after normalization.
  if (KindInfo::is_commutative(k))
  {
    if (node.num_children() == 2)
    {
      if (node[0].id() > node[1].id())
      {
        return NodeManager::get().mk_node(k, {node[1], node[0]});
      }
    }
  }
  else if (k == Kind::FP_ADD || k == Kind::FP_MUL)
  {
    if (node[1].id() > node[2].id())
    {
      return NodeManager::get().mk_node(k, {node[0], node[2], node[1]});
    }
  }
  else if (k == Kind::FP_FMA)
  {
    if (node[1].id() > node[2].id())
    {
      return NodeManager::get().mk_node(node.kind(),
                                        {node[0], node[2], node[1], node[3]});
    }
  }
  return node;
}

/* --- Quantifiers ---------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::EXISTS_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  assert(node[1].kind() != Kind::EXISTS);
  return rewriter.mk_node(
      Kind::NOT,
      {rewriter.mk_node(Kind::FORALL,
                        {node[0], rewriter.mk_node(Kind::NOT, {node[1]})})});
}

}  // namespace bzla
