#include "rewrite/rewrites_bv.h"

#include <iostream>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
namespace bzla {

using namespace node;

/* bvadd -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvadd(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvadd (_ bv0 N) a) or (bvadd a (_ bv0 N))
 * result: a
 */
namespace {
Node
_rw_bv_add_special_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && !node[idx1].is_value())
  {
    if (node[idx0].value<BitVector>().is_zero())
    {
      return node[idx1];
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  Node res = _rw_bv_add_special_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_special_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd (_ bvX N) (bvadd (_ bvY N) a))
 * result: (bvadd (_ bvZ N) a) with Z = X + Y
 */
namespace {
Node
_rw_bv_add_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && node[idx1].kind() == Kind::BV_ADD)
  {
    assert(node[idx1].num_children() == 2);
    if (node[idx1][0].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_ADD,
          {rewriter.mk_node(Kind::BV_ADD, {node[idx0], node[idx1][0]}),
           node[idx1][1]});
    }
    else if (node[idx1][1].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_ADD,
          {rewriter.mk_node(Kind::BV_ADD, {node[idx0], node[idx1][1]}),
           node[idx1][0]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_CONST>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_bv_add_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd a b) with a and b of bit-width 1
 * result: (bvxor a b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_BV1>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].type().bv_size() != 1) return node;
  return rewriter.mk_node(Kind::BV_XOR, {node[0], node[1]});
}

/**
 * match:  (bvadd a a)
 * result: (bvshl a (_ bv1 N))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_SAME>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0] != node[1]) return node;
  return rewriter.mk_node(Kind::BV_SHL,
                          {node[0],
                           NodeManager::get().mk_value(
                               BitVector::mk_one(node[0].type().bv_size()))});
}

/**
 * match:  (bvadd a (bvmul a b))
 * result: (bvmul a (bvadd b (_ bv1 N)))
 */
namespace {
Node
_rw_bv_add_mul(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx1].kind() == Kind::BV_MUL)
  {
    if (node[idx1][0] == node[idx0])
    {
      return rewriter.mk_node(
          Kind::BV_MUL,
          {node[idx0],
           rewriter.mk_node(Kind::BV_ADD,
                            {node[idx1][1],
                             NodeManager::get().mk_value(
                                 BitVector::mk_one(node.type().bv_size()))})});
    }
    if (node[idx1][1] == node[idx0])
    {
      return rewriter.mk_node(
          Kind::BV_MUL,
          {node[idx0],
           rewriter.mk_node(Kind::BV_ADD,
                            {node[idx1][0],
                             NodeManager::get().mk_value(
                                 BitVector::mk_one(node.type().bv_size()))})});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_MUL>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_add_mul(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_mul(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd a (bvnot a))
 * result: (bvnot (_ bv0 N))
 */
namespace {
Node
_rw_bv_add_not(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx1].kind() == Kind::BV_NOT && node[idx0] == node[idx1][0])
  {
    return NodeManager::get().mk_value(
        BitVector::mk_ones(node[0].type().bv_size()));
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_NOT>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_add_not(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_not(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd a (bvneg a)) or (bvadd (bvneg a) a)
 * result: 0
 */
namespace {
Node
_rw_bv_add_neg(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  Node neg0;
  if (node::utils::is_bv_neg(node[idx1], neg0))
  {
    if (node[idx0] == neg0)
    {
      return NodeManager::get().mk_value(
          BitVector::mk_zero(node[0].type().bv_size()));
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_NEG>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_add_neg(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_neg(rewriter, node, 1);
  }
  return res;
}

/**
 * We have for a / b that a = n * b + r (a - n * b = r), and thus for
 * a - ((a / b) * b) = a % b with (a / b) = n .
 * match:  (bvadd a (bvneg (bvmul (bvudiv a b) b)))
 *         (bvadd a (bvmul (bvneg (bvudiv a b)) b)))
 *         (bvadd a (bvmul (bvudiv a b)) (bvneg b))))
 * result: (bvurem a b)
 */
namespace {
Node
_rw_bv_add_urem(Rewriter& rewriter, const Node& node, size_t idx)
{
  size_t idx0      = idx;
  size_t idx1      = 1 - idx;
  const Node *udiv = nullptr, *b = nullptr;
  const Node& a = node[idx1];
  // (bvadd a (bvneg (bvmul (bvudiv a b) b)))
  Node neg0;
  if (node::utils::is_bv_neg(node[idx0], neg0))
  {
    const Node& mul = neg0;
    if (mul.kind() == Kind::BV_MUL)
    {
      if (mul[0].kind() == Kind::BV_UDIV)
      {
        udiv = &mul[0];
        b    = &mul[1];
      }
      if (mul[1].kind() == Kind::BV_UDIV)
      {
        udiv = &mul[1];
        b    = &mul[0];
      }
    }
  }
  // (bvadd a (bvmul (bvneg (bvudiv a b)) b)))
  // (bvadd a (bvmul (bvudiv a b)) (bvneg b))))
  else if (node[idx0].kind() == Kind::BV_MUL)
  {
    const Node& mul = node[idx0];
    if (node::utils::is_bv_neg(mul[0], neg0) && neg0.kind() == Kind::BV_UDIV)
    {
      udiv = &neg0;
      b    = &mul[1];
    }
    else if (node::utils::is_bv_neg(mul[1], neg0)
             && neg0.kind() == Kind::BV_UDIV)
    {
      udiv = &neg0;
      b    = &mul[0];
    }
    else if (mul[0].kind() == Kind::BV_UDIV
             && node::utils::is_bv_neg(mul[1], neg0))
    {
      udiv = &mul[0];
      b    = &neg0;
    }
    else if (mul[1].kind() == Kind::BV_UDIV
             && node::utils::is_bv_neg(mul[0], neg0))
    {
      udiv = &mul[1];
      b    = &neg0;
    }
  }
  if (udiv && b && (*udiv)[0] == a && (*udiv)[1] == *b)
  {
    return rewriter.mk_node(Kind::BV_UREM, {a, *b});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_UREM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_bv_add_urem(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_urem(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd a (ite c 0 e)) or (bvadd a (ite c t 0))
 * result: (ite c a (bvadd e a)) or (ite c (bvadd t a) a)
 */
namespace {
Node
_rw_bv_add_ite(Rewriter& rewriter, const Node& node, size_t idx)
{
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::ITE
      && ((node[idx0][1].is_value()
           && node[idx0][1].value<BitVector>().is_zero())
          || (node[idx0][2].is_value()
              && node[idx0][2].value<BitVector>().is_zero())))
  {
    return rewriter.mk_node(
        Kind::ITE,
        {node[idx0][0],
         rewriter.mk_node(Kind::BV_ADD, {node[idx0][1], node[idx1]}),
         rewriter.mk_node(Kind::BV_ADD, {node[idx0][2], node[idx1]})});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_ITE>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_add_ite(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_ite(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd a (bvshl b a))
 * result: (bvor a (bvshl b a))
 */
namespace {
Node
_rw_bv_add_shl(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx1].kind() == Kind::BV_SHL && node[idx1][1] == node[idx0])
  {
    return rewriter.mk_node(Kind::BV_OR, {node[idx0], node[idx1]});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_SHL>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_add_shl(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_shl(rewriter, node, 1);
  }
  return res;
}

/* bvand -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_AND_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvand(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvand (_ bv0 N) a) or (bvand a (_ bv0 N))
 * result: (_ bv0 N)
 *
 * match:  (bvand (bvnot (_ bv0 N)) a) or (bvand a (bvnot (_ bv0 N)))
 * result: a
 */
namespace {
Node
_rw_bv_and_special_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  size_t idx0             = idx;
  size_t idx1             = 1 - idx;
  if (node[idx0].is_value() && !node[idx1].is_value())
  {
    const BitVector& value0 = node[idx0].value<BitVector>();
    if (value0.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
    }
    if (value0.is_ones())
    {
      return node[idx1];
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_AND_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  Node res = _rw_bv_and_special_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_and_special_const(rewriter, node, 1);
  }
  return res;
}

/* bvashr ------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ASHR_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvashr(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvashr (_ bv0 N) a)
 * result: (_ bv0 N)
 *
 * match:  (bvashr a (_ bv0 N))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ASHR_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_zero())
    {
      return node[0];
    }
  }
  return node;
}

/* bvconcat ----------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_CONCAT_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvconcat(node[1].value<BitVector>()));
  return res;
}

/**
 * match:  (bvconcat (bvconcat a (_ bvX n)) (_ bvY m))
 * result: (bvconcat a (_ bvZ n+m)) with bvZ = (bvconcat (_ bvX n) (_ bvY m))
 *
 * match:  (bvconcat (_ bvX m) (bvconcat (_ bvY n) a))
 * result: (bvconcat (_ bvZ n+m) a) with bvZ = (bvconcat (_ bvX n) (_ bvY m))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_CONCAT_CONST>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].kind() == Kind::BV_CONCAT && node[0][1].is_value()
      && node[1].is_value())
  {
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {node[0][0], rewriter.mk_node(Kind::BV_CONCAT, {node[0][1], node[1]})});
  }
  else if (node[1].kind() == Kind::BV_CONCAT && node[1][0].is_value()
           && node[0].is_value())
  {
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(Kind::BV_CONCAT, {node[0], node[1][0]}), node[1][1]});
  }
  return node;
}

/**
 * match:  (bvconcat ((_ extract h1 l1) a) ((_ extract h2 l2) a))
 *         with l1 = h2 + 1
 * result: ((_ extract h1 l2) a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_CONCAT_EXTRACT>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.num_children() == 2);
  bool inverted     = false;
  const Node *node0 = &node[0], *node1 = &node[1];
  if (node0->kind() == Kind::BV_NOT && node1->kind() == Kind::BV_NOT)
  {
    inverted = true;
    node0    = &node[0][0];
    node1    = &node[1][0];
  }
  if (node0->kind() == Kind::BV_EXTRACT && node1->kind() == Kind::BV_EXTRACT
      && (*node0)[0] == (*node1)[0] && node0->index(1) == node1->index(0) + 1)
  {
    Node res = rewriter.mk_node(
        Kind::BV_EXTRACT, {(*node0)[0]}, {node0->index(0), node1->index(1)});
    return inverted ? rewriter.mk_node(Kind::BV_NOT, {res}) : res;
  }
  return node;
}

/**
 * match:  (bvconcat (bvand a b) c)
 * result: (bvand (bvconcat a c) (bvconcat b c))
 *
 * match:  (bvconcat a (bvand b c))
 * result: (bvand (bvconcat a b) (bvconcat a c))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_CONCAT_AND>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].kind() == Kind::BV_AND)
  {
    return rewriter.mk_node(
        Kind::BV_AND,
        {rewriter.mk_node(Kind::BV_CONCAT, {node[0][0], node[1]}),
         rewriter.mk_node(Kind::BV_CONCAT, {node[0][1], node[1]})});
  }
  else if (node[1].kind() == Kind::BV_AND)
  {
    return rewriter.mk_node(
        Kind::BV_AND,
        {rewriter.mk_node(Kind::BV_CONCAT, {node[0], node[1][0]}),
         rewriter.mk_node(Kind::BV_CONCAT, {node[0], node[1][1]})});
  }
  return node;
}

/* bvmul -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvmul(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvmul (_ bv0 N) a) or (bvmul a (_ bv0 N))
 * result: (_ bv0 N)
 *
 * match:  (bvmul (bvnot (_ bv0 N)) a) or (bvmul a (bvnot (_ bv0 N)))
 * result: (bvneg a)
 */
namespace {
Node
_rw_bv_mul_special_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0             = idx;
  size_t idx1             = 1 - idx;
  if (node[idx0].is_value() && !node[idx1].is_value())
  {
    const BitVector& value0 = node[idx0].value<BitVector>();
    if (value0.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
    }
    if (value0.is_one())
    {
      return node[idx1];
    }
    if (value0.is_ones())
    {
      return rewriter.mk_node(Kind::BV_NEG, {node[idx1]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  Node res = _rw_bv_mul_special_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_mul_special_const(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvadd a b) with a and b of bit-width 1
 * result: (bvand a b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_BV1>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].type().bv_size() != 1) return node;
  return rewriter.mk_node(Kind::BV_AND, {node[0], node[1]});
}

/**
 * match:  (bvmul (_ bvX N) (bvmul (_ bvY N) a))
 * result: (bvmul (_ bvZ N) a) with Z = X * Y
 */
namespace {
Node
_rw_bv_mul_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && node[idx1].kind() == Kind::BV_MUL)
  {
    assert(node[idx1].num_children() == 2);
    if (node[idx1][0].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_MUL,
          {rewriter.mk_node(Kind::BV_MUL, {node[idx0], node[idx1][0]}),
           node[idx1][1]});
    }
    else if (node[idx1][1].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_MUL,
          {rewriter.mk_node(Kind::BV_MUL, {node[idx0], node[idx1][1]}),
           node[idx1][0]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_CONST>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_bv_mul_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_mul_const(rewriter, node, 1);
  }
  return res;
}

/*
 * match:  (bvmul (_ bvX N) (bvadd a (_ bvY N))
 * result: (bvadd (bvmul (_ bvX N) a) (_ bvZ N)) with Z = X * Y
 */
namespace {
Node
_rw_bv_mul_const_add(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_value() && node[idx1].kind() == Kind::BV_ADD)
  {
    assert(node[idx1].num_children() == 2);
    if (node[idx1][0].is_value() || node[idx1][1].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_ADD,
          {rewriter.mk_node(Kind::BV_MUL, {node[idx0], node[idx1][0]}),
           rewriter.mk_node(Kind::BV_MUL, {node[idx0], node[idx1][1]})});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_CONST_ADD>::_apply(Rewriter& rewriter,
                                                       const Node& node)
{
  Node res = _rw_bv_mul_const_add(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_mul_const_add(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvmul a (ite c 0 e)) or (bvmul a (ite c t 0))
 * result: (ite c a (bvmul e a)) or (ite c (bvmul t a) a)
 */
namespace {
Node
_rw_bv_mul_ite(Rewriter& rewriter, const Node& node, size_t idx)
{
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::ITE
      && ((node[idx0][1].is_value()
           && node[idx0][1].value<BitVector>().is_zero())
          || (node[idx0][2].is_value()
              && node[idx0][2].value<BitVector>().is_zero())))
  {
    return rewriter.mk_node(
        Kind::ITE,
        {node[idx0][0],
         rewriter.mk_node(Kind::BV_MUL, {node[idx0][1], node[idx1]}),
         rewriter.mk_node(Kind::BV_MUL, {node[idx0][2], node[idx1]})});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_ITE>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_mul_ite(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_mul_ite(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvmul (bvshl a b) c)
 * result: (bvshl (bvmul a c) b)
 */
namespace {
Node
_rw_bv_mul_shl(Rewriter& rewriter, const Node& node, size_t idx)
{
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  assert(node.num_children() == 2);
  if (node[idx0].kind() == Kind::BV_SHL)
  {
    return rewriter.mk_node(
        Kind::BV_SHL,
        {rewriter.mk_node(Kind::BV_MUL, {node[idx0][0], node[idx1]}),
         node[idx0][1]});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_SHL>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  Node res = _rw_bv_mul_shl(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_mul_shl(rewriter, node, 1);
  }
  return res;
}

/**
 * match:  (bvmul (bvneg a) b)
 * result: (bvneg (bvmul a b))
 *
 * match:  (bvmul (bvneg a) (bvneg b))
 * resutl: (bvmul a b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_NEG>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 2);
  Node neg0, neg1;
  if (node::utils::is_bv_neg(node[0], neg0))
  {
    if (node::utils::is_bv_neg(node[1], neg1))
    {
      return rewriter.mk_node(Kind::BV_MUL, {neg0, neg1});
    }
    return rewriter.mk_node(Kind::BV_NEG,
                            {rewriter.mk_node(Kind::BV_MUL, {neg0, node[1]})});
  }
  else if (node::utils::is_bv_neg(node[1], neg1))
  {
    return rewriter.mk_node(Kind::BV_NEG,
                            {rewriter.mk_node(Kind::BV_MUL, {node[0], neg1})});
  }
  return node;
}

/**
 * match:  (bvmul (bvnot (_ bv0 N) a))
 * result: (bvneg a)
 */
namespace {
Node
_rw_bv_mul_ones(Rewriter& rewriter, const Node& node, size_t idx)
{
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  assert(node.num_children() == 2);
  if (node[idx0].is_value() && node[idx0].value<BitVector>().is_ones())
  {
    return rewriter.mk_node(Kind::BV_NEG, {node[idx1]});
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_ONES>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  Node res = _rw_bv_mul_ones(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_mul_ones(rewriter, node, 1);
  }
  return res;
}

/* bvnot -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_NOT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value()) return node;
  return NodeManager::get().mk_value(node[0].value<BitVector>().bvnot());
}

/**
 * match:  (bvnot (bvnot a))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_NOT_BV_NOT>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  (void) rewriter;
  if (node[0].kind() != Kind::BV_NOT) return node;
  return node[0][0];
}

/* bvshl -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvshl(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvshl (_ bv0 N) a)
 * result: (_ bv0 N)
 *
 * match:  (bvshl a (_ bv0 N))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHL_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_zero())
    {
      return node[0];
    }
  }
  return node;
}

/**
 * match:  (bvshl a (_ bvX N)) with X >= N
 * result: (_ bv0 N)
 *
 * match:  (bvshl a (_ bvX N)) with N <= 64
 * result: (bvconcat ((_ extract (N - X - 1) 0) a) (_ bv0 X))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHL_CONST>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  assert(node.num_children() == 2);
  if (node[1].is_value())
  {
    const BitVector& shift = node[1].value<BitVector>();
    uint64_t size          = shift.size();
    BitVector bv_size      = BitVector::from_ui(size, size);
    if (shift.compare(bv_size) >= 0)
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(size));
    }
    if (size <= 64)
    {
      uint64_t uishift = shift.to_uint64();
      return rewriter.mk_node(
          Kind::BV_CONCAT,
          {rewriter.mk_node(
               Kind::BV_EXTRACT, {node[0]}, {size - uishift - 1, 0}),
           NodeManager::get().mk_value(BitVector::mk_zero(uishift))});
    }
  }
  return node;
}

/* bvshr -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvshr(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvlshr (_ bv0 N) a)
 * result: (_ bv0 N)
 *
 * match:  (bvlshr a (_ bv0 N))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_zero())
    {
      return node[0];
    }
  }
  return node;
}

/**
 * match:  (bvshr a (_ bvX N)) with X >= N
 * result: (_ bv0 N)
 *
 * match:  (bvshr a (_ bvX N)) with N <= 64
 * result: (bvconcat (_ bv0 X) ((_ extract (N - 1) X) a))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_CONST>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  assert(node.num_children() == 2);
  if (node[1].is_value())
  {
    const BitVector& shift = node[1].value<BitVector>();
    uint64_t size          = shift.size();
    BitVector bv_size      = BitVector::from_ui(size, size);
    if (shift.compare(bv_size) >= 0)
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(size));
    }
    if (size <= 64)
    {
      uint64_t uishift = shift.to_uint64();
      return rewriter.mk_node(
          Kind::BV_CONCAT,
          {NodeManager::get().mk_value(BitVector::mk_zero(uishift)),
           rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, uishift})});
    }
  }
  return node;
}

/**
 * match:  (bvshr a a)
 * result: (_ bv0 N)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_SAME>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] == node[1])
  {
    return NodeManager::get().mk_value(
        BitVector::mk_zero(node.type().bv_size()));
  }
  return node;
}

/**
 * match:  (bvshr (bvnot a) a)
 * result: (bvshr (bvnot (_ bv0 N)) a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_NOT>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].kind() == Kind::BV_NOT && node[0][0] == node[1])
  {
    return rewriter.mk_node(
        Kind::BV_SHR,
        {NodeManager::get().mk_value(BitVector::mk_ones(node.type().bv_size())),
         node[1]});
  }
  return node;
}

/* bvslt -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SLT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().signed_compare(node[1].value<BitVector>())
      < 0);
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvslt (_ bv01..1 N) a)
 * result: false
 *
 * match:  (bvslt (_ bv10..0 N) a)
 * result: (distinct (_ bv10..0 N) a)
 *
 * match:  (bvslt a (_ bv01..1 N))
 * result: (distinct a (_ bv01..1 N))
 *
 * match:  (bvslt a (_ bv10..0 N))
 * result: false
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_SLT_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_max_signed())
    {
      // max_signed < node[1]  --->  false
      return NodeManager::get().mk_value(false);
    }
    if (value0.is_min_signed())
    {
      // min_signed < node[1]  --->  node[1] != min_signed
      return rewriter.mk_node(
          Kind::NOT, {rewriter.mk_node(Kind::EQUAL, {node[0], node[1]})});
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_max_signed())
    {
      // node[0] < max_signed --->  node[0] != node[1]
      return rewriter.mk_node(
          Kind::NOT, {rewriter.mk_node(Kind::EQUAL, {node[0], node[1]})});
    }
    if (value1.is_min_signed())
    {
      // node[0] < min_signed  --->  false
      return NodeManager::get().mk_value(false);
    }
  }
  return node;
}

/* bvudiv ------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvudiv(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvudiv (_ bv0 N) a)
 * result: (ite (= a (_ bv0 N)) (not (_ bv0 N)) (_ bv0 N))
 *
 * match:  (bvudiv a (_ bv0 N))
 * result: (not (_ bv0 N))
 *
 * match:  (bvudiv a (_ bv1 N))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_zero())
    {
      Node zero =
          NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
      Node ones =
          NodeManager::get().mk_value(BitVector::mk_ones(value0.size()));
      return rewriter.mk_node(
          Kind::ITE,
          {rewriter.mk_node(Kind::EQUAL, {node[1], zero}), ones, zero});
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_ones(value1.size()));
    }
    if (value1.is_one())
    {
      return node[0];
    }
  }
  return node;
}

/**
 * match:  (bvudiv a b) with a and b of bit-width 1
 * result: (bvnot (bvand (bvnot a) b))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_BV1>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].type().bv_size() != 1) return node;
  return rewriter.mk_node(
      Kind::BV_NOT,
      {rewriter.mk_node(Kind::BV_AND,
                        {rewriter.mk_node(Kind::BV_NOT, {node[0]}), node[1]})});
}

/**
 * match:  (bvudiv a b) where b = pow2(n)
 * result: (concat (_ bv0 n) ((_ extract (N - 1) n) a))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_POW2>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  assert(node.num_children() == 2);
  if (node[1].is_value())
  {
    const BitVector& val1 = node[1].value<BitVector>();
    if (val1.is_power_of_two())
    {
      uint64_t n    = val1.count_trailing_zeros();
      uint64_t size = val1.size();
      Node ext = rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, n});
      if (n == 0) return ext;
      return rewriter.mk_node(
          Kind::BV_CONCAT,
          {NodeManager::get().mk_value(BitVector::mk_zero(n)), ext});
    }
  }
  return node;
}

/**
 * match:  (bvudiv a a)
 * result: (ite (= a (_ bv0 N)) (bvnot (_ bv0 N)) (_ bv1 N))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_SAME>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0] == node[1])
  {
    NodeManager& nm = NodeManager::get();
    uint64_t size   = node.type().bv_size();
    Node one        = nm.mk_value(BitVector::mk_one(size));
    Node ones       = nm.mk_value(BitVector::mk_ones(size));
    Node zero       = nm.mk_value(BitVector::mk_zero(size));
    return rewriter.mk_node(
        Kind::ITE, {rewriter.mk_node(Kind::EQUAL, {node[0], zero}), ones, one});
  }
  return node;
}

/* bvult -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ULT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().compare(node[1].value<BitVector>()) < 0);
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvult (_ bv0 N) a)
 * result: (distinct (_ bv0 N) a)
 *
 * match:  (bvult (not (_ bv0 N)) a)
 * result: false
 *
 * match:  (bvult a (_ bv0 N))
 * result: false
 *
 * match:  (bvult a (_ bv1 N))
 * result: (= a (_ bv0 N))
 *
 * match:  (bvult a (not (_ bv0 N)))
 * result: (distinct a (not (_ bv0 N)))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_ULT_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_zero())
    {
      return rewriter.mk_node(
          Kind::NOT, {rewriter.mk_node(Kind::EQUAL, {node[0], node[1]})});
    }
    if (value0.is_ones())
    {
      return NodeManager::get().mk_value(false);
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_zero())
    {
      return NodeManager::get().mk_value(false);
    }
    if (value1.is_one())
    {
      return rewriter.mk_node(Kind::EQUAL,
                              {node[0],
                               NodeManager::get().mk_value(BitVector::mk_zero(
                                   node[0].type().bv_size()))});
    }
    if (value1.is_ones())
    {
      return rewriter.mk_node(
          Kind::NOT, {rewriter.mk_node(Kind::EQUAL, {node[0], node[1]})});
    }
  }
  return node;
}

/* bvudiv ------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UREM_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvurem(node[1].value<BitVector>()));
  return res;
}

/**
 * Match special values on either lhs or rhs.
 *
 * match:  (bvurem (_ bv0 N) a)
 * result: (_ bv0 N)
 *
 * match:  (bvurem a (_ bv0 N))
 * result: a
 *
 * match:  (bvurem a (_ bv1 N))
 * result: (_ bv0 N)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UREM_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0].is_value() && !node[1].is_value())
  {
    const BitVector& value0 = node[0].value<BitVector>();
    if (value0.is_zero())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value0.size()));
    }
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    const BitVector& value1 = node[1].value<BitVector>();
    if (value1.is_zero())
    {
      return node[0];
    }
    if (value1.is_one())
    {
      return NodeManager::get().mk_value(BitVector::mk_zero(value1.size()));
    }
  }
  return node;
}

/**
 * match:  (bvurem a b) with a and b of bit-width 1
 * result: (bvand a (bvnot (b))
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UREM_BV1>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].type().bv_size() != 1) return node;
  return rewriter.mk_node(Kind::BV_AND,
                          {node[0], rewriter.mk_node(Kind::BV_NOT, {node[1]})});
}

/**
 * match:  (bvurem a a)
 * result: (_ bv0 N)
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_UREM_SAME>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] == node[1])
  {
    return NodeManager::get().mk_value(
        BitVector::mk_zero(node.type().bv_size()));
  }
  return node;
}

/* bvxor -------------------------------------------------------------------- */

/**
 * Constant folding, matches when both lhs and rhs are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::BV_XOR_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvxor(node[1].value<BitVector>()));
  return res;
}

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_NAND_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  return rewriter.mk_node(Kind::BV_NOT,
                          {rewriter.mk_node(Kind::BV_AND, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_ADD,
      {rewriter.mk_node(Kind::BV_NOT, {node[0]}),
       NodeManager::get().mk_value(BitVector::mk_one(node.type().bv_size()))});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_NOR_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_NOT,
                          {rewriter.mk_node(Kind::BV_OR, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_OR_ELIM>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_NOT,
      {rewriter.mk_node(Kind::BV_AND,
                        {rewriter.mk_node(Kind::BV_NOT, {node[0]}),
                         rewriter.mk_node(Kind::BV_NOT, {node[1]})})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REDAND_ELIM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  return rewriter.mk_node(Kind::BV_COMP,
                          {node[0],
                           NodeManager::get().mk_value(
                               BitVector::mk_ones(node[0].type().bv_size()))}

  );
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REDOR_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_NOT,
      {rewriter.mk_node(Kind::BV_COMP,
                        {node[0],
                         NodeManager::get().mk_value(
                             BitVector::mk_zero(node[0].type().bv_size()))}

                        )});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REDXOR_ELIM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  Node result = rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {0, 0});
  for (size_t i = 1, size = node[0].type().bv_size(); i < size; ++i)
  {
    const Node& extract = rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {i, i});
    result              = rewriter.mk_node(Kind::BV_XOR, {result, extract});
  }
  return result;
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REPEAT_ELIM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  Node result = node[0];
  for (size_t i = 1, repeat = node.index(0); i < repeat; ++i)
  {
    result = rewriter.mk_node(Kind::BV_CONCAT, {result, node[0]});
  }
  return result;
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ROL_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  size_t size = node.type().bv_size();

  if (size == 1)
  {
    return node[0];
  }

  NodeManager& nm       = NodeManager::get();
  Node num_bits         = nm.mk_value(BitVector::from_ui(size, size));
  const Node& bits_left = rewriter.mk_node(Kind::BV_UREM, {node[1], num_bits});
  const Node& bits_right =
      rewriter.mk_node(Kind::BV_SUB, {num_bits, bits_left});
  const Node& rol =
      rewriter.mk_node(Kind::BV_OR,
                       {rewriter.mk_node(Kind::BV_SHL, {node[0], bits_left}),
                        rewriter.mk_node(Kind::BV_SHR, {node[0], bits_right})});

  // Check if we have to rotate (num_bits > 0)
  return rewriter.mk_node(
      Kind::ITE,
      {rewriter.mk_node(Kind::EQUAL,
                        {num_bits, nm.mk_value(BitVector::mk_zero(size))}),
       node[0],
       rol});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ROLI_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size      = node.type().bv_size();
  uint64_t rotate_by = node.index(0) % size;
  if (rotate_by)
  {
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(
             Kind::BV_EXTRACT, {node[0]}, {size - rotate_by - 1, 0}),
         rewriter.mk_node(
             Kind::BV_EXTRACT, {node[0]}, {size - 1, size - rotate_by})});
  }
  return node[0];
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ROR_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  size_t size = node.type().bv_size();

  if (size == 1)
  {
    return node[0];
  }

  NodeManager& nm        = NodeManager::get();
  Node num_bits          = nm.mk_value(BitVector::from_ui(size, size));
  const Node& bits_right = rewriter.mk_node(Kind::BV_UREM, {node[1], num_bits});
  const Node& bits_left =
      rewriter.mk_node(Kind::BV_SUB, {num_bits, bits_right});
  const Node& rol =
      rewriter.mk_node(Kind::BV_OR,
                       {rewriter.mk_node(Kind::BV_SHL, {node[0], bits_left}),
                        rewriter.mk_node(Kind::BV_SHR, {node[0], bits_right})});

  // Check if we have to rotate (num_bits > 0)
  return rewriter.mk_node(
      Kind::ITE,
      {rewriter.mk_node(Kind::EQUAL,
                        {num_bits, nm.mk_value(BitVector::mk_zero(size))}),
       node[0],
       rol});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_RORI_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size      = node.type().bv_size();
  uint64_t rotate_by = node.index(0) % size;
  if (rotate_by)
  {
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {rotate_by - 1, 0}),
         rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, rotate_by})});
  }
  return node[0];
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SADDO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 2);
  uint64_t size = node[0].type().bv_size();
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});
  const Node& add = rewriter.mk_node(Kind::BV_ADD, {node[0], node[1]});
  const Node& sign_add =
      rewriter.mk_node(Kind::BV_EXTRACT, {add}, {size - 1, size - 1});

  // Overflow occurs if
  //  1) negative + negative = positive
  //  2) positive + positive = negative
  Node one  = NodeManager::get().mk_value(BitVector::mk_one(1));
  Node zero = NodeManager::get().mk_value(BitVector::mk_zero(1));
  const Node& both_neg =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, one})});
  const Node& both_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero})});
  const Node& result_neg = rewriter.mk_node(Kind::EQUAL, {sign_add, one});
  const Node& result_pos = rewriter.mk_node(Kind::EQUAL, {sign_add, zero});

  return rewriter.mk_node(
      Kind::OR,
      {rewriter.mk_node(Kind::AND, {both_neg, result_pos}),
       rewriter.mk_node(Kind::AND, {both_pos, result_neg})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SDIV_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size = node.type().bv_size();

  if (size == 1)
  {
    return rewriter.mk_node(
        Kind::BV_NOT,
        {rewriter.mk_node(
            Kind::BV_AND,
            {rewriter.mk_node(Kind::BV_NOT, {node[0]}), node[1]})});
  }

  // Extract MSB of operands
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});

  // Checks whether result must be signed
  const Node& negate_res = rewriter.mk_node(Kind::BV_XOR, {sign0, sign1});

  // Normalize operands to unsigned
  Node one = NodeManager::get().mk_value(BitVector::mk_one(1));
  const Node& abs0 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[0]}),
                        node[0]});
  const Node& abs1 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign1, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[1]}),
                        node[1]});

  // Unsigned divison
  const Node& udiv = rewriter.mk_node(Kind::BV_UDIV, {abs0, abs1});

  // Negate result if necessary
  return rewriter.mk_node(Kind::ITE,
                          {rewriter.mk_node(Kind::EQUAL, {negate_res, one}),
                           rewriter.mk_node(Kind::BV_NEG, {udiv}),
                           udiv});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SDIVO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 2);
  // Overflow if node[0] = min_signed and node[1] = -1
  uint64_t size   = node[0].type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node min_signed = nm.mk_value(BitVector::mk_min_signed(size));
  Node ones       = nm.mk_value(BitVector::mk_ones(size));
  return rewriter.mk_node(Kind::AND,
                          {rewriter.mk_node(Kind::EQUAL, {node[0], min_signed}),
                           rewriter.mk_node(Kind::EQUAL, {node[1], ones})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SGE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_SLT, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SGT_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_SLT, {node[1], node[0]});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SIGN_EXTEND_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node)
{
  uint64_t extend_by = node.index(0);
  if (extend_by)
  {
    NodeManager& nm = NodeManager::get();
    Node zero       = nm.mk_value(BitVector::mk_zero(extend_by));
    Node ones       = nm.mk_value(BitVector::mk_ones(extend_by));
    uint64_t size   = node[0].type().bv_size();
    const Node& sign_bit =
        rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(
             Kind::ITE,
             {rewriter.mk_node(Kind::EQUAL,
                               {sign_bit, nm.mk_value(BitVector::mk_one(1))}),
              ones,
              zero}),
         node[0]});
  }
  return node[0];
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SLE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_SLT, {node[1], node[0]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SMOD_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size   = node.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(1));
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});
  // Normalize operands to unsigned
  const Node& abs0 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[0]}),
                        node[0]});
  const Node& abs1 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign1, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[1]}),
                        node[1]});
  // Unsigned division
  const Node& urem         = rewriter.mk_node(Kind::BV_UREM, {abs0, abs1});
  const Node& urem_is_zero = rewriter.mk_node(
      Kind::EQUAL, {urem, nm.mk_value(BitVector::mk_zero(size))});
  const Node& neg_urem = rewriter.mk_node(Kind::BV_NEG, {urem});

  // Compute result based on MSB of operands
  Node zero1 = nm.mk_value(BitVector::mk_zero(1));
  const Node& both_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero1}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero1})});
  const Node& neg_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero1})});
  const Node& pos_neg =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero1}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, one})});

  return rewriter.mk_node(
      Kind::ITE,
      {rewriter.mk_node(Kind::OR, {urem_is_zero, both_pos}),
       urem,
       rewriter.mk_node(
           Kind::ITE,
           {neg_pos,
            rewriter.mk_node(Kind::BV_ADD, {neg_urem, node[1]}),
            rewriter.mk_node(Kind::ITE,
                             {pos_neg,
                              rewriter.mk_node(Kind::BV_ADD, {urem, node[1]}),
                              neg_urem})})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SMULO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 2);

  /* Signed multiplication overflow detection.
   * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
   * overflow detection circuits", 2001.
   * http://ieeexplore.ieee.org/document/987767 */

  uint64_t size = node[0].type().bv_size();
  Node one      = NodeManager::get().mk_value(BitVector::mk_one(1));

  if (size == 1)
  {
    return rewriter.mk_node(
        Kind::EQUAL, {rewriter.mk_node(Kind::BV_AND, {node[0], node[1]}), one});
  }

  Node mul = rewriter.mk_node(
      Kind::BV_MUL,
      {rewriter.mk_node(Kind::BV_SIGN_EXTEND, {node[0]}, {1}),
       rewriter.mk_node(Kind::BV_SIGN_EXTEND, {node[1]}, {1})});
  if (size == 2)
  {
    return rewriter.mk_node(
        Kind::EQUAL,
        {rewriter.mk_node(
             Kind::BV_XOR,
             {rewriter.mk_node(Kind::BV_EXTRACT, {mul}, {size, size}),
              rewriter.mk_node(Kind::BV_EXTRACT, {mul}, {size - 1, size - 1})}),
         one});
  }

  Node xor0 = rewriter.mk_node(
      Kind::BV_XOR,
      {node[0],
       rewriter.mk_node(Kind::BV_SIGN_EXTEND,
                        {rewriter.mk_node(
                            Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1})},
                        {size - 1})});
  Node xor1 = rewriter.mk_node(
      Kind::BV_XOR,
      {node[1],
       rewriter.mk_node(Kind::BV_SIGN_EXTEND,
                        {rewriter.mk_node(
                            Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1})},
                        {size - 1})});

  Node ppc = rewriter.mk_node(Kind::BV_EXTRACT, {xor0}, {size - 2, size - 2});
  Node res = rewriter.mk_node(
      Kind::BV_AND, {rewriter.mk_node(Kind::BV_EXTRACT, {xor1}, {1, 1}), ppc});
  for (uint64_t i = 1; i < size - 2; ++i)
  {
    ppc = rewriter.mk_node(
        Kind::BV_OR,
        {ppc,
         rewriter.mk_node(
             Kind::BV_EXTRACT, {xor0}, {size - 2 - i, size - 2 - i})});
    res = rewriter.mk_node(
        Kind::BV_OR,
        {res,
         rewriter.mk_node(
             Kind::BV_AND,
             {rewriter.mk_node(Kind::BV_EXTRACT, {xor1}, {i + 1, i + 1}),
              ppc})});
  }

  return rewriter.mk_node(
      Kind::EQUAL,
      {rewriter.mk_node(
           Kind::BV_OR,
           {res,
            rewriter.mk_node(
                Kind::BV_XOR,
                {rewriter.mk_node(Kind::BV_EXTRACT, {mul}, {size, size}),
                 rewriter.mk_node(Kind::BV_EXTRACT, {mul}, {size - 1, size - 1})

                })}),
       one});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SREM_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size = node.type().bv_size();

  if (size == 1)
  {
    return rewriter.mk_node(
        Kind::BV_AND, {node[0], rewriter.mk_node(Kind::BV_NOT, {node[1]})});
  }

  NodeManager& nm = NodeManager::get();

  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});

  // Normalize operands to unsigned
  Node one = nm.mk_value(BitVector::mk_one(1));
  const Node& abs0 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[0]}),
                        node[0]});
  const Node& abs1 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign1, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[1]}),
                        node[1]});

  const Node& urem     = rewriter.mk_node(Kind::BV_UREM, {abs0, abs1});
  const Node& neg_urem = rewriter.mk_node(Kind::BV_NEG, {urem});
  return rewriter.mk_node(
      Kind::ITE, {rewriter.mk_node(Kind::EQUAL, {sign0, one}), neg_urem, urem});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SSUBO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 2);
  uint64_t size = node[0].type().bv_size();
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});
  const Node& sub = rewriter.mk_node(Kind::BV_SUB, {node[0], node[1]});
  const Node& sign_sub =
      rewriter.mk_node(Kind::BV_EXTRACT, {sub}, {size - 1, size - 1});

  // Overflow occurs if
  //  1) negative - positive = positive
  //  2) postive - negative = negative
  Node one  = NodeManager::get().mk_value(BitVector::mk_one(1));
  Node zero = NodeManager::get().mk_value(BitVector::mk_zero(1));
  const Node& neg_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero})});
  const Node& pos_neg =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, one})});
  const Node& result_neg = rewriter.mk_node(Kind::EQUAL, {sign_sub, one});
  const Node& result_pos = rewriter.mk_node(Kind::EQUAL, {sign_sub, zero});

  return rewriter.mk_node(Kind::OR,
                          {rewriter.mk_node(Kind::AND, {neg_pos, result_pos}),
                           rewriter.mk_node(Kind::AND, {pos_neg, result_neg})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SUB_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_ADD,
                          {node[0], rewriter.mk_node(Kind::BV_NEG, {node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UADDO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  const Node& add = rewriter.mk_node(
      Kind::BV_ADD,
      {rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[0]}, {1}),
       rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[1]}, {1})});
  uint64_t size = add.type().bv_size();
  Node one      = NodeManager::get().mk_value(BitVector::mk_one(1));
  return rewriter.mk_node(
      Kind::EQUAL,
      {rewriter.mk_node(Kind::BV_EXTRACT, {add}, {size - 1, size - 1}), one});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UGE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_ULT, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UGT_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_ULT, {node[1], node[0]});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ULE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_ULT, {node[1], node[0]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UMULO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  /* Unsigned multiplication overflow detection.
   * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
   * overflow detection circuits", 2001.
   * http://ieeexplore.ieee.org/document/987767 */

  uint64_t size = node[0].type().bv_size();

  if (size == 1)
  {
    return NodeManager::get().mk_value(false);
  }

  Node res;
  Node uppc =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});

  for (uint64_t i = 1; i < size; ++i)
  {
    Node aand = rewriter.mk_node(
        Kind::BV_AND,
        {rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {i, i}), uppc});
    if (res.is_null())
    {
      res = aand;
    }
    else
    {
      res = rewriter.mk_node(Kind::BV_OR, {res, aand});
    }
    uppc = rewriter.mk_node(
        Kind::BV_OR,
        {rewriter.mk_node(
             Kind::BV_EXTRACT, {node[0]}, {size - 1 - i, size - 1 - i}),
         uppc});
  }
  Node mul = rewriter.mk_node(
      Kind::BV_MUL,
      {rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[0]}, {1}),
       rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[1]}, {1})});
  res = rewriter.mk_node(
      Kind::BV_OR,
      {res, rewriter.mk_node(Kind::BV_EXTRACT, {mul}, {size, size})});
  return rewriter.mk_node(
      Kind::EQUAL, {res, NodeManager::get().mk_value(BitVector::mk_one(1))});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_USUBO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  const Node& sub = rewriter.mk_node(
      Kind::BV_SUB,
      {rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[0]}, {1}),
       rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[1]}, {1})});
  uint64_t size = sub.type().bv_size();
  Node one      = NodeManager::get().mk_value(BitVector::mk_one(1));
  return rewriter.mk_node(
      Kind::EQUAL,
      {rewriter.mk_node(Kind::BV_EXTRACT, {sub}, {size - 1, size - 1}), one});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  return rewriter.mk_node(Kind::BV_NOT,
                          {rewriter.mk_node(Kind::BV_XOR, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_XOR_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_AND,
      {rewriter.mk_node(Kind::BV_OR, {node[0], node[1]}),
       rewriter.mk_node(Kind::BV_NOT,
                        {rewriter.mk_node(Kind::BV_AND, {node[0], node[1]})})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ZERO_EXTEND_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node)
{
  uint64_t extend_by = node.index(0);
  if (extend_by)
  {
    Node zero = NodeManager::get().mk_value(BitVector::mk_zero(extend_by));
    return rewriter.mk_node(Kind::BV_CONCAT, {zero, node[0]});
  }
  return node[0];
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla
