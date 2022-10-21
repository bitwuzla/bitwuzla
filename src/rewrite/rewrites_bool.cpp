#include "rewrite/rewrites_bool.h"

#include <cmath>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewrite_utils.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

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
  if (node[idx0].kind() == Kind::AND
      && node::utils::is_or(node[idx1], or0, or1))
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
  if (node::utils::is_or(node[idx1], or0, or1))
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
 * match   (= a false)
 * result: (not a)
 */
namespace {
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
      BitVector value0 = node[idx0].value<BitVector>();
      if (value0.is_zero())
      {
        if (node[idx1].kind() == Kind::BV_XOR)
        {
          // 0 == a ^ b  --->  a = b
          return rewriter.mk_node(Kind::EQUAL, {node[idx1][0], node[idx1][1]});
        }
        Node or0, or1;
        if (node::utils::is_bv_or(node[idx1], or0, or1))
        {
          // 0 == a | b  ---> a == 0 && b == 0
          return rewriter.mk_node(
              Kind::AND,
              {rewriter.mk_node(Kind::EQUAL, {or0, node[idx0]}),
               rewriter.mk_node(Kind::EQUAL, {or1, node[idx0]})});
        }
      }
      else if (value0.is_ones())
      {
        if (node[idx1].kind() == Kind::BV_AND)
        {
          // 1..1 == a & b  ---> a == 1..1 && b == 1..1
          return rewriter.mk_node(
              Kind::AND,
              {rewriter.mk_node(Kind::EQUAL, {node[idx1][0], node[idx0]}),
               rewriter.mk_node(Kind::EQUAL, {node[idx1][1], node[idx0]})});
        }
        Node xnor0, xnor1;
        if (node::utils::is_bv_xnor(node[idx1], xnor0, xnor1))
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
 * match:  (= a (not (ite c a b)))
 * result: (and (not c) (= a (not b)))
 *
 * match:  (= a (not (ite c b a)))
 * result: (and c (= a (not b)))
 */
namespace {
Node
_rw_eq_ite_bv1(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::NOT && node[idx0][0].kind() == Kind::ITE)
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
               {node[idx1], rewriter.mk_node(Kind::NOT, {node[idx0][0][1]})})});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::EQUAL_ITE_BV1>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  Node res = _rw_eq_ite_bv1(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_ite_bv1(rewriter, node, 1);
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
 * match:  (= (bvadd a b) a)
 * result: (= b (_ bv0 N))
 *
 * Note: This rule will not lead to less variable substitutions since `a` cannot
 *       be substituted (the occurrence check will fail).
 */
namespace {
Node
_rw_eq_add(Rewriter& rewriter, const Node& node, size_t idx)
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
RewriteRule<RewriteRuleKind::EQUAL_ADD>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  Node res = _rw_eq_add(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_add(rewriter, node, 1);
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
RewriteRule<RewriteRuleKind::EQUAL_ADD_ADD>::_apply(Rewriter& rewriter,
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

    // TODO: check why we only rewrite when ext1_lhs is a non-slice and
    //       ext1_rhs is a slice
    //       NOTE: disabled second condition for now since it makes no sense
    if (ext1_lhs.kind() != Kind::BV_EXTRACT)
    //&& ext1_rhs.kind() == Kind::BV_EXTRACT)
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
RewriteRule<RewriteRuleKind::EQUAL_CONCAT>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  Node res = _rw_eq_concat(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_eq_concat(rewriter, node, 1);
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
  if (node::utils::is_xnor(node, xnor0, xnor1))
  {
    return rewriter.mk_node(Kind::EQUAL, {xnor0, xnor1});
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
