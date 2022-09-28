#include "rewrite/rewrites_bool.h"

#include "bitvector.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla {

using namespace node;

/* and ---------------------------------------------------------------------- */

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

/* equal -------------------------------------------------------------------- */

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

namespace {
Node
_rw_eq_special_const(Rewriter& rewriter, const Node& node, size_t idx)
{
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
        if (node[idx1].kind() == Kind::BV_NOT
            && node[idx1][0].kind() == Kind::BV_AND)
        {
          // 0 == a | b  ---> a == 0 && b == 0
          return rewriter.mk_node(
              Kind::AND,
              {
                  rewriter.mk_node(Kind::EQUAL, {node[idx1][0][0], node[idx0]}),
                  rewriter.mk_node(Kind::EQUAL, {node[idx1][0][1], node[idx0]}),
              });
        }
      }
      if (value0.is_ones())
      {
        if (node[idx1].kind() == Kind::BV_AND)
        {
          // 1..1 == a & b  ---> a == 1..1 && b == 1..1
          return rewriter.mk_node(
              Kind::AND,
              {rewriter.mk_node(Kind::EQUAL, {node[idx1][0], node[idx0]}),
               rewriter.mk_node(Kind::EQUAL, {node[idx1][1], node[idx0]})

              });
        }
        if (node[idx1].kind() == Kind::BV_NOT
            && node[idx1][0].kind() == Kind::BV_XOR)
        {
          // 1..1 == a XNOR b  --->  a = b
          return rewriter.mk_node(Kind::EQUAL,
                                  {node[idx1][0][0], node[idx1][0][1]});
        }
      }
    }
    else if (type0.is_bool())
    {
      if (node[idx0].value<bool>())
      {
        return node[idx1];
      }
      return rewriter.mk_node(Kind::NOT, {node[idx1]});
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
  assert(node.num_children() == 2);

  if (node[0].is_value() && !node[1].is_value())
  {
    return _rw_eq_special_const(rewriter, node, 0);
  }
  else if (!node[0].is_value() && node[1].is_value())
  {
    return _rw_eq_special_const(rewriter, node, 1);
  }
  return node;
}

/* not ---------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::NOT_EVAL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value()) return node;
  return NodeManager::get().mk_value(!node[0].value<bool>());
}

/* or ----------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::OR_ELIM>::_apply(Rewriter& rewriter,
                                              const Node& node)
{
  return rewriter.mk_node(
      Kind::NOT,
      {rewriter.mk_node(Kind::AND,
                        {rewriter.mk_node(Kind::NOT, {node[0]}),
                         rewriter.mk_node(Kind::NOT, {node[1]})})});
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
