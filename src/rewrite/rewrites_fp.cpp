#include "rewrite/rewrites_fp.h"

#include "node/node_manager.h"
#include "solver/fp/floating_point.h"

namespace bzla {

/* fpabs -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_ABS_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpabs());
  return res;
}

/* fpadd -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_ADD_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 3);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node[2].type().is_fp());
  for (const auto& c : node)
  {
    if (!c.is_value()) return node;
  }
  Node res = NodeManager::get().mk_value(node[1].value<FloatingPoint>().fpadd(
      node[0].value<RoundingMode>(), node[2].value<FloatingPoint>()));
  return res;
}

/* fpdiv -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_DIV_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 3);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node[2].type().is_fp());
  for (const auto& c : node)
  {
    if (!c.is_value()) return node;
  }
  Node res = NodeManager::get().mk_value(node[1].value<FloatingPoint>().fpdiv(
      node[0].value<RoundingMode>(), node[2].value<FloatingPoint>()));
  return res;
}

/* fpisinf ------------------------------------------------------------------ */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_INF_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpisinf());
  return res;
}

/* fpisnan ------------------------------------------------------------------ */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_NAN_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpisnan());
  return res;
}

/* fpisneg ------------------------------------------------------------------ */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_NEG_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpisneg());
  return res;
}

/* fpisnorm ----------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_NORM_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpisnormal());
  return res;
}

/* fpispos ------------------------------------------------------------------ */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_POS_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpispos());
  return res;
}

/* fpissubnorm -------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_SUBNORM_EVAL>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<FloatingPoint>().fpissubnormal());
  return res;
}

/* fpiszero ----------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_ZERO_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpiszero());
  return res;
}

/* fple --------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_LE_EVAL>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_fp());
  assert(node[1].type().is_fp());
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<FloatingPoint>().fple(node[1].value<FloatingPoint>()));
  return res;
}

/* fplt --------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_LT_EVAL>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_fp());
  assert(node[1].type().is_fp());
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<FloatingPoint>().fplt(node[1].value<FloatingPoint>()));
  return res;
}

/* fpmin -------------------------------------------------------------------- */

/* fpmax -------------------------------------------------------------------- */

/* fpmul -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_MUL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 3);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node[2].type().is_fp());
  for (const auto& c : node)
  {
    if (!c.is_value()) return node;
  }
  Node res = NodeManager::get().mk_value(node[1].value<FloatingPoint>().fpmul(
      node[0].value<RoundingMode>(), node[2].value<FloatingPoint>()));
  return res;
}

/* fpneg -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_NEG_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpneg());
  return res;
}

/* fprem -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_REM_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_fp());
  assert(node[1].type().is_fp());
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<FloatingPoint>().fprem(node[1].value<FloatingPoint>()));
  return res;
}

/* fprti -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_RTI_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[1].value<FloatingPoint>().fprti(node[0].value<RoundingMode>()));
  return res;
}

/* fpsqrt ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_SQRT_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[1].value<FloatingPoint>().fpsqrt(node[0].value<RoundingMode>()));
  return res;
}

/* to_fp: from_bv ----------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_BV_EVAL>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  assert(node[0].type().is_bv());
  assert(node.num_indices() == 2);
  if (!node[0].is_value()) return node;
  NodeManager& nm = NodeManager::get();
  Node res        = nm.mk_value(FloatingPoint(
      nm.mk_fp_type(node.index(0), node.index(1)), node[0].value<BitVector>()));
  return res;
}

/* to_fp: from_fp ----------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_FP_EVAL>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node.num_indices() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  NodeManager& nm = NodeManager::get();
  Node res =
      nm.mk_value(FloatingPoint(nm.mk_fp_type(node.index(0), node.index(1)),
                                node[0].value<RoundingMode>(),
                                node[1].value<FloatingPoint>()));
  return res;
}

/* to_fp: from_sbv ---------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_SBV_EVAL>::_apply(Rewriter& rewriter,
                                                             const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_bv());
  assert(node.num_indices() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  NodeManager& nm = NodeManager::get();
  Node res =
      nm.mk_value(FloatingPoint(nm.mk_fp_type(node.index(0), node.index(1)),
                                node[0].value<RoundingMode>(),
                                node[1].value<BitVector>(),
                                true));
  return res;
}

/* to_fp: from_ubv ---------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_UBV_EVAL>::_apply(Rewriter& rewriter,
                                                             const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_bv());
  assert(node.num_indices() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  NodeManager& nm = NodeManager::get();
  Node res =
      nm.mk_value(FloatingPoint(nm.mk_fp_type(node.index(0), node.index(1)),
                                node[0].value<RoundingMode>(),
                                node[1].value<BitVector>(),
                                false));
  return res;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
