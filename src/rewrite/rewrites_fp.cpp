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
  for (const auto& c : node)
  {
    if (!c.is_value()) return node;
  }
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node[2].type().is_fp());
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
  for (const auto& c : node)
  {
    if (!c.is_value()) return node;
  }
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node[2].type().is_fp());
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
  if (!node[0].is_value()) return node;
  Node res =
      NodeManager::get().mk_value(node[0].value<FloatingPoint>().fpiszero());
  return res;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
