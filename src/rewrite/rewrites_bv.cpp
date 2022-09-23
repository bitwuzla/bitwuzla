#include "rewrite/rewrites_bv.h"

#include "bitvector.h"
#include "node/node_manager.h"

namespace bzla {

/* bvadd -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvadd(node[1].value<BitVector>()));
  return res;
}

/* bvand -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_AND_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvand(node[1].value<BitVector>()));
  return res;
}

/* bvashr ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_ASHR_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvashr(node[1].value<BitVector>()));
  return res;
}

/* bvconcat ----------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_CONCAT_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvconcat(node[1].value<BitVector>()));
  return res;
}

/* bvmul -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvmul(node[1].value<BitVector>()));
  return res;
}

/* bvshl -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_SHL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvshl(node[1].value<BitVector>()));
  return res;
}

/* bvshr -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvshr(node[1].value<BitVector>()));
  return res;
}

/* bvslt -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_SLT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().signed_compare(node[1].value<BitVector>())
      < 0);
  return res;
}

/* bvudiv ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvudiv(node[1].value<BitVector>()));
  return res;
}

/* bvult -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_ULT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().compare(node[1].value<BitVector>()) < 0);
  return res;
}

/* bvudiv ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_UREM_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvurem(node[1].value<BitVector>()));
  return res;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
