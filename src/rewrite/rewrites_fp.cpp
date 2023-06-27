/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewrites_fp.h"

#include "node/node_manager.h"
#include "solver/fp/floating_point.h"

namespace bzla {

using namespace node;

/* fpabs -------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * match:  (fp.abs (fp.abs a)) or (fp.abs (fp.neg a))
 * result: (fp.abs a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_ABS_ABS_NEG>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());

  if (node[0].kind() != Kind::FP_ABS && node[0].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_ABS, {node[0][0]});
}

/* fpadd -------------------------------------------------------------------- */

/**
 * Constant folding, matches when all operands are values.
 */
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

/**
 * Constant folding, matches when all operands are values.
 */
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

/* fpfma -------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand all operands are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_FMA_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 4);
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());
  assert(node[2].type().is_fp());
  assert(node[3].type().is_fp());
  for (const auto& c : node)
  {
    if (!c.is_value()) return node;
  }
  Node res = NodeManager::get().mk_value(
      node[1].value<FloatingPoint>().fpfma(node[0].value<RoundingMode>(),
                                           node[2].value<FloatingPoint>(),
                                           node[3].value<FloatingPoint>()));
  return res;
}

/* fpisinf ------------------------------------------------------------------ */

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * match:  (fp.isInfinite (fp.abs a)) or (fp.isInfinite (fp.neg a))
 * result: (fp.isInfinite a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_INF_ABS_NEG>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());

  if (node[0].kind() != Kind::FP_ABS && node[0].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_IS_INF, {node[0][0]});
}

/* fpisnan ------------------------------------------------------------------ */

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * match:  (fp.isNaN (fp.abs a)) or (fp.isNaN (fp.neg a))
 * result: (fp.isNaN a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_NAN_ABS_NEG>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());

  if (node[0].kind() != Kind::FP_ABS && node[0].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_IS_NAN, {node[0][0]});
}

/* fpisneg ------------------------------------------------------------------ */

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * match:  (fp.isNormal (fp.abs a)) or (fp.isNormal (fp.neg a))
 * result: (fp.isNormal a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_NORM_ABS_NEG>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());

  if (node[0].kind() != Kind::FP_ABS && node[0].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_IS_NORMAL, {node[0][0]});
}

/* fpispos ------------------------------------------------------------------ */

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * match:  (fp.isSubnormal (fp.abs a)) or (fp.isSubnormal (fp.neg a))
 * result: (fp.isSubnormal a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_SUBNORM_ABS_NEG>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());

  if (node[0].kind() != Kind::FP_ABS && node[0].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_IS_SUBNORMAL, {node[0][0]});
}

/* fpiszero ----------------------------------------------------------------- */

/**
 * Constant folding, matches when operand is a value.
 */
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

/**
 * match:  (fp.isZero (fp.abs a)) or (fp.isZero (fp.neg a))
 * result: (fp.isZero a)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_IS_ZERO_ABS_NEG>::_apply(Rewriter& rewriter,
                                                         const Node& node)
{
  assert(node.num_children() == 1);
  assert(node[0].type().is_fp());

  if (node[0].kind() != Kind::FP_ABS && node[0].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_IS_ZERO, {node[0][0]});
}

/* fple --------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand all operands are values.
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_LEQ_EVAL>::_apply(Rewriter& rewriter,
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

/**
 * match:  (fp.leq a  a)
 * result: (not (fp.isNaN a))
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_LEQ_EQ>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0] != node[1]) return node;
  return rewriter.invert_node(rewriter.mk_node(Kind::FP_IS_NAN, {node[0]}));
}

/* fplt --------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand all operands are values.
 */
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

/**
 * match:  (fp.lt a a)
 * result: false
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_LT_EQ>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] != node[1]) return node;
  return NodeManager::get().mk_value(false);
}

/* fpmin -------------------------------------------------------------------- */

/**
 * match:  (fp.min a a)
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_MIN_EQ>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] != node[1]) return node;
  return node[0];
}

/* fpmax -------------------------------------------------------------------- */

/**
 * match:  (fp.max a a)
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_MAX_EQ>::_apply(Rewriter& rewriter,
                                                const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0] != node[1]) return node;
  return node[0];
}

/* fpmul -------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand all operands are values.
 */
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

/**
 * Constant folding, matches when operand operand is a value.
 */
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

/**
 * match:  (fp.neg (fp.neg a))
 * result: a
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_NEG_NEG>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 1);
  if (node[0].kind() != Kind::FP_NEG) return node;
  return node[0][0];
}

/* fprem -------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand all operands are values.
 */
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

/**
 * match:  (fp.rem (fp.rem a  b)  b)
 * result: (fp.rem a  b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_REM_SAME_DIV>::_apply(Rewriter& rewriter,
                                                      const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (node[0].kind() != Kind::FP_REM || node[1] != node[0][1]) return node;
  return node[0];
}

/**
 * match:  (fp.rem a (fp.abs b)) or (fp.rem (a (fp.neg b))
 * result: (fp.rem a  b)
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_REM_ABS_NEG>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  assert(node.num_children() == 2);
  if (node[1].kind() != Kind::FP_ABS && node[1].kind() != Kind::FP_NEG)
  {
    return node;
  }
  return rewriter.mk_node(Kind::FP_REM, {node[0], node[1][0]});
}

/**
 * match:  (fp.rem (fp.neg a) b)
 * result: (fp.neg (fp.rem a b))
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_REM_NEG>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 2);
  if (node[0].kind() != Kind::FP_NEG) return node;
  return rewriter.mk_node(
      Kind::FP_NEG, {rewriter.mk_node(Kind::FP_REM, {node[0][0], node[1]})});
}

/* fprti -------------------------------------------------------------------- */

/**
 * Constant folding, matches when operand all operands are values.
 */
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

/**
 * Constant folding, matches when operand all operands are values.
 */
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

/**
 * Constant folding, matches when operand operand is a value.
 */
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

/**
 * Constant folding, matches when operand operand is a value.
 */
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

/**
 * Constant folding, matches when operand operand is a value.
 */
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

/**
 * Conditional elimination, eliminated if to be converted node is of
 * bit-vector size one.
 *
 * match:  ((_ to_fp N M) r a) with size(a) = 1
 * result: (ite
 *            (= a #b1)
 *            (fp.neg ((_ to_fp_unsigned N M) r a))
 *            ((_ to_fp_unsigned N M) r a))
 *
 * @note This is imposed by SymFPU, it does not allow conversions from signed
 *        bit-vectors of size one.
 */
template <>
Node
RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_SBV_BV1_ELIM>::_apply(
    Rewriter& rewriter, const Node& node)
{
  assert(node.num_children() == 2);
  assert(node.num_indices() == 2);
  assert(node[1].type().is_bv());
  if (node[1].type().bv_size() == 1)
  {
    Node to_ubv = rewriter.mk_node(Kind::FP_TO_FP_FROM_UBV,
                                   {node[0], node[1]},
                                   {node.index(0), node.index(1)});
    return rewriter.mk_node(
        Kind::ITE,
        {rewriter.mk_node(
             Kind::EQUAL,
             {node[1], NodeManager::get().mk_value(BitVector::mk_one(1))}),
         rewriter.mk_node(Kind::FP_NEG, {to_ubv}),
         to_ubv});
  }
  return node;
}

/* to_fp: from_ubv ---------------------------------------------------------- */

/**
 * Constant folding, matches when operand operand is a value.
 */
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

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::FP_FP_ELIM>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 3);
  return rewriter.mk_node(
      Kind::FP_TO_FP_FROM_BV,
      {rewriter.mk_node(
          Kind::BV_CONCAT,
          {node[0], rewriter.mk_node(Kind::BV_CONCAT, {node[1], node[2]})})},
      {node[1].type().bv_size(), node[2].type().bv_size() + 1});
}

template <>
Node
RewriteRule<RewriteRuleKind::FP_GEQ_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  assert(node.num_children() == 2);
  return rewriter.mk_node(Kind::FP_LEQ, {node[1], node[0]});
}

template <>
Node
RewriteRule<RewriteRuleKind::FP_GT_ELIM>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  assert(node.num_children() == 2);
  return rewriter.mk_node(Kind::FP_LT, {node[1], node[0]});
}

template <>
Node
RewriteRule<RewriteRuleKind::FP_EQUAL_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  assert(node.num_children() == 2);
  return rewriter.mk_node(
      Kind::AND,
      {rewriter.mk_node(
           Kind::AND,
           {rewriter.invert_node(rewriter.mk_node(Kind::FP_IS_NAN, {node[0]})),
            rewriter.invert_node(
                rewriter.mk_node(Kind::FP_IS_NAN, {node[1]}))}),
       rewriter.mk_node(
           Kind::OR,
           {rewriter.mk_node(Kind::EQUAL, {node[0], node[1]}),
            rewriter.mk_node(
                Kind::AND,
                {rewriter.mk_node(Kind::FP_IS_ZERO, {node[0]}),
                 rewriter.mk_node(Kind::FP_IS_ZERO, {node[1]})})})});
}

template <>
Node
RewriteRule<RewriteRuleKind::FP_SUB_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  assert(node.num_children() == 3);
  return rewriter.mk_node(
      Kind::FP_ADD,
      {node[0], node[1], rewriter.mk_node(Kind::FP_NEG, {node[2]})});
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
