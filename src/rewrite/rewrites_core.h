/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_REWRITES_BOOL_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BOOL_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

/* equal -------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::EQUAL_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_CONST>::_apply(Rewriter& rewriter,
                                                       const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_EQUAL_CONST_BV1>::_apply(
    Rewriter& rewriter, const Node& node);

// true_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_TRUE>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// false_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_FALSE>::_apply(Rewriter& rewriter,
                                                       const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_INV>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// bcond_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// bcond_if_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE_SAME>::_apply(Rewriter& rewriter,
                                                          const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE_INVERTED>::_apply(
    Rewriter& rewriter, const Node& node);

// bcond_uneq_if_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE_DIS_BV1>::_apply(Rewriter& rewriter,
                                                             const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE_LIFT_COND>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::EQUAL_CONST_BV_ADD>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::EQUAL_CONST_BV_MUL>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::EQUAL_CONST_BV_NOT>::_apply(
    Rewriter& rewriter, const Node& node);

// add_left_eq
// add_right_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_BV_ADD>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// add_add_1_eq
// add_add_2_eq
// add_add_3_eq
// add_add_4_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_BV_ADD_ADD>::_apply(Rewriter& rewriter,
                                                            const Node& node);
// concat_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_BV_CONCAT>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// sub_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_BV_SUB>::_apply(Rewriter& rewriter,
                                                        const Node& node);

/* distinct ----------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::DISTINCT_CARD>::_apply(Rewriter& rewriter,
                                                         const Node& node);

/* ite ---------------------------------------------------------------------- */

// const_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_EVAL>::_apply(Rewriter& rewriter,
                                                    const Node& node);
// equal_branches_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_SAME>::_apply(Rewriter& rewriter,
                                                    const Node& node);
// cond_if_dom_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_THEN_ITE1>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// cond_if_merge_if_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_THEN_ITE2>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// cond_if_merge_else_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_THEN_ITE3>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// cond_else_dom_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_ELSE_ITE1>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// cond_else_merge_if_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_ELSE_ITE2>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// cond_else_merge_else_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_ELSE_ITE3>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// bool_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_BOOL>::_apply(Rewriter& rewriter,
                                                    const Node& node);
// concat_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_BV_CONCAT>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// op_lhs_cond
// op_rhs_cond
template <>
Node RewriteRule<RewriteRuleKind::ITE_BV_OP>::_apply(Rewriter& rewriter,
                                                     const Node& node);

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::DISTINCT_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

/* --- Commutative Operator Normalization ----------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::NORMALIZE_COMM>::_apply(Rewriter& rewriter,
                                                          const Node& node);

/* --- Quantifiers ---------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::EXISTS_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* -------------------------------------------------------------------------- */
}  // namespace bzla
#endif
