/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_REWRITES_FP_H_INCLUDED
#define BZLA_REWRITE_REWRITES_FP_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

/* fpabs -------------------------------------------------------------------- */

// const_unary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_ABS_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// fp_abs
template <>
Node RewriteRule<RewriteRuleKind::FP_ABS_ABS_NEG>::_apply(Rewriter& rewriter,
                                                          const Node& node);

/* fpadd -------------------------------------------------------------------- */

// const_ternary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_ADD_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* fpdiv -------------------------------------------------------------------- */

// const_ternary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_DIV_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* fpisinf ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_INF_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// fp_tester_sign_ops
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_INF_ABS_NEG>::_apply(Rewriter& rewriter,
                                                             const Node& node);

/* fpisnan ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NAN_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// fp_tester_sign_ops
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NAN_ABS_NEG>::_apply(Rewriter& rewriter,
                                                             const Node& node);

/* fpisneg ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NEG_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);
/* fpisnorm ----------------------------------------------------------------- */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NORM_EVAL>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// fp_tester_sign_ops
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NORM_ABS_NEG>::_apply(
    Rewriter& rewriter, const Node& node);

/* fpispos ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_POS_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);

/* fpissubnorm -------------------------------------------------------------- */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_SUBNORM_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);
// fp_tester_sign_ops
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_SUBNORM_ABS_NEG>::_apply(
    Rewriter& rewriter, const Node& node);

/* fpiszero ----------------------------------------------------------------- */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_ZERO_EVAL>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// fp_tester_sign_ops
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_ZERO_ABS_NEG>::_apply(
    Rewriter& rewriter, const Node& node);

/* fpleq -------------------------------------------------------------------- */

// const_binary_fp_bool_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_LEQ_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// fp_lte
template <>
Node RewriteRule<RewriteRuleKind::FP_LEQ_EQ>::_apply(Rewriter& rewriter,
                                                     const Node& node);

/* fplte -------------------------------------------------------------------- */

// const_binary_fp_bool_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_LT_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// fp_lt
template <>
Node RewriteRule<RewriteRuleKind::FP_LT_EQ>::_apply(Rewriter& rewriter,
                                                    const Node& node);

/* fpmin -------------------------------------------------------------------- */

// fp_min_max
template <>
Node RewriteRule<RewriteRuleKind::FP_MIN_EQ>::_apply(Rewriter& rewriter,
                                                     const Node& node);

/* fpmax -------------------------------------------------------------------- */

// fp_min_max
template <>
Node RewriteRule<RewriteRuleKind::FP_MAX_EQ>::_apply(Rewriter& rewriter,
                                                     const Node& node);

/* fpmul -------------------------------------------------------------------- */

// const_ternary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_MUL_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* fpneg -------------------------------------------------------------------- */

// const_unary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_NEG_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// fp_neg
template <>
Node RewriteRule<RewriteRuleKind::FP_NEG_NEG>::_apply(Rewriter& rewriter,
                                                      const Node& node);

/* fprem -------------------------------------------------------------------- */

// const_binary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_REM_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// fp_rem_same_divisor
template <>
Node RewriteRule<RewriteRuleKind::FP_REM_SAME_DIV>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// fp_rem_sign_divisor
template <>
Node RewriteRule<RewriteRuleKind::FP_REM_ABS_NEG>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// fp_rem_neg
template <>
Node RewriteRule<RewriteRuleKind::FP_REM_NEG>::_apply(Rewriter& rewriter,
                                                      const Node& node);

/* fprti -------------------------------------------------------------------- */

// const_binary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_RTI_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* fpsqrt ------------------------------------------------------------------- */

// const_binary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_SQRT_EVAL>::_apply(Rewriter& rewriter,
                                                        const Node& node);

/* to_fp: from_bv ----------------------------------------------------------- */

// const_fp_to_fp_from_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_BV_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);

/* to_fp: from_fp ----------------------------------------------------------- */

// const_fp_to_fp_from_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_FP_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);

/* to_fp: from_sbv ---------------------------------------------------------- */

// const_fp_to_fp_from_sbv_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_SBV_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_SBV_BV1_ELIM>::_apply(
    Rewriter& rewriter, const Node& node);

/* to_fp: from_ubv ---------------------------------------------------------- */

// const_fp_to_fp_from_ubv_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_UBV_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::FP_EQUAL_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::FP_GEQ_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::FP_GT_ELIM>::_apply(Rewriter& rewriter,
                                                      const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::FP_SUB_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* -------------------------------------------------------------------------- */
}  // namespace bzla

#endif
