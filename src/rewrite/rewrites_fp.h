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

/* fpisnan ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NAN_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// fp_tester_sign_ops

/* fpisneg ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NEG_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// fp_tester_sign_ops

/* fpisnorm ----------------------------------------------------------------- */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_NORM_EVAL>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// fp_tester_sign_ops

/* fpispos ------------------------------------------------------------------ */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_POS_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// fp_tester_sign_ops

/* fpissubnorm -------------------------------------------------------------- */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_SUBNORM_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);
// fp_tester_sign_ops

/* fpiszero ----------------------------------------------------------------- */

// const_fp_tester
template <>
Node RewriteRule<RewriteRuleKind::FP_IS_ZERO_EVAL>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// fp_tester_sign_ops

/* fple --------------------------------------------------------------------- */

// const_binary_fp_bool_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_LE_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// fp_lte

/* fplt --------------------------------------------------------------------- */

// const_binary_fp_bool_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_LT_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// fp_lt

/* fpmin -------------------------------------------------------------------- */

// fp_min_max

/* fpmax -------------------------------------------------------------------- */

// fp_min_max

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

/* fprem -------------------------------------------------------------------- */

// const_binary_fp_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_REM_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// fp_rem_same_divisor
// fp_rem_sign_divisor
// fp_rem_neg

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

/* to_fp: from_ubv ---------------------------------------------------------- */

// const_fp_to_fp_from_ubv_exp
template <>
Node RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_UBV_EVAL>::_apply(
    Rewriter& rewriter, const Node& node);

/* -------------------------------------------------------------------------- */
}  // namespace bzla

#endif
