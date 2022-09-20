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

}  // namespace bzla

/* -------------------------------------------------------------------------- */

#endif
