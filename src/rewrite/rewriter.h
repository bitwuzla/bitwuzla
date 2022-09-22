#ifndef BZLA_REWRITE_REWRITER_H_INCLUDED
#define BZLA_REWRITE_REWRITER_H_INCLUDED

#include <unordered_map>

#include "node/node.h"

namespace bzla {

/* -------------------------------------------------------------------------- */

class Rewriter
{
 public:
  const Node& rewrite(const Node& node);

 private:
  Node _rewrite(const Node& node);

  Node rewrite_eq(const Node& node);
  Node rewrite_ite(const Node& node);

  Node rewrite_bv_add(const Node& node);
  Node rewrite_bv_and(const Node& node);
  Node rewrite_bv_ashr(const Node& node);
  Node rewrite_bv_concat(const Node& node);
  Node rewrite_bv_extract(const Node& node);
  Node rewrite_bv_mul(const Node& node);
  Node rewrite_bv_shl(const Node& node);
  Node rewrite_bv_shr(const Node& node);
  Node rewrite_bv_slt(const Node& node);
  Node rewrite_bv_udiv(const Node& node);
  Node rewrite_bv_ult(const Node& node);
  Node rewrite_bv_urem(const Node& node);

  Node rewrite_fp_abs(const Node& node);
  Node rewrite_fp_add(const Node& node);
  Node rewrite_fp_div(const Node& node);
  Node rewrite_fp_is_inf(const Node& node);
  Node rewrite_fp_is_nan(const Node& node);
  Node rewrite_fp_is_neg(const Node& node);
  Node rewrite_fp_is_normal(const Node& node);
  Node rewrite_fp_is_pos(const Node& node);
  Node rewrite_fp_is_subnormal(const Node& node);
  Node rewrite_fp_is_zero(const Node& node);
  Node rewrite_fp_le(const Node& node);
  Node rewrite_fp_lt(const Node& node);
  Node rewrite_fp_max(const Node& node);
  Node rewrite_fp_min(const Node& node);
  Node rewrite_fp_mul(const Node& node);
  Node rewrite_fp_neg(const Node& node);
  Node rewrite_fp_rem(const Node& node);
  Node rewrite_fp_rti(const Node& node);
  Node rewrite_fp_sqrt(const Node& node);
  Node rewrite_fp_to_fp_from_bv(const Node& node);
  Node rewrite_fp_to_fp_from_fp(const Node& node);
  Node rewrite_fp_to_fp_from_sbv(const Node& node);
  Node rewrite_fp_to_fp_from_ubv(const Node& node);

  Node rewrite_apply(const Node& node);
  Node rewrite_lambda(const Node& node);

  Node rewrite_forall(const Node& node);
  Node rewrite_exists(const Node& node);

  std::unordered_map<Node, Node> d_cache;
};

/* -------------------------------------------------------------------------- */

enum class RewriteRuleKind
{
  BV_ADD_EVAL,
  BV_AND_EVAL,
  BV_ASHR_EVAL,
  BV_CONCAT_EVAL,
  BV_MUL_EVAL,
  BV_SHL_EVAL,
  BV_SHR_EVAL,
  BV_SLT_EVAL,
  BV_UDIV_EVAL,
  BV_ULT_EVAL,
  BV_UREM_EVAL,

  FP_ABS_EVAL,
  FP_ADD_EVAL,
  FP_DIV_EVAL,
  FP_IS_INF_EVAL,
  FP_IS_NAN_EVAL,
  FP_IS_NEG_EVAL,
  FP_IS_NORM_EVAL,
  FP_IS_POS_EVAL,
  FP_IS_SUBNORM_EVAL,
  FP_IS_ZERO_EVAL,
  FP_LE_EVAL,
  FP_LT_EVAL,
  FP_MIN_EVAL,
  FP_MAX_EVAL,
  FP_MUL_EVAL,
  FP_NEG_EVAL,
  FP_REM_EVAL,
  FP_RTI_EVAL,
  FP_SQRT_EVAL,
  FP_TO_FP_FROM_BV_EVAL,
  FP_TO_FP_FROM_FP_EVAL,
  FP_TO_FP_FROM_SBV_EVAL,
  FP_TO_FP_FROM_UBV_EVAL,

};

template <RewriteRuleKind K>
class RewriteRule
{
 public:
  static std::pair<Node, RewriteRuleKind> apply(Rewriter& rewriter,
                                                const Node& node)
  {
    return std::make_pair(_apply(rewriter, node), K);
  }

 private:
  static Node _apply(Rewriter& rewriter, const Node& node);
};

/* -------------------------------------------------------------------------- */

}  // namespace bzla

#endif
