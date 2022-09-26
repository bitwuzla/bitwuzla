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

  const Node& mk_node(node::Kind kind,
                      const std::vector<Node>& children,
                      const std::vector<uint64_t>& indices = {});

 private:
  const Node& _rewrite(const Node& node);

  Node rewrite_and(const Node& node);
  Node rewrite_not(const Node& node);
  Node rewrite_or(const Node& node);

  Node rewrite_eq(const Node& node);
  Node rewrite_ite(const Node& node);

  Node rewrite_bv_add(const Node& node);
  Node rewrite_bv_and(const Node& node);
  Node rewrite_bv_ashr(const Node& node);
  Node rewrite_bv_concat(const Node& node);
  Node rewrite_bv_extract(const Node& node);
  Node rewrite_bv_mul(const Node& node);
  Node rewrite_bv_not(const Node& node);
  Node rewrite_bv_shl(const Node& node);
  Node rewrite_bv_shr(const Node& node);
  Node rewrite_bv_slt(const Node& node);
  Node rewrite_bv_udiv(const Node& node);
  Node rewrite_bv_ult(const Node& node);
  Node rewrite_bv_urem(const Node& node);

  /* Eliminated operators */
  Node rewrite_bv_nand(const Node& node);
  Node rewrite_bv_neg(const Node& node);
  Node rewrite_bv_nor(const Node& node);
  Node rewrite_bv_or(const Node& node);
  Node rewrite_bv_redand(const Node& node);
  Node rewrite_bv_redor(const Node& node);
  Node rewrite_bv_redxor(const Node& node);
  Node rewrite_bv_repeat(const Node& node);
  Node rewrite_bv_rol(const Node& node);
  Node rewrite_bv_roli(const Node& node);
  Node rewrite_bv_ror(const Node& node);
  Node rewrite_bv_rori(const Node& node);
  Node rewrite_bv_saddo(const Node& node);
  Node rewrite_bv_sdiv(const Node& node);
  Node rewrite_bv_sdivo(const Node& node);
  Node rewrite_bv_sge(const Node& node);
  Node rewrite_bv_sgt(const Node& node);
  Node rewrite_bv_sign_extend(const Node& node);
  Node rewrite_bv_sle(const Node& node);
  Node rewrite_bv_smod(const Node& node);
  // Node rewrite_bv_smulo(const Node& node);
  Node rewrite_bv_srem(const Node& node);
  Node rewrite_bv_ssubo(const Node& node);
  Node rewrite_bv_sub(const Node& node);
  Node rewrite_bv_uaddo(const Node& node);
  Node rewrite_bv_uge(const Node& node);
  Node rewrite_bv_ugt(const Node& node);
  Node rewrite_bv_ule(const Node& node);
  // Node rewrite_bv_umulo(const Node& node);
  Node rewrite_bv_usubo(const Node& node);
  Node rewrite_bv_xnor(const Node& node);
  Node rewrite_bv_xor(const Node& node);
  Node rewrite_bv_zero_extend(const Node& node);

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
  AND_EVAL,
  NOT_EVAL,

  OR_ELIM,

  /* BV rewrites --------------------------------- */

  BV_ADD_EVAL,
  BV_ADD_SPECIAL_CONST,

  BV_AND_EVAL,
  BV_AND_SPECIAL_CONST,

  BV_ASHR_EVAL,
  BV_ASHR_SPECIAL_CONST,

  BV_CONCAT_EVAL,

  BV_MUL_EVAL,
  BV_MUL_SPECIAL_CONST,

  BV_NOT_EVAL,

  BV_SHL_EVAL,
  BV_SHL_SPECIAL_CONST,

  BV_SHR_EVAL,
  BV_SHR_SPECIAL_CONST,

  BV_SLT_EVAL,

  BV_UDIV_EVAL,
  BV_UDIV_SPECIAL_CONST,

  BV_ULT_EVAL,

  BV_UREM_EVAL,
  BV_UREM_SPECIAL_CONST,

  BV_NAND_ELIM,
  BV_NEG_ELIM,
  BV_NOR_ELIM,
  BV_OR_ELIM,
  BV_REDAND_ELIM,
  BV_REDOR_ELIM,
  BV_REDXOR_ELIM,
  BV_REPEAT_ELIM,
  BV_ROL_ELIM,
  BV_ROLI_ELIM,
  BV_ROR_ELIM,
  BV_RORI_ELIM,
  BV_SADDO_ELIM,
  BV_SDIV_ELIM,
  BV_SDIVO_ELIM,
  BV_SGE_ELIM,
  BV_SGT_ELIM,
  BV_SIGN_EXTEND_ELIM,
  BV_SLE_ELIM,
  BV_SMOD_ELIM,
  // BV_SMULO_ELIM,
  BV_SREM_ELIM,
  BV_SSUBO_ELIM,
  BV_SUB_ELIM,
  BV_UADDO_ELIM,
  BV_UGE_ELIM,
  BV_UGT_ELIM,
  BV_ULE_ELIM,
  // BV_UMULO_ELIM,
  BV_USUBO_ELIM,
  BV_XNOR_ELIM,
  BV_XOR_ELIM,
  BV_ZERO_EXTEND_ELIM,

  /* FP rewrites --------------------------------- */

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
