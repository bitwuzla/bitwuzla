#ifndef BZLA_REWRITE_REWRITER_H_INCLUDED
#define BZLA_REWRITE_REWRITER_H_INCLUDED

#include <unordered_map>

#include "node/node.h"

namespace bzla {

/* -------------------------------------------------------------------------- */

class Rewriter
{
 public:
  /**
   * Constructor.
   * @param enabled True to enable rewriting, false to disable all rewrites
   *                except for operator elimination.
   */
  Rewriter(bool enabled = true) : d_enabled(enabled) {}

  const Node& rewrite(const Node& node);

  const Node& mk_node(node::Kind kind,
                      const std::vector<Node>& children,
                      const std::vector<uint64_t>& indices = {});

  /**
   * Helper to create an inverted Boolean or bit-vector node.
   * @param node The node to invert.
   * @return The inverted node.
   */
  Node invert_node(const Node& node);

 private:
  const Node& _rewrite(const Node& node);

  /* Boolean ------------------------------------- */
  Node rewrite_and(const Node& node);
  Node rewrite_not(const Node& node);
  Node rewrite_eq(const Node& node);
  Node rewrite_ite(const Node& node);
  /* Eliminated operators */
  Node rewrite_distinct(const Node& node);
  Node rewrite_implies(const Node& node);
  Node rewrite_or(const Node& node);
  Node rewrite_xor(const Node& node);

  /* BV ------------------------------------------ */
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
  Node rewrite_bv_xor(const Node& node);
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
  Node rewrite_bv_smulo(const Node& node);
  Node rewrite_bv_srem(const Node& node);
  Node rewrite_bv_ssubo(const Node& node);
  Node rewrite_bv_sub(const Node& node);
  Node rewrite_bv_uaddo(const Node& node);
  Node rewrite_bv_uge(const Node& node);
  Node rewrite_bv_ugt(const Node& node);
  Node rewrite_bv_ule(const Node& node);
  Node rewrite_bv_umulo(const Node& node);
  Node rewrite_bv_usubo(const Node& node);
  Node rewrite_bv_xnor(const Node& node);
  Node rewrite_bv_zero_extend(const Node& node);

  /* FP ------------------------------------------ */
  Node rewrite_fp_abs(const Node& node);
  Node rewrite_fp_add(const Node& node);
  Node rewrite_fp_div(const Node& node);
  Node rewrite_fp_equal(const Node& node);
  Node rewrite_fp_gt(const Node& node);
  Node rewrite_fp_ge(const Node& node);
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

  /* Fun ----------------------------------------- */
  Node rewrite_apply(const Node& node);
  Node rewrite_lambda(const Node& node);

  /* Quant --------------------------------------- */
  Node rewrite_forall(const Node& node);
  Node rewrite_exists(const Node& node);

  /** True to enable rewriting, false to only enable operator elimination. */
  bool d_enabled;
  /** Cache for rewritten nodes, maps node to its rewritten form. */
  std::unordered_map<Node, Node> d_cache;
};

/* -------------------------------------------------------------------------- */

enum class RewriteRuleKind
{
  /* Boolean rewrites ---------------------------- */

  AND_EVAL,

  EQUAL_EVAL,
  EQUAL_SPECIAL_CONST,

  NOT_EVAL,

  DISTINCT_CARD,
  DISTINCT_ELIM,

  //// Elimination rules
  IMPLIES_ELIM,
  OR_ELIM,
  XOR_ELIM,

  /* BV rewrites --------------------------------- */

  //// bvadd
  BV_ADD_EVAL,
  BV_ADD_SPECIAL_CONST,
  BV_ADD_CONST,
  BV_ADD_BV1,
  BV_ADD_SAME,
  BV_ADD_NOT,
  BV_ADD_NEG,
  BV_ADD_UREM,
  // Level 3
  BV_ADD_ITE,
  BV_ADD_MUL,
  BV_ADD_SHL,

  //// bvand
  BV_AND_EVAL,
  BV_AND_SPECIAL_CONST,

  //// bvashr
  BV_ASHR_EVAL,
  BV_ASHR_SPECIAL_CONST,

  //// bvconcat
  BV_CONCAT_EVAL,
  BV_CONCAT_CONST,
  // Level 1
  BV_CONCAT_EXTRACT,
  // Level 3
  BV_CONCAT_AND,

  //// bvextract
  BV_EXTRACT_EVAL,
  BV_EXTRACT_FULL,
  BV_EXTRACT_EXTRACT,
  BV_EXTRACT_CONCAT_FULL_RHS,
  // Level 0-2
  BV_EXTRACT_CONCAT_FULL_LHS,
  // Level 3
  BV_EXTRACT_CONCAT_LSH_RHS,
  BV_EXTRACT_CONCAT,
  BV_EXTRACT_AND,
  BV_EXTRACT_ITE,
  BV_EXTRACT_ADD_MUL,

  //// bvmul
  BV_MUL_EVAL,
  BV_MUL_SPECIAL_CONST,
  BV_MUL_CONST,
  BV_MUL_BV1,
  // Level 3
  BV_MUL_CONST_ADD,
  BV_MUL_ITE,
  BV_MUL_NEG,
  BV_MUL_ONES,
  BV_MUL_SHL,

  //// bvnot
  BV_NOT_EVAL,
  BV_NOT_BV_NOT,

  //// bvshl
  BV_SHL_EVAL,
  BV_SHL_SPECIAL_CONST,
  BV_SHL_CONST,

  //// bvlshr
  BV_SHR_EVAL,
  BV_SHR_SPECIAL_CONST,
  BV_SHR_CONST,
  BV_SHR_SAME,
  BV_SHR_NOT,

  //// bvslt
  BV_SLT_EVAL,
  BV_SLT_SPECIAL_CONST,
  BV_SLT_SAME,
  BV_SLT_BV1,
  BV_SLT_ITE,
  // Level 3
  BV_SLT_CONCAT,

  //// bvudiv
  BV_UDIV_EVAL,
  BV_UDIV_SPECIAL_CONST,
  BV_UDIV_BV1,
  BV_UDIV_SAME,
  BV_UDIV_POW2,

  //// bvult
  BV_ULT_EVAL,
  BV_ULT_SPECIAL_CONST,
  BV_ULT_SAME,
  BV_ULT_BV1,
  BV_ULT_ITE,
  // Level 3
  BV_ULT_CONCAT,

  //// bvurem
  BV_UREM_EVAL,
  BV_UREM_SPECIAL_CONST,
  BV_UREM_BV1,
  BV_UREM_SAME,

  //// bvxor
  BV_XOR_EVAL,

  //// Elimination rules
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
  BV_SMULO_ELIM,
  BV_SREM_ELIM,
  BV_SSUBO_ELIM,
  BV_SUB_ELIM,
  BV_UADDO_ELIM,
  BV_UGE_ELIM,
  BV_UGT_ELIM,
  BV_ULE_ELIM,
  BV_UMULO_ELIM,
  BV_USUBO_ELIM,
  BV_XNOR_ELIM,
  BV_XOR_ELIM,
  BV_ZERO_EXTEND_ELIM,

  /* FP rewrites --------------------------------- */

  FP_ABS_EVAL,
  FP_ABS_ABS_NEG,

  FP_ADD_EVAL,
  FP_DIV_EVAL,

  FP_IS_INF_EVAL,
  FP_IS_INF_ABS_NEG,

  FP_IS_NAN_EVAL,
  FP_IS_NAN_ABS_NEG,

  FP_IS_NEG_EVAL,

  FP_IS_NORM_EVAL,
  FP_IS_NORM_ABS_NEG,

  FP_IS_POS_EVAL,

  FP_IS_SUBNORM_EVAL,
  FP_IS_SUBNORM_ABS_NEG,

  FP_IS_ZERO_EVAL,
  FP_IS_ZERO_ABS_NEG,

  FP_LE_EVAL,
  FP_LE_EQ,

  FP_LT_EVAL,
  FP_LT_EQ,

  FP_MIN_EVAL,
  FP_MIN_EQ,

  FP_MAX_EVAL,
  FP_MAX_EQ,

  FP_MUL_EVAL,

  FP_NEG_EVAL,
  FP_NEG_NEG,

  FP_REM_EVAL,
  FP_REM_SAME_DIV,
  FP_REM_ABS_NEG,
  FP_REM_NEG,

  FP_RTI_EVAL,
  FP_SQRT_EVAL,
  FP_TO_FP_FROM_BV_EVAL,
  FP_TO_FP_FROM_FP_EVAL,
  FP_TO_FP_FROM_SBV_EVAL,
  FP_TO_FP_FROM_UBV_EVAL,

  //// Elimination rules
  FP_GE_ELIM,
  FP_GT_ELIM,
  FP_EQUAL_ELIM,
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
