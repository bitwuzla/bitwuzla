/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_REWRITER_H_INCLUDED
#define BZLA_REWRITE_REWRITER_H_INCLUDED

#include <unordered_map>
#ifndef NDEBUG
#include <unordered_set>
#endif

#include "node/node.h"
#include "util/statistics.h"

namespace bzla {

namespace util {
class Logger;
}

class Env;

/* -------------------------------------------------------------------------- */

class Rewriter
{
 public:
  /**
   * Constructor.
   * @param env   The associated environment.
   * @param level The rewriting level; level 0 disables all rewrites
   *              except for operator elimination, level 1 enables one-level
   *              rewrites, level 2 multi-level rewrites.
   */
  Rewriter(Env& env, uint8_t level = 0);

  /**
   * Rewrite given node.
   * @param node The node to rewrite.
   * @return The rewritten node or `node` if no rewrites applied.
   */
  const Node& rewrite(const Node& node);

  /**
   * Create node and apply rewriting.
   * @param kind     The kind of the node to create.
   * @param children The children of the node to create.
   * @param indices  The indices of the node to create.
   * @return The created, rewritten node.
   */
  const Node& mk_node(node::Kind kind,
                      const std::vector<Node>& children,
                      const std::vector<uint64_t>& indices = {});

  /**
   * Helper to create an inverted Boolean or bit-vector node.
   * @param node The node to invert.
   * @return The inverted node.
   */
  const Node& invert_node(const Node& node);
  /**
   * Helper to conditionally create an inverted Boolean or bit-vector node.
   * @param condition True to invert the given node.
   * @param node The node to invert.
   * @return The inverted node.
   */
  const Node& invert_node_if(bool condition, const Node& node);

  /**
   * @return True if given node corresponds to a (rewritten) OR node.
   * @param node   The node to check.
   * @param child0 The (resulting) first child of the extracted or node.
   * @param child1 The (resulting) second child of the extracted or node.
   */
  bool is_or(const Node& node, Node& child0, Node& child1);
  /**
   * @return True if given node corresponds to a (rewritten) XOR node.
   * @param node   The node to check.
   * @param child0 The (resulting) first child of the extracted xor node.
   * @param child1 The (resulting) second child of the extracted xor node.
   */
  bool is_xor(const Node& node, Node& child0, Node& child1);
  /**
   * @return True if given node corresponds to a (rewritten) XNOR node.
   * @param node   The node to check.
   * @param child0 The (resulting) first child of the extracted xnor node.
   * @param child1 The (resulting) second child of the extracted xnor node.
   */
  bool is_xnor(const Node& node, Node& child0, Node& child1);

  /**
   * @return True if given node corresponds to a (rewritten) BV_NEG node.
   * @param node  The node to check.
   * @param child The (resulting) child of the extracted bvneg node.
   */
  bool is_bv_neg(const Node& node, Node& child);
  /**
   * @return True if given node corresponds to a (rewritten) BV_OR node.
   * @param node   The node to check.
   * @param child0 The (resulting) first child of the extracted bvor node.
   * @param child1 The (resulting) second child of the extracted bvor node.
   */
  bool is_bv_or(const Node& node, Node& child0, Node& child1);
  /**
   * @return True if given node corresponds to a (rewritten) BV_OR node.
   * @param node   The node to check.
   * @param child0 The (resulting) first child of the extracted bvsub node.
   * @param child1 The (resulting) second child of the extracted bvsub node.
   */
  bool is_bv_sub(const Node& node, Node& child0, Node& child1);
  /**
   * @return True if given node corresponds to a (rewritten) BV_XNOR node.
   * @param node   The node to check.
   * @param child0 The (resulting) first child of the extracted bvxnor node.
   * @param child1 The (resulting) second child of the extracted bvxnor node.
   */
  bool is_bv_xnor(const Node& node, Node& child0, Node& child1);

  /** Clear rewrite cache. */
  void clear_cache();

 private:
  /** The limit for recursive calls to _rewrite(). */
  static constexpr uint64_t RECURSION_LIMIT = 4096;

  const Node& _rewrite(const Node& node);

  /* Core ---------------------------------------- */
  Node rewrite_eq(const Node& node);
  Node rewrite_ite(const Node& node);
  /* Eliminated operators */
  Node rewrite_distinct(const Node& node);

  /* Boolean ------------------------------------- */
  Node rewrite_and(const Node& node);
  Node rewrite_not(const Node& node);
  /* Eliminated operators */
  Node rewrite_implies(const Node& node);
  Node rewrite_or(const Node& node);
  Node rewrite_xor(const Node& node);

  /* BV ------------------------------------------ */
  Node rewrite_bv_add(const Node& node);
  Node rewrite_bv_and(const Node& node);
  Node rewrite_bv_ashr(const Node& node);
  Node rewrite_bv_concat(const Node& node);
  Node rewrite_bv_dec(const Node& node);
  Node rewrite_bv_extract(const Node& node);
  Node rewrite_bv_inc(const Node& node);
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
  Node rewrite_bv_nego(const Node& node);
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
  Node rewrite_bv_comp(const Node& node);

  /* FP ------------------------------------------ */
  Node rewrite_fp_abs(const Node& node);
  Node rewrite_fp_add(const Node& node);
  Node rewrite_fp_div(const Node& node);
  Node rewrite_fp_equal(const Node& node);
  Node rewrite_fp_fma(const Node& node);
  Node rewrite_fp_fp(const Node& node);
  Node rewrite_fp_gt(const Node& node);
  Node rewrite_fp_geq(const Node& node);
  Node rewrite_fp_is_inf(const Node& node);
  Node rewrite_fp_is_nan(const Node& node);
  Node rewrite_fp_is_neg(const Node& node);
  Node rewrite_fp_is_normal(const Node& node);
  Node rewrite_fp_is_pos(const Node& node);
  Node rewrite_fp_is_subnormal(const Node& node);
  Node rewrite_fp_is_zero(const Node& node);
  Node rewrite_fp_leq(const Node& node);
  Node rewrite_fp_lt(const Node& node);
  Node rewrite_fp_max(const Node& node);
  Node rewrite_fp_min(const Node& node);
  Node rewrite_fp_mul(const Node& node);
  Node rewrite_fp_neg(const Node& node);
  Node rewrite_fp_rem(const Node& node);
  Node rewrite_fp_rti(const Node& node);
  Node rewrite_fp_sqrt(const Node& node);
  Node rewrite_fp_sub(const Node& node);
  Node rewrite_fp_to_fp_from_bv(const Node& node);
  Node rewrite_fp_to_fp_from_fp(const Node& node);
  Node rewrite_fp_to_fp_from_sbv(const Node& node);
  Node rewrite_fp_to_fp_from_ubv(const Node& node);

  /* Array --------------------------------------- */
  Node rewrite_select(const Node& node);
  Node rewrite_store(const Node& node);

  /* Fun ----------------------------------------- */
  Node rewrite_apply(const Node& node);
  Node rewrite_lambda(const Node& node);

  /* Quant --------------------------------------- */
  Node rewrite_forall(const Node& node);
  Node rewrite_exists(const Node& node);

  /* Normalization */
  Node normalize_commutative(const Node& node);

  /** Associated environment. */
  Env& d_env;
  /** Logger instance */
  util::Logger& d_logger;

  /** True to enable rewriting, false to only enable operator elimination. */
  uint8_t d_level;
  /** Cache for rewritten nodes, maps node to its rewritten form. */
  std::unordered_map<Node, Node> d_cache;
#ifndef NDEBUG
  /** Cache for detecting rewrite cycles in debug mode. */
  std::unordered_set<Node> d_rec_cache;
  /** Counter for new nodes created during rewriting. */
  uint64_t d_num_nodes = 0;
#endif
  uint64_t d_num_rec_calls = 0;
  /** Indicates whether rewrite recursion limit was reached. */
  bool d_recursion_limit_reached = false;
  util::HistogramStatistic& d_stats_rewrites;
};

/* -------------------------------------------------------------------------- */

enum class RewriteRuleKind
{
  /* Boolean rewrites ---------------------------- */

  // Level 1+
  AND_EVAL,
  AND_SPECIAL_CONST,
  AND_CONST,
  AND_IDEM1,
  AND_IDEM2,
  AND_IDEM3,
  AND_CONTRA1,
  AND_CONTRA2,
  AND_CONTRA3,
  AND_RESOL1,
  AND_SUBSUM1,
  AND_SUBSUM2,
  AND_NOT_AND1,
  AND_NOT_AND2,
  AND_BV_LT_FALSE,
  AND_BV_LT,

  // Level 1+
  EQUAL_EVAL,
  EQUAL_SPECIAL_CONST,
  EQUAL_CONST,
  EQUAL_EQUAL_CONST_BV1,
  EQUAL_TRUE,
  EQUAL_ITE,
  EQUAL_FALSE,
  EQUAL_INV,
  EQUAL_CONST_BV_ADD,
  EQUAL_CONST_BV_MUL,
  EQUAL_CONST_BV_NOT,
  // Level 2+
  EQUAL_BV_ADD,
  EQUAL_BV_ADD_ADD,
  EQUAL_BV_CONCAT,
  EQUAL_BV_SUB,
  EQUAL_ITE_SAME,
  EQUAL_ITE_INVERTED,
  EQUAL_ITE_DIS_BV1,
  EQUAL_ITE_LIFT_COND,

  // Level 1+
  ITE_EVAL,
  ITE_SAME,
  ITE_THEN_ITE1,
  ITE_THEN_ITE2,
  ITE_THEN_ITE3,
  ITE_ELSE_ITE1,
  ITE_ELSE_ITE2,
  ITE_ELSE_ITE3,
  ITE_BOOL,
  // Level 2+
  ITE_BV_CONCAT,
  ITE_BV_OP,

  // Level 1+
  NOT_EVAL,
  NOT_NOT,
  NOT_XOR,

  // Level 0+
  DISTINCT_ELIM,
  // Level 1+
  DISTINCT_CARD,

  // Level 1+
  NORMALIZE_COMM,

  //// Elimination rules
  // Level 0+
  IMPLIES_ELIM,
  OR_ELIM,
  XOR_ELIM,

  /* BV rewrites --------------------------------- */

  //// bvadd
  // Level 1+
  BV_ADD_EVAL,
  BV_ADD_SPECIAL_CONST,
  BV_ADD_CONST,
  BV_ADD_BV1,
  BV_ADD_SAME,
  BV_ADD_NOT,
  BV_ADD_NEG,
  BV_ADD_UREM,
  // Level 2+
  BV_ADD_ITE1,
  BV_ADD_ITE2,
  BV_ADD_MUL1,
  BV_ADD_MUL2,
  BV_ADD_SHL,
  // normalization
  BV_ADD_NORM_MUL_CONST,

  //// bvand
  // Level 1+
  BV_AND_EVAL,
  BV_AND_SPECIAL_CONST,
  BV_AND_CONST,
  BV_AND_IDEM1,
  BV_AND_IDEM2,
  BV_AND_IDEM3,
  BV_AND_CONTRA1,
  BV_AND_CONTRA2,
  BV_AND_CONTRA3,
  BV_AND_SUBSUM1,
  BV_AND_SUBSUM2,
  BV_AND_RESOL1,
  BV_AND_NOT_AND1,
  BV_AND_NOT_AND2,
  BV_AND_CONCAT,

  //// bvashr
  // Level 1+
  BV_ASHR_EVAL,
  BV_ASHR_SPECIAL_CONST,

  //// bvconcat
  // Level 1+
  BV_CONCAT_EVAL,
  BV_CONCAT_CONST,
  BV_CONCAT_EXTRACT,
  // Level 2+
  BV_CONCAT_AND,

  //// bvextract
  // Level 1+
  BV_EXTRACT_EVAL,
  BV_EXTRACT_FULL,
  BV_EXTRACT_EXTRACT,
  // Level 1
  BV_EXTRACT_CONCAT_FULL_LHS,
  BV_EXTRACT_CONCAT_FULL_RHS,
  // Level 2+
  BV_EXTRACT_CONCAT_LHS_RHS,
  BV_EXTRACT_CONCAT,
  BV_EXTRACT_AND,
  BV_EXTRACT_ITE,
  BV_EXTRACT_ADD_MUL,

  //// bvmul
  // Level 1+
  BV_MUL_EVAL,
  BV_MUL_SPECIAL_CONST,
  BV_MUL_CONST,
  BV_MUL_BV1,
  // Level 2+
  BV_MUL_CONST_ADD,
  BV_MUL_ITE,
  BV_MUL_NEG,
  BV_MUL_ONES,
  BV_MUL_SHL,

  //// bvnot
  // Level 1+
  BV_NOT_EVAL,
  BV_NOT_BV_NOT,
  // Level 2+
  BV_NOT_BV_NEG,
  BV_NOT_BV_CONCAT,

  //// bvshl
  // Level 1+
  BV_SHL_EVAL,
  BV_SHL_SPECIAL_CONST,
  BV_SHL_CONST,

  //// bvlshr
  // Level 1+
  BV_SHR_EVAL,
  BV_SHR_SPECIAL_CONST,
  BV_SHR_CONST,
  BV_SHR_SAME,
  BV_SHR_NOT,

  //// bvslt
  // Level 1+
  BV_SLT_EVAL,
  BV_SLT_SPECIAL_CONST,
  BV_SLT_SAME,
  BV_SLT_BV1,
  BV_SLT_ITE,
  // Level 2+
  BV_SLT_CONCAT,

  //// bvudiv
  // Level 1+
  BV_UDIV_EVAL,
  BV_UDIV_SPECIAL_CONST,
  BV_UDIV_BV1,
  BV_UDIV_SAME,
  BV_UDIV_POW2,
  // Level 2+
  BV_UDIV_ITE,

  //// bvult
  // Level 1+
  BV_ULT_EVAL,
  BV_ULT_SPECIAL_CONST,
  BV_ULT_SAME,
  BV_ULT_BV1,
  BV_ULT_ITE,
  // Level 2+
  BV_ULT_CONCAT,

  //// bvurem
  // Level 1+
  BV_UREM_EVAL,
  BV_UREM_SPECIAL_CONST,
  BV_UREM_BV1,
  BV_UREM_SAME,

  //// bvxor
  // Level 1+
  BV_XOR_EVAL,
  BV_XOR_SAME,
  BV_XOR_SPECIAL_CONST,

  //// Elimination rules
  // Level 1+
  BV_DEC_ELIM,
  BV_INC_ELIM,
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
  BV_NEGO_ELIM,
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
  BV_COMP_ELIM,

  /* FP rewrites --------------------------------- */

  //// fp.abs
  // Level 1+
  FP_ABS_EVAL,
  FP_ABS_ABS_NEG,

  //// fp.add
  // Level 1+
  FP_ADD_EVAL,

  //// fp.div
  // Level 1+
  FP_DIV_EVAL,

  //// fp.fma
  // Level 1+
  FP_FMA_EVAL,

  //// fp.isInfinite
  // Level 1+
  FP_IS_INF_EVAL,
  FP_IS_INF_ABS_NEG,

  //// fp.isNaN
  // Level 1+
  FP_IS_NAN_EVAL,
  FP_IS_NAN_ABS_NEG,

  //// fp.isNeg
  // Level 1+
  FP_IS_NEG_EVAL,

  //// fp.isNormal
  // Level 1+
  FP_IS_NORM_EVAL,
  FP_IS_NORM_ABS_NEG,

  //// fp.isPos
  // Level 1+
  FP_IS_POS_EVAL,

  //// fp.isSubnormal
  // Level 1+
  FP_IS_SUBNORM_EVAL,
  FP_IS_SUBNORM_ABS_NEG,

  //// fp.isZero
  // Level 1+
  FP_IS_ZERO_EVAL,
  FP_IS_ZERO_ABS_NEG,

  // Level 1+
  FP_LEQ_EVAL,
  FP_LEQ_EQ,

  //// fp.lt
  // Level 1+
  FP_LT_EVAL,
  FP_LT_EQ,

  //// fp.min
  // Level 1+
  FP_MIN_EVAL,
  FP_MIN_EQ,

  //// fp.max
  // Level 1+
  FP_MAX_EVAL,
  FP_MAX_EQ,

  //// fp.mul
  // Level 1+
  FP_MUL_EVAL,

  //// fp.neg
  // Level 1+
  FP_NEG_EVAL,
  FP_NEG_NEG,

  //// fp.rem
  // Level 1+
  FP_REM_EVAL,
  FP_REM_SAME_DIV,
  FP_REM_ABS_NEG,
  FP_REM_NEG,

  //// fp.roundToIntegral
  // Level 1+
  FP_RTI_EVAL,

  //// fp.sqrt
  // Level 1+
  FP_SQRT_EVAL,

  //// to_fp
  // Level 1+
  FP_TO_FP_FROM_BV_EVAL,
  FP_TO_FP_FROM_FP_EVAL,
  FP_TO_FP_FROM_SBV_EVAL,
  FP_TO_FP_FROM_SBV_BV1_ELIM,

  //// to_fp_unsigned
  // Level 1+
  FP_TO_FP_FROM_UBV_EVAL,

  //// Elimination rules
  // Level 0+
  FP_EQUAL_ELIM,
  FP_FP_ELIM,
  FP_GEQ_ELIM,
  FP_GT_ELIM,
  FP_SUB_ELIM,

  /* Array rewrites ---------------------------- */

  //// select
  // Level 1+
  ARRAY_PROP_SELECT,

  /* Quantifier rewrites*/
  EXISTS_ELIM,
};

std::ostream& operator<<(std::ostream& out, RewriteRuleKind kind);

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
