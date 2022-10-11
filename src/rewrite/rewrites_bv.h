#ifndef BZLA_REWRITE_REWRITES_BV_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BV_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

/* bvadd -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// bool_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_BV1>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// mult_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_MUL_TWO>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// not_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_NOT>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// bcond_add (TODO tbd)

// urem_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_UREM>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// neg_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_NEG>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// zero_add (subsumed by BV_ADD_SPECIAL_CONST)
// const_lhs_add
// const_rhs_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_CONST>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// const_neg_lhs_add (TODO tbd)
// const_neg_rhs_add (TODO tbd)

// push_ite_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_ITE>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// sll_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_SHL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// mul_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_MUL>::_apply(Rewriter& rewriter,
                                                      const Node& node);

/* bvand -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// idem1_and
// contr1_and
// contr2_and
// idem2_and
// comm_and
// bool_xnor_and
// resol1_and
// resol2_and
// lt_false_and
// lt_and
// contr_rec_and
// subsum1_and
// subst1_and
// subst2_and
// subsum2_and
// subst3_and
// subst4_and
// contr3_and
// idem3_and
// const1_and
// const2_and
// concat_and

/* bvashr ------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::BV_ASHR_EVAL>::_apply(Rewriter& rewriter,
                                                        const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::BV_ASHR_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);

/* bvconcat ----------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_CONCAT_EVAL>::_apply(Rewriter& rewriter,
                                                          const Node& node);

// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
// const_concat
// slice_concat
// and_lhs_concat
// and_rhs_concat

/* bvextract ---------------------------------------------------------------- */

// full_slice
// const_slice
// slice_slice
// concat_lower_slice
// concat_upper_slice
// concat_rec_upper_slice
// concat_rec_lower_slice
// concat_rec_slice
// and_slice
// bcond_slice
// zero_lower_slice

/* bvmul -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// bool_mul
#if 0
// this increases mul nodes in the general case
// bcond_mul
#endif
// const_lhs_mul
// const_rhs_mul
// const_mul
// push_ite_mul
// sll_mul
// neg_mul
// ones_mul

/* bvnot -------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::BV_NOT_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_NOT_BV_NOT>::_apply(Rewriter& rewriter,
                                                         const Node& node);

/* bvshl -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_SHL_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_SHL_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// const_sll

/* bvshr -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_SHR_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);

// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_SHR_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// const_srl
// same_srl
// not_same_srl

/* bvslt -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_SLT_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_SLT_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// false_lt
// bool_slt
// concat_lower_slt
// bcond_slt

/* bvudiv ------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_UDIV_EVAL>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_UDIV_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// bool_udiv
// power2_udiv
// one_udiv
// bcond_udiv

/* bvult -------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_ULT_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_ULT_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// false_lt
// bool_ult
// concat_upper_ult
// concat_lower_ult
// bcond_ult

/* bvurem ------------------------------------------------------------------- */

// const_binary_bv_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_UREM_EVAL>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// special_const_lhs_binary_exp
// special_const_rhs_binary_exp
template <>
Node RewriteRule<RewriteRuleKind::BV_UREM_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// bool_urem
// zero_urem

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::BV_NAND_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_NOR_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_OR_ELIM>::_apply(Rewriter& rewriter,
                                                      const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_REDAND_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_REDOR_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_REDXOR_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_REPEAT_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_ROL_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_ROLI_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_ROR_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_RORI_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SADDO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SDIV_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SDIVO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SGE_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SGT_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SIGN_EXTEND_ELIM>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SLE_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SMOD_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SMULO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SREM_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SSUBO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_SUB_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_UADDO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_UGE_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_UGT_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_ULE_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_UMULO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_USUBO_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_XOR_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_ZERO_EXTEND_ELIM>::_apply(
    Rewriter& rewriter, const Node& node);

}  // namespace bzla
#endif
