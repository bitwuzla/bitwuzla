/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
Node RewriteRule<RewriteRuleKind::BV_ADD_SAME>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// not_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_NOT>::_apply(Rewriter& rewriter,
                                                      const Node& node);
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
// bcond_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_ITE1>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// push_ite_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_ITE2>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// sll_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_SHL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// mul_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_MUL1>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// add_mul_distrib
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_MUL2>::_apply(Rewriter& rewriter,
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
// const1_and
// const2_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_CONST>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// idem1_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_IDEM1>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// idem2_and
// comm_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_IDEM2>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// idem3_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_IDEM3>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// contr1_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_CONTRA1>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// contr2_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_CONTRA2>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// contr3_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_CONTRA3>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// subsum1_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_SUBSUM1>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// subsum2_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_SUBSUM2>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// resol1_and
// resol2_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_RESOL1>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// subst1_and
// subst2_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_NOT_AND1>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// subst3_and
// subst4_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_NOT_AND2>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// concat_and
template <>
Node RewriteRule<RewriteRuleKind::BV_AND_CONCAT>::_apply(Rewriter& rewriter,
                                                         const Node& node);

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
// const_concat
template <>
Node RewriteRule<RewriteRuleKind::BV_CONCAT_CONST>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// slice_concat
template <>
Node RewriteRule<RewriteRuleKind::BV_CONCAT_EXTRACT>::_apply(Rewriter& rewriter,
                                                             const Node& node);
// and_lhs_concat
// and_rhs_concat
template <>
Node RewriteRule<RewriteRuleKind::BV_CONCAT_AND>::_apply(Rewriter& rewriter,
                                                         const Node& node);

/* bvextract ---------------------------------------------------------------- */

// const_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_EVAL>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// full_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_FULL>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// slice_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_EXTRACT>::_apply(
    Rewriter& rewriter, const Node& node);
// concat_lower_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_CONCAT_FULL_RHS>::_apply(
    Rewriter& rewriter, const Node& node);
// concat_upper_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_CONCAT_FULL_LHS>::_apply(
    Rewriter& rewriter, const Node& node);
// concat_rec_upper_slice
// concat_rec_lower_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_CONCAT_LHS_RHS>::_apply(
    Rewriter& rewriter, const Node& node);
// concat_rec_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_CONCAT>::_apply(Rewriter& rewriter,
                                                             const Node& node);
// and_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_AND>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// bcond_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_ITE>::_apply(Rewriter& rewriter,
                                                          const Node& node);
// zero_lower_slice
template <>
Node RewriteRule<RewriteRuleKind::BV_EXTRACT_ADD_MUL>::_apply(
    Rewriter& rewriter, const Node& node);

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
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_BV1>::_apply(Rewriter& rewriter,
                                                      const Node& node);
#if 0
// this increases mul nodes in the general case
// bcond_mul (TODO tbd)
#endif
// const_lhs_mul
// const_rhs_mul
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_CONST>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// const_mul
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_CONST_ADD>::_apply(Rewriter& rewriter,
                                                            const Node& node);
// push_ite_mul
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_ITE>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// sll_mul
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_SHL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// neg_mul
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_NEG>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// ones_mul
template <>
Node RewriteRule<RewriteRuleKind::BV_MUL_ONES>::_apply(Rewriter& rewriter,
                                                       const Node& node);

/* bvnot -------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::BV_NOT_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::BV_NOT_BV_NOT>::_apply(Rewriter& rewriter,
                                                         const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::BV_NOT_BV_NEG>::_apply(Rewriter& rewriter,
                                                         const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_NOT_BV_CONCAT>::_apply(Rewriter& rewriter,
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
template <>
Node RewriteRule<RewriteRuleKind::BV_SHL_CONST>::_apply(Rewriter& rewriter,
                                                        const Node& node);

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
template <>
Node RewriteRule<RewriteRuleKind::BV_SHR_CONST>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// same_srl
template <>
Node RewriteRule<RewriteRuleKind::BV_SHR_SAME>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// not_same_srl
template <>
Node RewriteRule<RewriteRuleKind::BV_SHR_NOT>::_apply(Rewriter& rewriter,
                                                      const Node& node);

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
template <>
Node RewriteRule<RewriteRuleKind::BV_SLT_SAME>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// bool_slt
template <>
Node RewriteRule<RewriteRuleKind::BV_SLT_BV1>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// concat_lower_slt
template <>
Node RewriteRule<RewriteRuleKind::BV_SLT_CONCAT>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// bcond_slt
template <>
Node RewriteRule<RewriteRuleKind::BV_SLT_ITE>::_apply(Rewriter& rewriter,
                                                      const Node& node);

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
template <>
Node RewriteRule<RewriteRuleKind::BV_UDIV_BV1>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// power2_udiv
template <>
Node RewriteRule<RewriteRuleKind::BV_UDIV_POW2>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// one_udiv
template <>
Node RewriteRule<RewriteRuleKind::BV_UDIV_SAME>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// bcond_udiv
template <>
Node RewriteRule<RewriteRuleKind::BV_UDIV_ITE>::_apply(Rewriter& rewriter,
                                                       const Node& node);

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
template <>
Node RewriteRule<RewriteRuleKind::BV_ULT_SAME>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// bool_ult
template <>
Node RewriteRule<RewriteRuleKind::BV_ULT_BV1>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// concat_upper_ult
// concat_lower_ult
template <>
Node RewriteRule<RewriteRuleKind::BV_ULT_CONCAT>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// bcond_ult
template <>
Node RewriteRule<RewriteRuleKind::BV_ULT_ITE>::_apply(Rewriter& rewriter,
                                                      const Node& node);

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
template <>
Node RewriteRule<RewriteRuleKind::BV_UREM_BV1>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// zero_urem
template <>
Node RewriteRule<RewriteRuleKind::BV_UREM_SAME>::_apply(Rewriter& rewriter,
                                                        const Node& node);

/* bvxor -------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::BV_XOR_EVAL>::_apply(Rewriter& rewriter,
                                                       const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::BV_XOR_SAME>::_apply(Rewriter& rewriter,
                                                       const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::BV_XOR_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::BV_NAND_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::_apply(Rewriter& rewriter,
                                                       const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::BV_NEGO_ELIM>::_apply(Rewriter& rewriter,
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

template <>
Node RewriteRule<RewriteRuleKind::BV_COMP_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);

}  // namespace bzla
#endif
