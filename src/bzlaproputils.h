/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAPROPUTILS_H_INCLUDED
#define BZLAPROPUTILS_H_INCLUDED

#include "bzlabv.h"
#include "bzlabvprop.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

#define BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA 100

/*------------------------------------------------------------------------*/

bool bzla_is_bv_sext(Bzla* bzla, BzlaNode* n);
bool bzla_is_bv_sra(Bzla* bzla,
                    const BzlaNode* n,
                    BzlaNode** res_a,
                    BzlaNode** res_b);

/* maintain information about entailed propagations, e.g., when all children
 * of a node need to be updated with respect to the target value. */
struct BzlaPropEntailInfo
{
  BzlaNode* exp;
  BzlaBitVector* bvexp; /* target value  */
  int32_t idx_x;        /* branch to take */
};
typedef struct BzlaPropEntailInfo BzlaPropEntailInfo;

BZLA_DECLARE_STACK(BzlaPropEntailInfo, BzlaPropEntailInfo);

void bzla_proputils_clone_prop_info_stack(BzlaMemMgr* mm,
                                          BzlaPropEntailInfoStack* stack,
                                          BzlaPropEntailInfoStack* res,
                                          BzlaNodeMap* exp_map);

void bzla_proputils_reset_prop_info_stack(BzlaMemMgr* mm,
                                          BzlaPropEntailInfoStack* stack);

/*------------------------------------------------------------------------*/

struct BzlaPropInfo
{
  const BzlaNode* exp;
  const BzlaBitVector* bv[3];
  const BzlaBvDomain* bvd[3];
  int32_t pos_x;
  const BzlaBitVector* target_value;
  BzlaBvDomain* res_x;
};

typedef struct BzlaPropInfo BzlaPropInfo;

void bzla_propinfo_set_result(Bzla* bzla, BzlaPropInfo* pi, BzlaBvDomain* res);

/*------------------------------------------------------------------------*/

uint64_t bzla_proputils_select_move_prop(Bzla* bzla,
                                         BzlaNode* root,
                                         BzlaBitVector* bvroot,
                                         int32_t idx_x,
                                         BzlaNode** input,
                                         BzlaBitVector** assignment);

/*=========================================================================*/

typedef bool (*BzlaPropIsEssFun)(Bzla* bzla, BzlaPropInfo* pi, uint32_t pos_x);
typedef bool (*BzlaPropIsInvFun)(Bzla* bzla, BzlaPropInfo* pi);

typedef BzlaBitVector* (*BzlaPropComputeValueFun)(Bzla* bzla, BzlaPropInfo* pi);

/*------------------------------------------------------------------------*/
/* Consistent value computation functions as implemented for CAV'16. */
/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_proputils_cons_add(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_and(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_xor(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_eq(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_ult(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_sll(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_slt(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_srl(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_sra(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_mul(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_udiv(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_urem(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_concat(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_sext(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_slice(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_cond(Bzla* bzla, BzlaPropInfo* pi);

/*------------------------------------------------------------------------*/
/* Consistent value computation functions with respect to const bits in x */
/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_proputils_cons_add_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_and_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_xor_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_eq_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_ult_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_sll_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_slt_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_srl_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_sra_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_mul_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_udiv_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_urem_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_concat_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_sext_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_slice_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_cond_const(Bzla* bzla, BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_udiv_const_pos0_aux(Bzla* bzla,
                                                       BzlaPropInfo* pi);

BzlaBitVector* bzla_proputils_cons_urem_const_pos0_aux(Bzla* bzla,
                                                       BzlaPropInfo* pi);

/*------------------------------------------------------------------------*/
/* Inverse value computation functions as implemented for CAV'16.         */
/*------------------------------------------------------------------------*/

/**
 * Determine inverse value for 'x' given 'x + s = t' or 's + x = t'.
 * Note that + is always invertible (if const bits are not considered).
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_add(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x & s = t' or 's & x = t'.
 * Note that & is always invertible (if const bits are not considered).
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_and(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x ^ s = t' or 's ^ x = t'.
 * Note that & is always invertible (if const bits are not considered).
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_xor(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x == s = t' or 's == x = t'.
 * Note that == is always invertible (if const bits are not considered).
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_eq(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x < s = t' or 's < x = t' (unsigned).
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_ult(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x < s = t' or 's < x = t' (signed).
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_slt(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x << s = t' or 's << x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_sll(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x >> s = t' or 's >> x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_srl(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x >>a s = t' or 's >>a x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_sra(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x * s = t' or 's * x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_mul(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x / s = t' or 's / x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_udiv(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x % s = t' or 's % x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_urem(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x o s = t' or 's o x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_concat(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'sext(x, n) = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 't'.
 *
 * Returns an inverse value for 'x' given values 'x_val' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_sext(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x[u:l] = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 't'.
 *
 * Returns an inverse value for 'x' given values 'x_val' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_slice(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'c ? x : s = t' or 'c ? s : x = t'.
 *
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_cond(Bzla* bzla, BzlaPropInfo* pi);

/*------------------------------------------------------------------------*/
/* Inverse value computation functions with respect to const bits in x.   */
/*------------------------------------------------------------------------*/

/**
 * Determine inverse value for 'x' given 'x + s = t' or 's + x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_add_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x & s = t' or 's & x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_and_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x ^ s = t' or 's ^ x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_xor_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x == s = t' or 's == x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_eq_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x < s = t' or 's < x = t' (unsigned)
 * with respect to const bits in x.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_ult_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x << s = t' or 's << x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_sll_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x < s = t' or 's < x = t' (signed)
 * with respect to const bits in x.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_slt_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x >> s = t' or 's >> x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_srl_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x >>a s = t' or 's >>a x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_sra_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x * s = t' or 's * x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_mul_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x / s = t' or 's / x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_udiv_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x % s = t' or 's % x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_urem_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x o s = t' or 's o x = t' with
 * respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_concat_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'sext(x, n) = t' with respect to const
 * bits in x.
 *
 * Assertion: Operation is invertible given 't'.
 *
 * Returns an inverse value for 'x' given values 'x_val' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_sext_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'x[u:l] = t' with respect to const
 * bits.
 *
 * Assertion: Operation is invertible given 't'.
 *
 * Returns an inverse value for 'x' given values 'x_val' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_slice_const(Bzla* bzla, BzlaPropInfo* pi);

/**
 * Determine inverse value for 'x' given 'c ? x : s = t' or 'c ? s : x = t'
 * with respect to const bits in x.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * pi: The struct containing all information for inverse value computation.
 */
BzlaBitVector* bzla_proputils_inv_cond_const(Bzla* bzla, BzlaPropInfo* pi);

/*========================================================================*/
#endif
