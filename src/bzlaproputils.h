/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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

/* maintain information about entailed propagations, e.g., when all children
 * of a node need to be updated with respect to the target value. */
struct BzlaPropInfo
{
  BzlaNode* exp;
  BzlaBitVector* bvexp; /* target value  */
  int32_t idx_x;        /* branch to take */
};
typedef struct BzlaPropInfo BzlaPropInfo;

BZLA_DECLARE_STACK(BzlaPropInfo, BzlaPropInfo);

void bzla_proputils_clone_prop_info_stack(BzlaMemMgr* mm,
                                          BzlaPropInfoStack* stack,
                                          BzlaPropInfoStack* res,
                                          BzlaNodeMap* exp_map);

void bzla_proputils_reset_prop_info_stack(BzlaMemMgr* mm,
                                          BzlaPropInfoStack* stack);

/*------------------------------------------------------------------------*/

uint64_t bzla_proputils_select_move_prop(Bzla* bzla,
                                         BzlaNode* root,
                                         BzlaBitVector* bvroot,
                                         int32_t idx_x,
                                         BzlaNode** input,
                                         BzlaBitVector** assignment);

/*=========================================================================*/

typedef bool (*BzlaPropIsInv)(BzlaMemMgr* mm,
                              const BzlaBvDomain* x,
                              const BzlaBitVector* t,
                              const BzlaBitVector* s,
                              uint32_t idx_x);

typedef BzlaBitVector* (*BzlaPropComputeValue)(Bzla* bzla,
                                               BzlaNode* exp,
                                               BzlaBitVector* bv_t,
                                               BzlaBitVector* bv_s,
                                               int32_t idx_x,
                                               BzlaIntHashTable* domains);

/*------------------------------------------------------------------------*/
/* Consistent value computation functions.                                */
/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_proputils_cons_add(Bzla* bzla,
                                       BzlaNode* add_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_and(Bzla* bzla,
                                       BzlaNode* and_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_eq(Bzla* bzla,
                                      BzlaNode* eq_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_ult(Bzla* bzla,
                                       BzlaNode* ult_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_sll(Bzla* bzla,
                                       BzlaNode* sll_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_srl(Bzla* bzla,
                                       BzlaNode* srl_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_mul(Bzla* bzla,
                                       BzlaNode* mul_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_udiv(Bzla* bzla,
                                        BzlaNode* div_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t idx_x,
                                        BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_urem(Bzla* bzla,
                                        BzlaNode* urem_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t idx_x,
                                        BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_concat(Bzla* bzla,
                                          BzlaNode* conc_exp,
                                          BzlaBitVector* t,
                                          BzlaBitVector* s,
                                          int32_t idx_x,
                                          BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_slice(Bzla* bzla,
                                         BzlaNode* slice_exp,
                                         BzlaBitVector* t,
                                         BzlaBitVector* s,
                                         int32_t idx_x,
                                         BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_cond(Bzla* bzla,
                                        BzlaNode* cond_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t idx_x,
                                        BzlaIntHashTable* domains);

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
 * add    : the Boolector node representing the + operation
 * t      : target value for 'add' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_add(Bzla* bzla,
                                      BzlaNode* add_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

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
 * and    : the Boolector node representing the & operation
 * t      : target value for 'and' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_and(Bzla* bzla,
                                      BzlaNode* and_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

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
 * eq     : the Boolector node representing the == operation
 * t      : target value for 'eq' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_eq(Bzla* bzla,
                                     BzlaNode* eq_exp,
                                     BzlaBitVector* t,
                                     BzlaBitVector* s,
                                     int32_t idx_x,
                                     BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x < s = t' or 's < x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * ult    : the Boolector node representing the ult operation
 * t      : target value for 'ult' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_ult(Bzla* bzla,
                                      BzlaNode* ult_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x << s = t' or 's << x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * sll    : the Boolector node representing the << operation
 * t      : target value for 'sll' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_sll(Bzla* bzla,
                                      BzlaNode* sll_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x >> s = t' or 's >> x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * srl    : the Boolector node representing the >> operation
 * t      : target value for 'srl' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_srl(Bzla* bzla,
                                      BzlaNode* srl_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x * s = t' or 's * x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * mul    : the Boolector node representing the * operation
 * t      : target value for 'mul' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_mul(Bzla* bzla,
                                      BzlaNode* mul_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t idx_x,
                                      BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x / s = t' or 's / x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * udiv   : the Boolector node representing the / operation
 * t      : target value for 'udiv' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_udiv(Bzla* bzla,
                                       BzlaNode* div_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x % s = t' or 's % x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * urem   : the Boolector node representing the % operation
 * t      : target value for 'urem' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_urem(Bzla* bzla,
                                       BzlaNode* urem_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x o s = t' or 's o x = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 's' and 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * concat : the Boolector node representing the o operation
 * t      : target value for 'concat' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_concat(Bzla* bzla,
                                         BzlaNode* conc_exp,
                                         BzlaBitVector* t,
                                         BzlaBitVector* s,
                                         int32_t idx_x,
                                         BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x[u:l] = t'.
 * This inverse value computation does not consider constant bits.
 *
 * Assertion: Operation is invertible given 't'.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * slice  : the Boolector node representing the [:] operation
 * t      : target value for 'slice' (the 'output' value)
 * idx_x  : not used, in order to have a consistent interface for inverse
 *          value computation functions
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_slice(Bzla* bzla,
                                        BzlaNode* slice_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t idx_x,
                                        BzlaIntHashTable* domains);

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
 * cond   : the Boolector node representing the ite operation
 * t      : target value for 'cond' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: not used, in order to have a consistent interface for inverse
 *          value computation functions
 */
BzlaBitVector* bzla_proputils_inv_cond(Bzla* bzla,
                                       BzlaNode* cond_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t idx_x,
                                       BzlaIntHashTable* domains);

/*------------------------------------------------------------------------*/
/* Inverse value computation functions using propagator domains.          */
/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_proputils_inv_add_const(Bzla* bzla,
                                            BzlaNode* add_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t idx_x,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_and_const(Bzla* bzla,
                                            BzlaNode* and_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t idx_x,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_eq_const(Bzla* bzla,
                                           BzlaNode* eq_exp,
                                           BzlaBitVector* t,
                                           BzlaBitVector* s,
                                           int32_t idx_x,
                                           BzlaIntHashTable* domains);

/**
 * Determine inverse value for 'x' given 'x < s = t' or 's < x = t' using the
 * ult domain propagator. This inverse value computation determines an inverse
 * value with respect to constant bits.
 *
 * Returns an inverse value for 'x' given values 's' (for the other operand)
 * and 't' (as the target value of the operation, the 'output' value).
 *
 * Falls back to the inverse value computation that does not utilize propagator
 * domains in case of a conflict.
 *
 * ult    : the Boolector node representing the ult operation
 * t      : target value for 'ult' (the 'output' value)
 * s      : (fixed) value of the other operand
 * idx_x  : the index of 'x', the operand we determine the value for
 * domains: a map maintaining node (id) to its propagator domain
 */
BzlaBitVector* bzla_proputils_inv_ult_const(Bzla* bzla,
                                            BzlaNode* ult_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t idx_x,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_sll_const(Bzla* bzla,
                                            BzlaNode* sll_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t idx_x,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_srl_const(Bzla* bzla,
                                            BzlaNode* srl_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t idx_x,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_mul_const(Bzla* bzla,
                                            BzlaNode* mul_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t idx_x,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_udiv_const(Bzla* bzla,
                                             BzlaNode* div_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t idx_x,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_urem_const(Bzla* bzla,
                                             BzlaNode* urem_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t idx_x,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_concat_const(Bzla* bzla,
                                               BzlaNode* conc_exp,
                                               BzlaBitVector* t,
                                               BzlaBitVector* s,
                                               int32_t idx_x,
                                               BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_slice_const(Bzla* bzla,
                                              BzlaNode* slice_exp,
                                              BzlaBitVector* t,
                                              BzlaBitVector* s,
                                              int32_t idx_x,
                                              BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_cond_const(Bzla* bzla,
                                             BzlaNode* cond_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t idx_x,
                                             BzlaIntHashTable* domains);

/*========================================================================*/
#endif
