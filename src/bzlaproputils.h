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
                                         int32_t eidx,
                                         BzlaNode** input,
                                         BzlaBitVector** assignment);

/*=========================================================================*/

typedef bool (*BzlaPropIsInv)(BzlaMemMgr* mm,
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
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_and(Bzla* bzla,
                                       BzlaNode* and_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_eq(Bzla* bzla,
                                      BzlaNode* eq_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_ult(Bzla* bzla,
                                       BzlaNode* ult_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_sll(Bzla* bzla,
                                       BzlaNode* sll_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_srl(Bzla* bzla,
                                       BzlaNode* srl_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_mul(Bzla* bzla,
                                       BzlaNode* mul_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_udiv(Bzla* bzla,
                                        BzlaNode* div_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t eidx,
                                        BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_urem(Bzla* bzla,
                                        BzlaNode* urem_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t eidx,
                                        BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_concat(Bzla* bzla,
                                          BzlaNode* conc_exp,
                                          BzlaBitVector* t,
                                          BzlaBitVector* s,
                                          int32_t eidx,
                                          BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_slice(Bzla* bzla,
                                         BzlaNode* slice_exp,
                                         BzlaBitVector* t,
                                         BzlaBitVector* s,
                                         int32_t eidx,
                                         BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_cons_cond(Bzla* bzla,
                                        BzlaNode* cond_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t eidx,
                                        BzlaIntHashTable* domains);

/*------------------------------------------------------------------------*/
/* Inverse value computation functions as implemented for CAV'16.         */
/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_proputils_inv_add(Bzla* bzla,
                                      BzlaNode* add_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_and(Bzla* bzla,
                                      BzlaNode* and_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_eq(Bzla* bzla,
                                     BzlaNode* eq_exp,
                                     BzlaBitVector* t,
                                     BzlaBitVector* s,
                                     int32_t eidx,
                                     BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_ult(Bzla* bzla,
                                      BzlaNode* ult_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_sll(Bzla* bzla,
                                      BzlaNode* sll_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_srl(Bzla* bzla,
                                      BzlaNode* srl_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_mul(Bzla* bzla,
                                      BzlaNode* mul_exp,
                                      BzlaBitVector* t,
                                      BzlaBitVector* s,
                                      int32_t eidx,
                                      BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_udiv(Bzla* bzla,
                                       BzlaNode* div_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_urem(Bzla* bzla,
                                       BzlaNode* urem_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_concat(Bzla* bzla,
                                         BzlaNode* conc_exp,
                                         BzlaBitVector* t,
                                         BzlaBitVector* s,
                                         int32_t eidx,
                                         BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_slice(Bzla* bzla,
                                        BzlaNode* slice_exp,
                                        BzlaBitVector* t,
                                        BzlaBitVector* s,
                                        int32_t eidx,
                                        BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_cond(Bzla* bzla,
                                       BzlaNode* cond_exp,
                                       BzlaBitVector* t,
                                       BzlaBitVector* s,
                                       int32_t eidx,
                                       BzlaIntHashTable* domains);

/*------------------------------------------------------------------------*/
/* Inverse value interval computation wrt const bits (propagator domain).  */
/*------------------------------------------------------------------------*/

bool bzla_proputils_inv_interval_ult(BzlaMemMgr* mm,
                                     BzlaBitVector* t,
                                     BzlaBitVector* s,
                                     int32_t idx_x,
                                     BzlaBvDomain* d_x,
                                     BzlaBitVector** min,
                                     BzlaBitVector** max);

/*------------------------------------------------------------------------*/
/* Inverse value computation functions using propagator domains.          */
/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_proputils_inv_add_bvprop(Bzla* bzla,
                                             BzlaNode* add_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t eidx,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_and_bvprop(Bzla* bzla,
                                             BzlaNode* and_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t eidx,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_eq_bvprop(Bzla* bzla,
                                            BzlaNode* eq_exp,
                                            BzlaBitVector* t,
                                            BzlaBitVector* s,
                                            int32_t eidx,
                                            BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_ult_bvprop(Bzla* bzla,
                                             BzlaNode* ult_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t eidx,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_sll_bvprop(Bzla* bzla,
                                             BzlaNode* sll_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t eidx,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_srl_bvprop(Bzla* bzla,
                                             BzlaNode* srl_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t eidx,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_mul_bvprop(Bzla* bzla,
                                             BzlaNode* mul_exp,
                                             BzlaBitVector* t,
                                             BzlaBitVector* s,
                                             int32_t eidx,
                                             BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_udiv_bvprop(Bzla* bzla,
                                              BzlaNode* div_exp,
                                              BzlaBitVector* t,
                                              BzlaBitVector* s,
                                              int32_t eidx,
                                              BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_urem_bvprop(Bzla* bzla,
                                              BzlaNode* urem_exp,
                                              BzlaBitVector* t,
                                              BzlaBitVector* s,
                                              int32_t eidx,
                                              BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_concat_bvprop(Bzla* bzla,
                                                BzlaNode* conc_exp,
                                                BzlaBitVector* t,
                                                BzlaBitVector* s,
                                                int32_t eidx,
                                                BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_slice_bvprop(Bzla* bzla,
                                               BzlaNode* slice_exp,
                                               BzlaBitVector* t,
                                               BzlaBitVector* s,
                                               int32_t eidx,
                                               BzlaIntHashTable* domains);

BzlaBitVector* bzla_proputils_inv_cond_bvprop(Bzla* bzla,
                                              BzlaNode* cond_exp,
                                              BzlaBitVector* t,
                                              BzlaBitVector* s,
                                              int32_t eidx,
                                              BzlaIntHashTable* domains);

/*========================================================================*/
#endif
