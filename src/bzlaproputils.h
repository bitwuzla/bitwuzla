/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAPROPUTILS_H_INCLUDED
#define BZLAPROPUTILS_H_INCLUDED

#include "bzlabv.h"
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
  int32_t eidx;         /* branch to take */
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
                                         BzlaNode** input,
                                         BzlaBitVector** assignment);

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
BzlaBitVector* inv_add_bv(Bzla* bzla,
                          BzlaNode* add_exp,
                          BzlaBitVector* bvadd,
                          BzlaBitVector* bve,
                          int32_t eidx);

BzlaBitVector* inv_and_bv(Bzla* bzla,
                          BzlaNode* and_exp,
                          BzlaBitVector* bvand,
                          BzlaBitVector* bve,
                          int32_t eidx);

BzlaBitVector* inv_eq_bv(Bzla* bzla,
                         BzlaNode* eq_exp,
                         BzlaBitVector* bveq,
                         BzlaBitVector* bve,
                         int32_t eidx);

BzlaBitVector* inv_ult_bv(Bzla* bzla,
                          BzlaNode* ult_exp,
                          BzlaBitVector* bvult,
                          BzlaBitVector* bve,
                          int32_t eidx);

BzlaBitVector* inv_sll_bv(Bzla* bzla,
                          BzlaNode* sll_exp,
                          BzlaBitVector* bvsll,
                          BzlaBitVector* bve,
                          int32_t eidx);

BzlaBitVector* inv_srl_bv(Bzla* bzla,
                          BzlaNode* srl_exp,
                          BzlaBitVector* bvsrl,
                          BzlaBitVector* bve,
                          int32_t eidx);

BzlaBitVector* inv_mul_bv(Bzla* bzla,
                          BzlaNode* mul_exp,
                          BzlaBitVector* bvmul,
                          BzlaBitVector* bve,
                          int32_t eidx);

BzlaBitVector* inv_udiv_bv(Bzla* bzla,
                           BzlaNode* div_exp,
                           BzlaBitVector* bvdiv,
                           BzlaBitVector* bve,
                           int32_t eidx);

BzlaBitVector* inv_urem_bv(Bzla* bzla,
                           BzlaNode* urem_exp,
                           BzlaBitVector* bvurem,
                           BzlaBitVector* bve,
                           int32_t eidx);

BzlaBitVector* inv_concat_bv(Bzla* bzla,
                             BzlaNode* conc_exp,
                             BzlaBitVector* bvconc,
                             BzlaBitVector* bve,
                             int32_t eidx);

BzlaBitVector* inv_slice_bv(Bzla* bzla,
                            BzlaNode* slice_exp,
                            BzlaBitVector* bvslice,
                            BzlaBitVector* bve,
                            int32_t eidx);

BzlaBitVector* inv_cond_bv(Bzla* bzla,
                           BzlaNode* cond_exp,
                           BzlaBitVector* bvcond,
                           BzlaBitVector* bve,
                           int32_t eidx);

int32_t sat_prop_solver_aux(Bzla* bzla);
#endif

/*------------------------------------------------------------------------*/

#endif
