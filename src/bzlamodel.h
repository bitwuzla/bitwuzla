/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAMODEL_H_INCLUDED
#define BZLAMODEL_H_INCLUDED

#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlanode.h"
#include "utils/bzlahashint.h"

/*------------------------------------------------------------------------*/

BzlaBitVector* bzla_model_recursively_compute_assignment(
    Bzla* bzla,
    BzlaIntHashTable* bv_model,
    BzlaIntHashTable* fun_model,
    BzlaNode* exp);

void bzla_model_generate(Bzla* bzla,
                         BzlaIntHashTable* bv_model,
                         BzlaIntHashTable* fun_model,
                         bool model_for_all_nodes);

/*------------------------------------------------------------------------*/

void bzla_model_delete(Bzla* bzla);
void bzla_model_delete_bv(Bzla* bzla, BzlaIntHashTable** bv_model);

/*------------------------------------------------------------------------*/

void bzla_model_init_bv(Bzla* bzla, BzlaIntHashTable** bv_model);
void bzla_model_init_fun(Bzla* bzla, BzlaIntHashTable** fun_model);

/*------------------------------------------------------------------------*/

BzlaIntHashTable* bzla_model_clone_bv(Bzla* bzla,
                                      BzlaIntHashTable* bv_model,
                                      bool inc_ref_cnt);
BzlaIntHashTable* bzla_model_clone_fun(Bzla* bzla,
                                       BzlaIntHashTable* fun_model,
                                       bool inc_ref_cnt);

/*------------------------------------------------------------------------*/

const BzlaBitVector* bzla_model_get_bv(Bzla* bzla, BzlaNode* exp);
const BzlaBitVector* bzla_model_get_bv_aux(Bzla* bzla,
                                           BzlaIntHashTable* bv_model,
                                           BzlaIntHashTable* fun_model,
                                           BzlaNode* exp);

const BzlaPtrHashTable* bzla_model_get_fun(Bzla* bzla, BzlaNode* exp);
const BzlaPtrHashTable* bzla_model_get_fun_aux(Bzla* bzla,
                                               BzlaIntHashTable* bv_model,
                                               BzlaIntHashTable* fun_model,
                                               BzlaNode* exp);

/*------------------------------------------------------------------------*/

void bzla_model_add_to_bv(Bzla* bzla,
                          BzlaIntHashTable* bv_model,
                          BzlaNode* exp,
                          const BzlaBitVector* assignment);
void bzla_model_remove_from_bv(Bzla* bzla,
                               BzlaIntHashTable* bv_model,
                               BzlaNode* exp);

/*------------------------------------------------------------------------*/

#endif
