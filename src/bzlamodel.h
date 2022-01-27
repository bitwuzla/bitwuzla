/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAMODEL_H_INCLUDED
#define BZLAMODEL_H_INCLUDED

#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlanode.h"
#include "utils/bzlahashint.h"

/*------------------------------------------------------------------------*/

/**
 * Get AIG vector assignment of given node as bit-vector.
 * Zero initialized if unconstrained.
 */
BzlaBitVector* bzla_model_get_bv_assignment(Bzla* bzla, BzlaNode* exp);

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

void bzla_model_get_array_model(Bzla* bzla,
                                BzlaNode* exp,
                                BzlaNodePtrStack* indices,
                                BzlaNodePtrStack* values,
                                BzlaNode** default_value);

void bzla_model_get_fun_model(Bzla* bzla,
                              BzlaNode* exp,
                              BzlaNodePtrStack* args,
                              BzlaNodePtrStack* values);

/**
 * Get node representation of the model value of the given node.
 *
 * For bit-vector nodes, the returned node is a bit-vector const node.
 * For arrays, the returned node is a write chain.
 * For functions, the returned node is an ite chain over the argument values.
 */
BzlaNode* bzla_model_get_value(Bzla* bzla, BzlaNode* exp);

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
