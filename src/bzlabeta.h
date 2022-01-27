/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLABETA_H_INCLUDED
#define BZLABETA_H_INCLUDED

#include "bzlaexp.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"

BzlaNode* bzla_beta_reduce_full(Bzla* bzla,
                                BzlaNode* exp,
                                BzlaPtrHashTable* cache);

BzlaNode* bzla_beta_reduce_merge(Bzla* bzla,
                                 BzlaNode* exp,
                                 BzlaPtrHashTable* merge_lambdas);

BzlaNode* bzla_beta_reduce_partial(Bzla* bzla,
                                   BzlaNode* exp,
                                   BzlaPtrHashTable* conds);

BzlaNode* bzla_beta_reduce_partial_collect(Bzla* bzla,
                                           BzlaNode* exp,
                                           BzlaPtrHashTable* cond_sel_if,
                                           BzlaPtrHashTable* cond_sel_else);

BzlaNode* bzla_beta_reduce_partial_collect_new(Bzla* bzla,
                                               BzlaNode* exp,
                                               BzlaNodePtrStack* exps,
                                               BzlaIntHashTable* cache);

BzlaNode* bzla_beta_reduce_bounded(Bzla* bzla, BzlaNode* exp, int32_t bound);

void bzla_beta_assign_param(Bzla* bzla, BzlaNode* lambda, BzlaNode* arg);

void bzla_beta_assign_args(Bzla* bzla, BzlaNode* fun, BzlaNode* args);

void bzla_beta_unassign_params(Bzla* bzla, BzlaNode* lambda);

#endif
