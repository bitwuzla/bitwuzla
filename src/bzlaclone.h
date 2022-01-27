/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLACLONE_H_INCLUDED
#define BZLACLONE_H_INCLUDED

#include "bzlanode.h"
#include "utils/bzlanodemap.h"

/* Clone an existing Bitwuzla instance. */
Bzla *bzla_clone(Bzla *bzla);

/* Clone the expression layer of an existing Bitwuzla instance. */
Bzla *bzla_clone_exp_layer(Bzla *bzla,
                           BzlaNodeMap **exp_map,
                           bool clone_simplified);

/* Clone the expression layer and no bzla->slv */
Bzla *bzla_clone_formula(Bzla *bzla);

/* Rebuild 'exp' (and all expressions below) of an existing Bitwuzla instance
 * 'bzla' in an existing Bitwuzla instance 'clone' with rewrite level
 * 'rewrite_level'. 'exp_map' must contain all previously cloned expressions.
 */
BzlaNode *bzla_clone_recursively_rebuild_exp(Bzla *bzla,
                                             Bzla *clone,
                                             BzlaNode *exp,
                                             BzlaNodeMap *exp_map,
                                             uint32_t rewrite_level);

BzlaSortId bzla_clone_recursively_rebuild_sort(Bzla *bzla,
                                               Bzla *clone,
                                               BzlaSortId sort);

/* helpers for hash table cloning */
void *bzla_clone_key_as_node(BzlaMemMgr *mm, const void *map, const void *key);

void *bzla_clone_key_as_str(BzlaMemMgr *mm, const void *map, const void *key);

void *bzla_clone_key_as_static_str(BzlaMemMgr *mm,
                                   const void *map,
                                   const void *key);

void *bzla_clone_key_as_bv_tuple(BzlaMemMgr *mm,
                                 const void *map,
                                 const void *t);

void bzla_clone_data_as_node_ptr(BzlaMemMgr *mm,
                                 const void *map,
                                 BzlaHashTableData *data,
                                 BzlaHashTableData *cloned_data);

void bzla_clone_data_as_str_ptr(BzlaMemMgr *mm,
                                const void *str_table,
                                BzlaHashTableData *data,
                                BzlaHashTableData *cloned_data);

void bzla_clone_data_as_int(BzlaMemMgr *mm,
                            const void *map,
                            BzlaHashTableData *data,
                            BzlaHashTableData *cloned_data);

void bzla_clone_data_as_dbl(BzlaMemMgr *mm,
                            const void *map,
                            BzlaHashTableData *data,
                            BzlaHashTableData *cloned_data);

void bzla_clone_data_as_bv_ptr(BzlaMemMgr *mm,
                               const void *map,
                               BzlaHashTableData *data,
                               BzlaHashTableData *cloned_data);

void bzla_clone_data_as_ptr_htable(BzlaMemMgr *mm,
                                   const void *map,
                                   BzlaHashTableData *data,
                                   BzlaHashTableData *cloned_data);

void bzla_clone_data_as_bv_ptr_htable(BzlaMemMgr *mm,
                                      const void *map,
                                      BzlaHashTableData *data,
                                      BzlaHashTableData *cloned_data);

void bzla_clone_data_as_int_htable(BzlaMemMgr *mm,
                                   const void *map,
                                   BzlaHashTableData *data,
                                   BzlaHashTableData *cloned_data);

void bzla_clone_node_ptr_stack(BzlaMemMgr *mm,
                               BzlaNodePtrStack *stack,
                               BzlaNodePtrStack *res,
                               BzlaNodeMap *exp_map,
                               bool is_zero_terminated);
#endif
