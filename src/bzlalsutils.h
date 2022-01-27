/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLALSUTILS_H_INCLUDED
#define BZLALSUTILS_H_INCLUDED

#include "bzlaslv.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"

/**
 * Update cone of incluence as a consequence of a local search move.
 *
 * Note: 'roots' will only be updated if 'update_roots' is true.
 *         + PROP engine: always
 *         + SLS  engine: only if an actual move is performed
 *                        (not during neighborhood exploration, 'try_move')
 */
void bzla_lsutils_update_cone(Bzla* bzla,
                              BzlaIntHashTable* bv_model,
                              BzlaIntHashTable* roots,
                              BzlaIntHashTable* score,
                              BzlaIntHashTable* exps,
                              bool update_roots,
                              uint64_t* stats_updates,
                              double* time_update_cone,
                              double* time_update_cone_reset,
                              double* time_update_cone_model_gen,
                              double* time_update_cone_compute_score);

bool bzla_lsutils_is_leaf_node(BzlaNode* n);

void bzla_lsutils_initialize_bv_model(BzlaSolver* slv);

#endif
