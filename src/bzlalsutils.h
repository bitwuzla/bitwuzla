/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLALSUTILS_H_INCLUDED
#define BZLALSUTILS_H_INCLUDED

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

#endif
