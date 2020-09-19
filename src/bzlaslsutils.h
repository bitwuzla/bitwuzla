/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLASLSUTILS_H_INCLUDED
#define BZLASLSUTILS_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashint.h"

double bzla_slsutils_compute_score_node(Bzla *bzla,
                                        BzlaIntHashTable *bv_model,
                                        BzlaIntHashTable *fun_model,
                                        BzlaIntHashTable *score,
                                        BzlaNode *exp);

void bzla_slsutils_compute_sls_scores(Bzla *bzla,
                                      BzlaIntHashTable *bv_model,
                                      BzlaIntHashTable *fun_model,
                                      BzlaIntHashTable *score);
#endif
