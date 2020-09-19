/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLADC_H_INCLUDED
#define BZLADC_H_INCLUDED

#include <stdint.h>

#include "bzlatypes.h"

void bzla_dcr_compute_scores(Bzla* bzla);
void bzla_dcr_compute_scores_dual_prop(Bzla* bzla);

int32_t bzla_dcr_compare_scores(Bzla* bzla, BzlaNode* a, BzlaNode* b);
int32_t bzla_dcr_compare_scores_qsort(const void* p1, const void* p2);
#endif
