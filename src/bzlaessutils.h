/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAESSUTILS_H_INCLUDED
#define BZLAESSUTILS_H_INCLUDED

#include "bzlabv.h"

typedef struct BzlaPropInfo BzlaPropInfo;

bool bzla_is_ess_add(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);
bool bzla_is_ess_add_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

#endif
