/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLACONSUTILS_H_INCLUDED
#define BZLACONSUTILS_H_INCLUDED

#include "bzlabv.h"

typedef struct BzlaPropInfo BzlaPropInfo;

bool bzla_is_cons_add(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_add_const(Bzla *bzla, BzlaPropInfo *pi);

#endif
