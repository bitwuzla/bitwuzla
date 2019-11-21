/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlatypes.h"

#ifndef BZLAFP_H_INCLUDED
#define BZLAFP_H_INCLUDED

typedef struct BzlaFloatingPointSize BzlaFloatingPointSize;
typedef struct BzlaFloatingPoint BzlaFloatingPoint;

void *bzla_fp_word_blaster_new(Bzla *bzla);
void *bzla_fp_word_blaster_clone(Bzla *bzla);
void bzla_fp_word_blaster_delete(void *wblaster);

#endif
