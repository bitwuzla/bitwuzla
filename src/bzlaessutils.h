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

/* -------------------------------------------------------------------------- */

/** Check if x is essential w.r.t. to t for x + s = t or s + x = t. */
bool bzla_is_ess_add(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/* -------------------------------------------------------------------------- */

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x + s = t
 * or s + x = t.
 */
bool bzla_is_ess_add_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

#endif
