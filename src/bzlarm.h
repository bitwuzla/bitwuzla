/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLARM_H_INCLUDED
#define BZLARM_H_INCLUDED

#include "bzlatypes.h"
#include "stdbool.h"
#include "stdint.h"

#define BZLA_RM_BW 3

/** Compute the hash of the given floating-point. */
uint32_t bzla_rm_hash(const BzlaRoundingMode rm);

/** Return true if given value corresponds to a valid rounding mode. */
bool bzla_rm_is_valid(uint32_t rm);

#endif
