/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLARM_H_INCLUDED
#define BZLARM_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "bzlabv.h"

#define BZLA_RM_BW 3

enum BzlaRoundingMode
{
  BZLA_RM_RNA = 0,
  BZLA_RM_RNE,
  BZLA_RM_RTN,
  BZLA_RM_RTP,
  BZLA_RM_RTZ,
  BZLA_RM_MAX,
};
typedef enum BzlaRoundingMode BzlaRoundingMode;

/** Compute the hash of the given floating-point. */
uint32_t bzla_rm_hash(const BzlaRoundingMode rm);

/** Return true if given value corresponds to a valid rounding mode. */
bool bzla_rm_is_valid(uint32_t rm);

/**
 * Convert given bit-vector (representing a rounding mode value) into its
 * corresponding BzlaRoundingMode representation.
 */
BzlaRoundingMode bzla_rm_from_bv(const BzlaBitVector *bv);

#endif
