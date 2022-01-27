/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlarm.h"

#include "assert.h"

uint32_t
bzla_rm_hash(const BzlaRoundingMode rm)
{
  assert(rm == BZLA_RM_RNA || rm == BZLA_RM_RNE || rm == BZLA_RM_RTN
         || rm == BZLA_RM_RTP || rm == BZLA_RM_RTZ);
  return rm;
}

bool
bzla_rm_is_valid(uint32_t rm)
{
  return rm < BZLA_RM_MAX;
}

BzlaRoundingMode
bzla_rm_from_bv(const BzlaBitVector *bv)
{
  assert(bv);
  BzlaRoundingMode res = bzla_bv_to_uint64(bv);
  assert(bzla_rm_is_valid(res));
  return res;
}
