/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include "bzlaconsutils.h"

#include <assert.h>

#include "bzlabvdomain.h"
#include "bzlacore.h"
#include "bzlaproputils.h"

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: true
 */
bool
bzla_is_cons_add_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return true;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x & s = t
 * s & x = t
 *
 * IC: t & xhi = t
 */
bool
bzla_is_cons_and_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t pos_x;
  const BzlaBitVector *t;
  BzlaBitVector *tmp;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  tmp = bzla_bv_and(mm, t, x->hi);
  res = bzla_bv_compare(t, tmp) == 0;
  bzla_bv_free(mm, tmp);
  return res;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x ^ s = t
 * s ^ x = t
 *
 * IC: true
 */
bool
bzla_is_cons_xor_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return true;
}
