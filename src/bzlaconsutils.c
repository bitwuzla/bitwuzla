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
 * Check consistency condition (without considering const bits in x) for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: true
 */
bool
bzla_is_cons_add(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return true;
}

/**
 * Check consistency condition (without considering const bits in x) for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: mcb(x, t-s)
 */
bool
bzla_is_cons_add_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t pos_x;
  const BzlaBitVector *s, *t;
  BzlaBitVector *t_sub_s;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  mm      = bzla->mm;
  t_sub_s = bzla_bv_sub(mm, t, s);
  res     = bzla_bvdomain_check_fixed_bits(mm, x, t_sub_s);
  bzla_bv_free(mm, t_sub_s);
  return res;
}
