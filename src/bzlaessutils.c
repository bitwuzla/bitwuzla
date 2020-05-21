/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include "bzlaessutils.h"

#include <assert.h>

#include "bzlaconsutils.h"
#include "bzlacore.h"
#include "bzlaproputils.h"
#include "utils/bzlautil.h"

/*
 * Check if x is essential w.r.t. to t for:
 *
 * x + s = t
 * s + x = t
 *
 * EC: mcb(s, t - x)
 */
bool
bzla_is_ess_add(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);
  (void) pos_x;
  return false;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x + s = t
 * s + x = t
 *
 * EC: mcb(s, t - x)
 */
bool
bzla_is_ess_add_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_cons_add_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}
