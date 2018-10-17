/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 *
 *  Bit-vector operator propagators based on [1] and [2].
 *
 *  [1] Wenxi Wang, Harald SøndergaardPeter J. Stuckey:
 *      A Bit-Vector Solver with Word-Level Propagation
 *  [2] L. Michel, P. Van Hentenryck:
 *      Constraint Satisfaction over Bit-Vectors
 */

#include "bzlabvprop.h"

BzlaBvDomain *
bzla_bvprop_new_init(BzlaMemMgr *mm, uint32_t width)
{
  assert(mm);

  BzlaBvDomain *res;

  BZLA_CNEW(mm, res);
  res->lo = bzla_bv_zero(mm, width);
  res->hi = bzla_bv_ones(mm, width);
  return res;
}

BzlaBvDomain *
bzla_bvprop_new(BzlaMemMgr *mm,
                const BzlaBitVector *lo,
                const BzlaBitVector *hi)
{
  assert(mm);
  assert(lo);
  assert(hi);
  assert(bzla_bv_get_width(lo) == bzla_bv_get_width(hi));

  BzlaBvDomain *res;

  BZLA_CNEW(mm, res);
  res->lo = bzla_bv_copy(mm, lo);
  res->hi = bzla_bv_copy(mm, hi);
  return res;
}

void
bzla_bvprop_free(BzlaMemMgr *mm, BzlaBvDomain *d)
{
  assert(mm);
  assert(d);

  bzla_bv_free(mm, d->lo);
  bzla_bv_free(mm, d->hi);
  BZLA_DELETE(mm, d);
}

bool
bzla_bvprop_is_valid(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  BzlaBitVector *not_lo       = bzla_bv_not(mm, d->lo);
  BzlaBitVector *not_lo_or_hi = bzla_bv_or(mm, not_lo, d->hi);
  bool res                    = bzla_bv_is_ones(not_lo_or_hi);
  bzla_bv_free(mm, not_lo);
  bzla_bv_free(mm, not_lo_or_hi);
  return res;
}

bool
bzla_bvprop_is_fixed(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  BzlaBitVector *equal = bzla_bv_eq(mm, d->lo, d->hi);
  bool res             = bzla_bv_is_true(equal);
  bzla_bv_free(mm, equal);
  return res;
}
