/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018-2019 Aina Niemetz.
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

static BzlaBvDomain *
new_domain(BzlaMemMgr *mm)
{
  BzlaBvDomain *res;
  BZLA_CNEW(mm, res);
  return res;
}

BzlaBvDomain *
bzla_bvprop_new_init(BzlaMemMgr *mm, uint32_t width)
{
  assert(mm);
  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_zero(mm, width);
  res->hi           = bzla_bv_ones(mm, width);
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

  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_copy(mm, lo);
  res->hi           = bzla_bv_copy(mm, hi);
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

void
bzla_bvprop_eq(BzlaMemMgr *mm,
               BzlaBvDomain *d_x,
               BzlaBvDomain *d_y,
               BzlaBvDomain **res_d_xy,
               BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(d_y);

  *res_d_xy       = new_domain(mm);
  (*res_d_xy)->lo = bzla_bv_or(mm, d_x->lo, d_y->lo);
  (*res_d_xy)->hi = bzla_bv_and(mm, d_x->hi, d_y->hi);

  if (bzla_bvprop_is_valid(mm, *res_d_xy))
  {
    /* Domain is valid and fixed: equality is true. */
    if (bzla_bvprop_is_fixed(mm, *res_d_xy))
    {
      *res_d_z       = new_domain(mm);
      (*res_d_z)->lo = bzla_bv_one(mm, 1);
      (*res_d_z)->hi = bzla_bv_one(mm, 1);
    }
    /* Domain is valid and not fixed: equality can be true/false. */
    else
    {
      *res_d_z = bzla_bvprop_new_init(mm, 1);
    }
  }
  else /* Domain is invalid: equality is false. */
  {
    *res_d_z       = new_domain(mm);
    (*res_d_z)->lo = bzla_bv_zero(mm, 1);
    (*res_d_z)->hi = bzla_bv_zero(mm, 1);
  }
  assert(bzla_bvprop_is_valid(mm, *res_d_z));
}

void
bzla_bvprop_not(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(d_z);

  BzlaBitVector *not_hi = bzla_bv_not(mm, d_z->hi);
  BzlaBitVector *not_lo = bzla_bv_not(mm, d_z->lo);
  *res_d_x              = new_domain(mm);
  (*res_d_x)->lo        = bzla_bv_or(mm, d_x->lo, not_hi);
  (*res_d_x)->hi        = bzla_bv_and(mm, d_x->hi, not_lo);
  bzla_bv_free(mm, not_hi);
  bzla_bv_free(mm, not_lo);

  not_hi         = bzla_bv_not(mm, d_x->hi);
  not_lo         = bzla_bv_not(mm, d_x->lo);
  *res_d_z       = new_domain(mm);
  (*res_d_z)->lo = bzla_bv_or(mm, d_z->lo, not_hi);
  (*res_d_z)->hi = bzla_bv_and(mm, d_z->hi, not_lo);
  bzla_bv_free(mm, not_hi);
  bzla_bv_free(mm, not_lo);
}

static void
bvprop_shift_const_aux(BzlaMemMgr *mm,
                       BzlaBvDomain *d_x,
                       BzlaBvDomain *d_z,
                       BzlaBitVector *n,
                       BzlaBvDomain **res_d_x,
                       BzlaBvDomain **res_d_z,
                       bool is_srl)
{
  assert(mm);
  assert(d_x);
  assert(d_z);

  uint32_t w, wn;
  BzlaBitVector *mask1, *mask2, *ones_wn, *zero_wn, *ones_w_wn, *zero_w_wn;
  BzlaBitVector *tmp, *tmp1;

  w = bzla_bv_get_width(d_z->hi);
  assert(w == bzla_bv_get_width(d_z->lo));
  assert(w == bzla_bv_get_width(d_x->hi));
  assert(w == bzla_bv_get_width(d_x->lo));
#ifndef NDEBUG
  BzlaBitVector *uint32maxbv = bzla_bv_ones(mm, 32);
  assert(bzla_bv_compare(n, uint32maxbv) <= 0);
  bzla_bv_free(mm, uint32maxbv);
#endif
  wn = (uint32_t) bzla_bv_to_uint64(n);

  /**
   * SLL: mask1 = 1_[wn]   :: 0_[w-wn]
   *      mask2 = 1_[w-wn] :: 0_[wn]
   * SRL: mask1 = 0_[w-wn] :: 1_[wn]
   *      mask2 = 0_[wn]   :: 1_[w-wn]
   */
  if (wn == 0)
  {
    mask1 = bzla_bv_zero(mm, w);
    mask2 = bzla_bv_ones(mm, w);
  }
  else if (w == wn)
  {
    mask1 = bzla_bv_ones(mm, w);
    mask2 = bzla_bv_zero(mm, w);
  }
  else
  {
    zero_wn   = bzla_bv_zero(mm, wn);
    zero_w_wn = bzla_bv_zero(mm, w - wn);
    ones_wn   = bzla_bv_ones(mm, wn);
    ones_w_wn = bzla_bv_ones(mm, w - wn);

    if (is_srl)
    {
      mask1 = bzla_bv_concat(mm, zero_w_wn, ones_wn);
      mask2 = bzla_bv_concat(mm, zero_wn, ones_w_wn);
    }
    else
    {
      mask1 = bzla_bv_concat(mm, ones_wn, zero_w_wn);
      mask2 = bzla_bv_concat(mm, ones_w_wn, zero_wn);
    }
    bzla_bv_free(mm, zero_wn);
    bzla_bv_free(mm, zero_w_wn);
    bzla_bv_free(mm, ones_wn);
    bzla_bv_free(mm, ones_w_wn);
  }

  *res_d_x = new_domain(mm);
  *res_d_z = new_domain(mm);

  /**
   * SLL: lo_x' = lo_x | (lo_z >> n)
   * SRL: lo_x' = lo_x | (lo_z << n)
   */
  tmp = is_srl ? bzla_bv_sll(mm, d_z->lo, n) : bzla_bv_srl(mm, d_z->lo, n);
  (*res_d_x)->lo = bzla_bv_or(mm, d_x->lo, tmp);
  bzla_bv_free(mm, tmp);

  /**
   * SLL: hi_x' = ((hi_z >> n) | mask1) & hi_x
   * SRL: hi_x' = ((hi_z << n) | mask1) & hi_x
   */
  tmp  = is_srl ? bzla_bv_sll(mm, d_z->hi, n) : bzla_bv_srl(mm, d_z->hi, n);
  tmp1 = bzla_bv_or(mm, tmp, mask1);
  (*res_d_x)->hi = bzla_bv_and(mm, tmp1, d_x->hi);
  bzla_bv_free(mm, tmp);
  bzla_bv_free(mm, tmp1);

  /**
   * SLL: lo_z' = ((low_x << n) | lo_z) & mask2
   * SRL: lo_z' = ((low_x >> n) | lo_z) & mask2
   */
  tmp  = is_srl ? bzla_bv_srl(mm, d_x->lo, n) : bzla_bv_sll(mm, d_x->lo, n);
  tmp1 = bzla_bv_or(mm, tmp, d_z->lo);
  (*res_d_z)->lo = bzla_bv_and(mm, tmp1, mask2);
  bzla_bv_free(mm, tmp);
  bzla_bv_free(mm, tmp1);

  /**
   * SLL: hi_z' = (hi_x << n) & hi_z
   * SRL: hi_z' = (hi_x >> n) & hi_z
   */
  tmp = is_srl ? bzla_bv_srl(mm, d_x->hi, n) : bzla_bv_sll(mm, d_x->hi, n);
  (*res_d_z)->hi = bzla_bv_and(mm, tmp, d_z->hi);
  bzla_bv_free(mm, tmp);

  bzla_bv_free(mm, mask2);
  bzla_bv_free(mm, mask1);
}

void
bzla_bvprop_sll_const(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBitVector *n,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z)
{
  bvprop_shift_const_aux(mm, d_x, d_z, n, res_d_x, res_d_z, false);
}

void
bzla_bvprop_srl_const(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBitVector *n,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z)
{
  bvprop_shift_const_aux(mm, d_x, d_z, n, res_d_x, res_d_z, true);
}
