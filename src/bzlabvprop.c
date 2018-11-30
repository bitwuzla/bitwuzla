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

#include <stdio.h>

#include "utils/bzlautil.h"

#if 0
static void print_domain(
    BzlaMemMgr * g_mm, BzlaBvDomain *d, bool print_short)
{
  if (print_short)
  {
    char *lo   = bzla_bv_to_char (g_mm, d->lo);
    char *hi   = bzla_bv_to_char (g_mm, d->hi);
    size_t len = strlen (lo);
    for (size_t i = 0; i < len; i++)
    {
      if (lo[i] != hi[i])
      {
        if (lo[i] == '0' && hi[i] == '1')
        {
          lo[i] = 'x';
        }
        else
        {
          assert (lo[i] == '1' && hi[i] == '0');
          lo[i] = '?';
        }
      }
    }
    printf ("%s\n", lo);
    bzla_mem_freestr (g_mm, hi);
    bzla_mem_freestr (g_mm, lo);
  }
  else
  {
    char *s = bzla_bv_to_char (g_mm, d->lo);
    printf ("lo: %s, ", s);
    bzla_mem_freestr (g_mm, s);
    s = bzla_bv_to_char (g_mm, d->hi);
    printf ("hi: %s\n", s);
    bzla_mem_freestr (g_mm, s);
  }
}
#endif

BZLA_DECLARE_STACK(BzlaBvDomainPtr, BzlaBvDomain *);

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

static bool
made_progress(BzlaBvDomain *d_x,
              BzlaBvDomain *d_y,
              BzlaBvDomain *d_z,
              BzlaBvDomain *d_c,
              BzlaBvDomain *res_d_x,
              BzlaBvDomain *res_d_y,
              BzlaBvDomain *res_d_z,
              BzlaBvDomain *res_d_c)
{
  assert(d_x);
  assert(d_z);
  assert(res_d_x);
  assert(res_d_z);
  assert(!d_y || res_d_y);

  if (bzla_bv_compare(d_x->lo, res_d_x->lo)) return true;
  if (bzla_bv_compare(d_x->hi, res_d_x->hi)) return true;
  if (d_y && bzla_bv_compare(d_y->lo, res_d_y->lo)) return true;
  if (d_y && bzla_bv_compare(d_y->hi, res_d_y->hi)) return true;
  if (bzla_bv_compare(d_z->lo, res_d_z->lo)) return true;
  if (bzla_bv_compare(d_z->hi, res_d_z->hi)) return true;
  if (d_c && bzla_bv_compare(d_c->lo, res_d_c->lo)) return true;
  if (d_c && bzla_bv_compare(d_c->hi, res_d_c->hi)) return true;
  return false;
}

bool
bzla_bvprop_eq(BzlaMemMgr *mm,
               BzlaBvDomain *d_x,
               BzlaBvDomain *d_y,
               BzlaBvDomain **res_d_xy,
               BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));

  /**
   * lo_xy = lo_x | lo_y
   * hi_xy = hi_x & hi_y
   */
  *res_d_xy       = new_domain(mm);
  (*res_d_xy)->lo = bzla_bv_or(mm, d_x->lo, d_y->lo);
  (*res_d_xy)->hi = bzla_bv_and(mm, d_x->hi, d_y->hi);

  if (res_d_z)
  {
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
    /* Domain is invalid: equality is false. */
    else
    {
      *res_d_z       = new_domain(mm);
      (*res_d_z)->lo = bzla_bv_zero(mm, 1);
      (*res_d_z)->hi = bzla_bv_zero(mm, 1);
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
  }
  return true;
}

bool
bzla_bvprop_not(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));

  /**
   * lo_x' = lo_x | ~hi_z
   * hi_x' = hi_x & ~hi_z
   */
  BzlaBitVector *not_hi = bzla_bv_not(mm, d_z->hi);
  BzlaBitVector *not_lo = bzla_bv_not(mm, d_z->lo);
  *res_d_x              = new_domain(mm);
  (*res_d_x)->lo        = bzla_bv_or(mm, d_x->lo, not_hi);
  (*res_d_x)->hi        = bzla_bv_and(mm, d_x->hi, not_lo);
  bzla_bv_free(mm, not_hi);
  bzla_bv_free(mm, not_lo);

  /**
   * lo_z' = lo_z | ~hi_x
   * hi_z' = hi_z & ~hi_x
   */
  not_hi         = bzla_bv_not(mm, d_x->hi);
  not_lo         = bzla_bv_not(mm, d_x->lo);
  *res_d_z       = new_domain(mm);
  (*res_d_z)->lo = bzla_bv_or(mm, d_z->lo, not_hi);
  (*res_d_z)->hi = bzla_bv_and(mm, d_z->hi, not_lo);
  bzla_bv_free(mm, not_hi);
  bzla_bv_free(mm, not_lo);

  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

static bool
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
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(n);
  assert(bzla_bv_get_width(d_x->lo) == bzla_bv_get_width(n));
  assert(res_d_x);
  assert(res_d_z);

  uint32_t w, wn;
  BzlaBitVector *mask1, *ones_wn, *zero_wn, *ones_w_wn, *zero_w_wn;
  BzlaBitVector *tmp0, *tmp1;

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
   * SRL: mask1 = 0_[w-wn] :: 1_[wn]
   */
  if (wn == 0)
  {
    mask1 = bzla_bv_zero(mm, w);
  }
  else if (wn >= w)
  {
    mask1 = bzla_bv_ones(mm, w);
  }
  else
  {
    zero_wn   = bzla_bv_zero(mm, wn);
    zero_w_wn = bzla_bv_zero(mm, w - wn);
    ones_wn   = bzla_bv_ones(mm, wn);
    ones_w_wn = bzla_bv_ones(mm, w - wn);

    mask1 = is_srl ? bzla_bv_concat(mm, zero_w_wn, ones_wn)
                   : bzla_bv_concat(mm, ones_wn, zero_w_wn);
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
  tmp0 = is_srl ? bzla_bv_sll(mm, d_z->lo, n) : bzla_bv_srl(mm, d_z->lo, n);
  (*res_d_x)->lo = bzla_bv_or(mm, d_x->lo, tmp0);
  bzla_bv_free(mm, tmp0);

  /**
   * SLL: hi_x' = ((hi_z >> n) | mask1) & hi_x
   * SRL: hi_x' = ((hi_z << n) | mask1) & hi_x
   */
  tmp0 = is_srl ? bzla_bv_sll(mm, d_z->hi, n) : bzla_bv_srl(mm, d_z->hi, n);
  tmp1 = bzla_bv_or(mm, tmp0, mask1);
  (*res_d_x)->hi = bzla_bv_and(mm, tmp1, d_x->hi);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /**
   * SLL: lo_z' = ((low_x << n) | lo_z)
   * SRL: lo_z' = ((low_x >> n) | lo_z)
   *
   * Note: Propagator in [1] is incorrect!
   * (was:
   *   SLL: lo_z' = ((low_x << n) | lo_z) & mask2
   *   SRL: lo_z' = ((low_x >> n) | lo_z) & mask2
   *  with:
   *   SLL: mask2 = 1_[w-wn] :: 0_[wn]
   *   SRL: mask2 = 0_[wn]   :: 1_[w-wn]
   *  )
   */
  tmp0 = is_srl ? bzla_bv_srl(mm, d_x->lo, n) : bzla_bv_sll(mm, d_x->lo, n);
  (*res_d_z)->lo = bzla_bv_or(mm, tmp0, d_z->lo);
  bzla_bv_free(mm, tmp0);

  /**
   * SLL: hi_z' = (hi_x << n) & hi_z
   * SRL: hi_z' = (hi_x >> n) & hi_z
   */
  tmp0 = is_srl ? bzla_bv_srl(mm, d_x->hi, n) : bzla_bv_sll(mm, d_x->hi, n);
  (*res_d_z)->hi = bzla_bv_and(mm, tmp0, d_z->hi);
  bzla_bv_free(mm, tmp0);

  bzla_bv_free(mm, mask1);

  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_sll_const(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBitVector *n,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z)
{
  return bvprop_shift_const_aux(mm, d_x, d_z, n, res_d_x, res_d_z, false);
}

bool
bzla_bvprop_srl_const(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBitVector *n,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z)
{
  return bvprop_shift_const_aux(mm, d_x, d_z, n, res_d_x, res_d_z, true);
}

bool
bzla_bvprop_sll(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(bzla_bv_get_width(d_x->lo) == bzla_bv_get_width(d_y->lo));
  assert(bzla_bv_get_width(d_x->lo) == bzla_bv_get_width(d_z->lo));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  /* z_[bw] = x_[bw] << y_[bw]
   *
   * prev_z = x
   * for i = 0 to bw - 1:
   *   shift = 1 << i
   *   cur_z = ite (y[i:i], prev_z << shift, prev_z)
   *   prev_z = cur_z
   */

  uint32_t i, n, bw;
  bool res, progress;
  BzlaBitVector *bv;
  BzlaBvDomain *d, *tmp_x, *tmp_y, *tmp_z;
  BzlaBvDomainPtrStack d_c_stack, d_shift_stack, d_ite_stack;
  BzlaBvDomain **tmp_c, **tmp_shift, **tmp_ite, **tmp_z_prev;
  BzlaBvDomain *tmp_res_c;
  BzlaBitVectorPtrStack shift_stack;

  res = true;

  bw = bzla_bv_get_width(d_x->lo);
  assert(bw == bzla_bv_get_width(d_x->hi));
  assert(bw == bzla_bv_get_width(d_z->lo));
  assert(bw == bzla_bv_get_width(d_z->hi));

  BZLA_INIT_STACK(mm, d_c_stack);
  BZLA_INIT_STACK(mm, d_shift_stack);
  BZLA_INIT_STACK(mm, d_ite_stack);
  BZLA_INIT_STACK(mm, shift_stack);

  for (i = 0; i < bw; i++)
  {
    /* slice y into bw ite conditions */
    d     = new_domain(mm);
    d->lo = bzla_bv_slice(mm, d_y->lo, i, i);
    d->hi = bzla_bv_slice(mm, d_y->hi, i, i);
    BZLA_PUSH_STACK(d_c_stack, d);
    /* bw shift propagators */
    d = bzla_bvprop_new_init(mm, bw);
    BZLA_PUSH_STACK(d_shift_stack, d);
    /* bw ite propagators */
    if (i == bw - 1)
      d = bzla_bvprop_new(mm, d_z->lo, d_z->hi);
    else
      d = bzla_bvprop_new_init(mm, bw);
    BZLA_PUSH_STACK(d_ite_stack, d);
    /* shift width */
    bv = bzla_bv_uint64_to_bv(mm, 1 << i, bw);
    BZLA_PUSH_STACK(shift_stack, bv);
  }

  assert(BZLA_COUNT_STACK(d_c_stack) == bw);
  assert(BZLA_COUNT_STACK(d_shift_stack) == bw);
  assert(BZLA_COUNT_STACK(d_ite_stack) == bw);
  assert(BZLA_COUNT_STACK(shift_stack) == bw);

  tmp_x = bzla_bvprop_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvprop_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvprop_new(mm, d_z->lo, d_z->hi);

  do
  {
    progress = false;

    for (i = 0; i < bw; i++)
    {
      /* prev_z = x
       * for i = 0 to bw - 1:
       *   cur_z = ite (y[i:i], prev_z << shift, prev_z)
       *   prev_z = cur_z */

      /* shift = 1 << i */
      bv = BZLA_PEEK_STACK(shift_stack, i);

      tmp_shift  = &d_shift_stack.start[i];
      tmp_z_prev = i ? &d_ite_stack.start[i - 1] : &tmp_x;
      /* prev_z << shift */
      if (!bzla_bvprop_sll_const(
              mm, *tmp_z_prev, *tmp_shift, bv, res_d_x, res_d_z))
      {
        res = false;
        bzla_bvprop_free(mm, *res_d_x);
        bzla_bvprop_free(mm, *res_d_z);
        goto DONE;
      }
      assert(bzla_bvprop_is_valid(mm, *res_d_x));
      assert(bzla_bvprop_is_valid(mm, *res_d_z));
      if (!progress)
      {
        progress = made_progress(
            *tmp_z_prev, 0, *tmp_shift, 0, *res_d_x, 0, *res_d_z, 0);
      }
      bzla_bvprop_free(mm, *tmp_z_prev);
      bzla_bvprop_free(mm, *tmp_shift);
      *tmp_z_prev = *res_d_x;
      *tmp_shift  = *res_d_z;

      /* ite (y[i:i], z << (1 << i), x) */
      tmp_c   = &d_c_stack.start[i];
      tmp_ite = &d_ite_stack.start[i];
      if (!bzla_bvprop_ite(mm,
                           *tmp_c,
                           *tmp_shift,
                           *tmp_z_prev,
                           *tmp_ite,
                           &tmp_res_c,
                           res_d_x,
                           res_d_y,
                           res_d_z))
      {
        res = false;
        bzla_bvprop_free(mm, tmp_res_c);
        bzla_bvprop_free(mm, *res_d_x);
        bzla_bvprop_free(mm, *res_d_y);
        bzla_bvprop_free(mm, *res_d_z);
        goto DONE;
      }
      assert(bzla_bvprop_is_valid(mm, *res_d_x));
      assert(bzla_bvprop_is_valid(mm, *res_d_y));
      assert(bzla_bvprop_is_valid(mm, *res_d_z));
      assert(bzla_bvprop_is_valid(mm, tmp_res_c));
      if (!progress)
      {
        progress = made_progress(*tmp_shift,
                                 *tmp_z_prev,
                                 *tmp_ite,
                                 *tmp_c,
                                 *res_d_x,
                                 *res_d_y,
                                 *res_d_z,
                                 tmp_res_c);
      }
      bzla_bvprop_free(mm, *tmp_shift);
      bzla_bvprop_free(mm, *tmp_z_prev);
      bzla_bvprop_free(mm, *tmp_c);
      bzla_bvprop_free(mm, *tmp_ite);
      *tmp_shift  = *res_d_x;
      *tmp_z_prev = *res_d_y;
      *tmp_ite    = *res_d_z;
      *tmp_c      = tmp_res_c;
    }
  } while (progress);

  /* Collect y bits into the result for d_y. */
  for (i = 0; i < bw; i++)
  {
    d = BZLA_PEEK_STACK(d_c_stack, i);
    assert(bzla_bv_get_width(d->lo) == 1);
    assert(bzla_bv_get_width(d->hi) == 1);
    bzla_bv_set_bit(tmp_y->lo, i, bzla_bv_get_bit(d->lo, 0));
    bzla_bv_set_bit(tmp_y->hi, i, bzla_bv_get_bit(d->hi, 0));
  }

  /* Result for d_z. */
  bzla_bvprop_free(mm, tmp_z);
  tmp_z     = new_domain(mm);
  tmp_z->lo = bzla_bv_copy(mm, d_ite_stack.start[bw - 1]->lo);
  tmp_z->hi = bzla_bv_copy(mm, d_ite_stack.start[bw - 1]->hi);
  assert(bzla_bvprop_is_valid(mm, tmp_x));
  assert(bzla_bvprop_is_valid(mm, tmp_y));
  assert(bzla_bvprop_is_valid(mm, tmp_z));
DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  for (i = 0, n = BZLA_COUNT_STACK(d_c_stack); i < n; i++)
  {
    assert(!BZLA_EMPTY_STACK(d_c_stack));
    assert(!BZLA_EMPTY_STACK(d_shift_stack));
    assert(!BZLA_EMPTY_STACK(d_ite_stack));
    assert(!BZLA_EMPTY_STACK(shift_stack));
    bzla_bvprop_free(mm, BZLA_POP_STACK(d_c_stack));
    bzla_bvprop_free(mm, BZLA_POP_STACK(d_shift_stack));
    bzla_bvprop_free(mm, BZLA_POP_STACK(d_ite_stack));
    bzla_bv_free(mm, BZLA_POP_STACK(shift_stack));
  }
  BZLA_RELEASE_STACK(d_c_stack);
  BZLA_RELEASE_STACK(d_shift_stack);
  BZLA_RELEASE_STACK(d_ite_stack);
  BZLA_RELEASE_STACK(shift_stack);

  return res;
}

bool
bzla_bvprop_and(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  BzlaBitVector *tmp0, *tmp1;

  *res_d_x = new_domain(mm);
  *res_d_y = new_domain(mm);
  *res_d_z = new_domain(mm);

  /* lo_x' = lo_x | lo_z */
  (*res_d_x)->lo = bzla_bv_or(mm, d_x->lo, d_z->lo);

  /* hi_x' = hi_x & ~(~hi_z & lo_y) */
  tmp0 = bzla_bv_not(mm, d_z->hi);
  tmp1 = bzla_bv_and(mm, tmp0, d_y->lo);
  bzla_bv_free(mm, tmp0);
  tmp0 = bzla_bv_not(mm, tmp1);
  bzla_bv_free(mm, tmp1);
  (*res_d_x)->hi = bzla_bv_and(mm, d_x->hi, tmp0);
  bzla_bv_free(mm, tmp0);

  /* lo_y' = lo_y | lo_z */
  (*res_d_y)->lo = bzla_bv_or(mm, d_y->lo, d_z->lo);

  /* hi_y' = hi_y | ~(~hi_z & lo_x) */
  tmp0 = bzla_bv_not(mm, d_z->hi);
  tmp1 = bzla_bv_and(mm, tmp0, d_x->lo);
  bzla_bv_free(mm, tmp0);
  tmp0 = bzla_bv_not(mm, tmp1);
  bzla_bv_free(mm, tmp1);
  (*res_d_y)->hi = bzla_bv_and(mm, d_y->hi, tmp0);
  bzla_bv_free(mm, tmp0);

  /* lo_z' = lo_z | (lo_x & lo_y) */
  tmp0           = bzla_bv_and(mm, d_x->lo, d_y->lo);
  (*res_d_z)->lo = bzla_bv_or(mm, d_z->lo, tmp0);
  bzla_bv_free(mm, tmp0);

  /* hi_z' = hi_z & hi_x & hi_y */
  tmp0           = bzla_bv_and(mm, d_x->hi, d_y->hi);
  (*res_d_z)->hi = bzla_bv_and(mm, d_z->hi, tmp0);
  bzla_bv_free(mm, tmp0);

  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_y)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_or(BzlaMemMgr *mm,
               BzlaBvDomain *d_x,
               BzlaBvDomain *d_y,
               BzlaBvDomain *d_z,
               BzlaBvDomain **res_d_x,
               BzlaBvDomain **res_d_y,
               BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  BzlaBitVector *tmp0, *tmp1;

  *res_d_x = new_domain(mm);
  *res_d_y = new_domain(mm);
  *res_d_z = new_domain(mm);

  /* lo_x' = lo_x | (~hi_y & lo_z) */
  tmp0           = bzla_bv_not(mm, d_y->hi);
  tmp1           = bzla_bv_and(mm, tmp0, d_z->lo);
  (*res_d_x)->lo = bzla_bv_or(mm, d_x->lo, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_x' = hi_x & hi_z */
  (*res_d_x)->hi = bzla_bv_and(mm, d_x->hi, d_z->hi);

  /* lo_y' = lo_y | (~hi_x & lo_z) */
  tmp0           = bzla_bv_not(mm, d_x->hi);
  tmp1           = bzla_bv_and(mm, tmp0, d_x->lo);
  (*res_d_y)->lo = bzla_bv_or(mm, d_y->lo, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_y' = hi_y & hi_z */
  (*res_d_y)->hi = bzla_bv_and(mm, d_y->hi, d_z->hi);

  /* lo_z' = lo_z | lo_x | lo_y */
  tmp0           = bzla_bv_or(mm, d_z->lo, d_x->lo);
  (*res_d_z)->lo = bzla_bv_or(mm, tmp0, d_y->lo);
  bzla_bv_free(mm, tmp0);

  /* hi_z' = hi_z & (hi_x | hi_y) */
  tmp0           = bzla_bv_or(mm, d_x->hi, d_y->hi);
  (*res_d_z)->hi = bzla_bv_and(mm, d_z->hi, tmp0);
  bzla_bv_free(mm, tmp0);

  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_y)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_xor(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  BzlaBitVector *tmp0, *tmp1, *tmp2;
  BzlaBitVector *not_hi_z, *not_hi_y, *not_hi_x;

  *res_d_x = new_domain(mm);
  *res_d_y = new_domain(mm);
  *res_d_z = new_domain(mm);

  not_hi_z = bzla_bv_not(mm, d_z->hi);
  not_hi_y = bzla_bv_not(mm, d_y->hi);
  not_hi_x = bzla_bv_not(mm, d_x->hi);

  /* lo_x' = lo_x | (~hi_z & lo_y) | (lo_z & ~hi_y) */
  tmp0 = bzla_bv_and(mm, not_hi_z, d_y->lo);
  tmp1 = bzla_bv_or(mm, d_x->lo, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, not_hi_y, d_z->lo);
  (*res_d_x)->lo = bzla_bv_or(mm, tmp0, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_x' = hi_x & (hi_z | hi_y) & (~(lo_y & lo_z)) */
  tmp0 = bzla_bv_or(mm, d_z->hi, d_y->hi);
  tmp1 = bzla_bv_and(mm, d_x->hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, d_y->lo, d_z->lo);
  tmp2           = bzla_bv_not(mm, tmp0);
  (*res_d_x)->hi = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);

  /* lo_y' = lo_y | (~hi_z & lo_x) | (lo_z & ~hi_x) */
  tmp0 = bzla_bv_and(mm, not_hi_z, d_x->lo);
  tmp1 = bzla_bv_or(mm, tmp0, d_y->lo);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, d_z->lo, not_hi_x);
  (*res_d_y)->lo = bzla_bv_or(mm, tmp0, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_y' = hi_y & (hi_z | hi_x) & (~(lo_x & lo_z)) */
  tmp0 = bzla_bv_or(mm, d_z->hi, d_x->hi);
  tmp1 = bzla_bv_and(mm, d_y->hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, d_x->lo, d_z->lo);
  tmp2           = bzla_bv_not(mm, tmp0);
  (*res_d_y)->hi = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);

  /* lo_z' = lo_z | (~hi_x & lo_y) | (lo_x & ~hi_y) */
  tmp0 = bzla_bv_and(mm, not_hi_x, d_y->lo);
  tmp1 = bzla_bv_or(mm, d_z->lo, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, d_x->lo, not_hi_y);
  (*res_d_z)->lo = bzla_bv_or(mm, tmp0, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_z' = hi_z & (hi_x | hi_y) & (~(lo_x & lo_y)) */
  tmp0 = bzla_bv_or(mm, d_x->hi, d_y->hi);
  tmp1 = bzla_bv_and(mm, d_z->hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, d_x->lo, d_y->lo);
  tmp2           = bzla_bv_not(mm, tmp0);
  (*res_d_z)->hi = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);
  bzla_bv_free(mm, not_hi_x);
  bzla_bv_free(mm, not_hi_y);
  bzla_bv_free(mm, not_hi_z);
  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_y)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_slice(BzlaMemMgr *mm,
                  BzlaBvDomain *d_x,
                  BzlaBvDomain *d_z,
                  uint32_t upper,
                  uint32_t lower,
                  BzlaBvDomain **res_d_x,
                  BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(upper >= lower);
  assert(upper < bzla_bv_get_width(d_x->lo));
  assert(upper - lower + 1 == bzla_bv_get_width(d_z->lo));

  /* Apply equality propagator on sliced 'x' domain.
   *
   * lo_x' = lo_x[wx-1:upper+1] o lo_x[upper:lower] | lo_z o lo_x[lower - 1:0]
   * hi_x' = hi_x[wx-1:upper+1] o hi_x[upper:lower] & hi_z o hi_x[lower - 1:0]
   *
   * Note: We don't use the propagator described in [1] since it changes the
   *       don't care bits of 'd_x'.
   */

  BzlaBvDomain *sliced_x = new_domain(mm);
  sliced_x->lo           = bzla_bv_slice(mm, d_x->lo, upper, lower);
  sliced_x->hi           = bzla_bv_slice(mm, d_x->hi, upper, lower);

  if (!bzla_bvprop_eq(mm, sliced_x, d_z, res_d_z, 0))
  {
    bzla_bvprop_free(mm, sliced_x);
    return false;
  }
  bzla_bvprop_free(mm, sliced_x);

  uint32_t wx = bzla_bv_get_width(d_x->lo);

  *res_d_x = new_domain(mm);

  BzlaBitVector *lo_x = bzla_bv_copy(mm, (*res_d_z)->lo);
  BzlaBitVector *hi_x = bzla_bv_copy(mm, (*res_d_z)->hi);
  BzlaBitVector *tmp;
  if (lower > 0)
  {
    BzlaBitVector *lower_lo_x = bzla_bv_slice(mm, d_x->lo, lower - 1, 0);
    BzlaBitVector *lower_hi_x = bzla_bv_slice(mm, d_x->hi, lower - 1, 0);
    tmp                       = bzla_bv_concat(mm, lo_x, lower_lo_x);
    bzla_bv_free(mm, lo_x);
    lo_x = tmp;
    tmp  = bzla_bv_concat(mm, hi_x, lower_hi_x);
    bzla_bv_free(mm, hi_x);
    hi_x = tmp;
    bzla_bv_free(mm, lower_lo_x);
    bzla_bv_free(mm, lower_hi_x);
  }

  if (upper < wx - 1)
  {
    BzlaBitVector *upper_lo_x = bzla_bv_slice(mm, d_x->lo, wx - 1, upper + 1);
    BzlaBitVector *upper_hi_x = bzla_bv_slice(mm, d_x->hi, wx - 1, upper + 1);
    tmp                       = bzla_bv_concat(mm, upper_lo_x, lo_x);
    bzla_bv_free(mm, lo_x);
    lo_x = tmp;
    tmp  = bzla_bv_concat(mm, upper_hi_x, hi_x);
    bzla_bv_free(mm, hi_x);
    hi_x = tmp;
    bzla_bv_free(mm, upper_lo_x);
    bzla_bv_free(mm, upper_hi_x);
  }

  assert(bzla_bv_get_width(lo_x) == wx);
  assert(bzla_bv_get_width(hi_x) == wx);
  (*res_d_x)->lo = lo_x;
  (*res_d_x)->hi = hi_x;
  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_concat(BzlaMemMgr *mm,
                   BzlaBvDomain *d_x,
                   BzlaBvDomain *d_y,
                   BzlaBvDomain *d_z,
                   BzlaBvDomain **res_d_x,
                   BzlaBvDomain **res_d_y,
                   BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  bool res;
  uint32_t wy, wz;

  wy = bzla_bv_get_width(d_y->hi);
  assert(wy == bzla_bv_get_width(d_y->lo));
  wz = bzla_bv_get_width(d_z->hi);
  assert(wz == bzla_bv_get_width(d_z->lo));

#if 0
  /* These are the propagators as proposed in [1]. */

  uint32_t wx;
  BzlaBitVector *mask, *zero, *ones, *tmp0, *tmp1;
  BzlaBitVector *lo_x, *hi_x, *lo_y, *hi_y;

  wx = bzla_bv_get_width (d_x->hi);
  assert (wx == bzla_bv_get_width (d_x->lo));

  lo_x = bzla_bv_uext (mm, d_x->lo, wz - wx);
  hi_x = bzla_bv_uext (mm, d_x->hi, wz - wx);
  lo_y = bzla_bv_uext (mm, d_y->lo, wz - wy);
  hi_y = bzla_bv_uext (mm, d_y->hi, wz - wy);

  zero = bzla_bv_zero (mm, wz - wy);
  ones = bzla_bv_ones (mm, wy);
  mask = bzla_bv_concat (mm, zero, ones);

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_z' = lo_z | ((lo_x << wy) | lo_y) */
  tmp0           = bzla_bv_sll_uint32 (mm, lo_x, wy);
  tmp1           = bzla_bv_or (mm, tmp0, lo_y);
  (*res_d_z)->lo = bzla_bv_or (mm, d_z->lo, tmp1);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* hi_z' = hi_z & ((hi_x << wy) | hi_y) */
  tmp0           = bzla_bv_sll_uint32 (mm, hi_x, wy);
  tmp1           = bzla_bv_or (mm, tmp0, hi_y);
  (*res_d_z)->hi = bzla_bv_and (mm, d_z->hi, tmp1);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* lo_x' = lo_x | (lo_z >> wy) */
  tmp0           = bzla_bv_srl_uint32 (mm, d_z->lo, wy);
  tmp1           = bzla_bv_or (mm, lo_x, tmp0);
  (*res_d_x)->lo = bzla_bv_slice (mm, tmp1, wx - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* hi_x' = hi_x & (hi_z >> wy) */
  tmp0           = bzla_bv_srl_uint32 (mm, d_z->hi, wy);
  tmp1           = bzla_bv_and (mm, hi_x, tmp0);
  (*res_d_x)->hi = bzla_bv_slice (mm, tmp1, wx - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* lo_y' = lo_y | (lo_z & mask */
  tmp0           = bzla_bv_and (mm, d_z->lo, mask);
  tmp1           = bzla_bv_or (mm, lo_y, tmp0);
  (*res_d_y)->lo = bzla_bv_slice (mm, tmp1, wy - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* hi_y' = hi_y & (hi_z & mask) */
  tmp0           = bzla_bv_and (mm, d_z->hi, mask);
  tmp1           = bzla_bv_and (mm, hi_y, tmp0);
  (*res_d_y)->hi = bzla_bv_slice (mm, tmp1, wy - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  bzla_bv_free (mm, lo_x);
  bzla_bv_free (mm, hi_x);
  bzla_bv_free (mm, lo_y);
  bzla_bv_free (mm, hi_y);

  bzla_bv_free (mm, zero);
  bzla_bv_free (mm, ones);
  bzla_bv_free (mm, mask);
  res = bzla_bvprop_is_valid (mm, *res_d_x)
        && bzla_bvprop_is_valid (mm, *res_d_y)
        && bzla_bvprop_is_valid (mm, *res_d_z);
#else
  /* These propagators are decompositional (simpler). */

  BzlaBitVector *lo_zx, *lo_zy, *hi_zx, *hi_zy;
  BzlaBvDomain *d_zx, *d_zy;

  /* z = zx o zy */
  lo_zx = bzla_bv_slice(mm, d_z->lo, wz - 1, wy);
  hi_zx = bzla_bv_slice(mm, d_z->hi, wz - 1, wy);
  lo_zy = bzla_bv_slice(mm, d_z->lo, wy - 1, 0);
  hi_zy = bzla_bv_slice(mm, d_z->hi, wy - 1, 0);
  d_zx  = bzla_bvprop_new(mm, lo_zx, hi_zx);
  d_zy  = bzla_bvprop_new(mm, lo_zy, hi_zy);

  *res_d_z = new_domain(mm);

  /* res_z = prop(d_zx = d_x) o prop(d_zy o d_y) */
  if (!bzla_bvprop_eq(mm, d_zx, d_x, res_d_x, 0))
  {
    res = false;
    goto DONE;
  }
  if (!bzla_bvprop_eq(mm, d_zy, d_y, res_d_y, 0))
  {
    res = false;
    goto DONE;
  }

  (*res_d_z)->lo = bzla_bv_concat(mm, (*res_d_x)->lo, (*res_d_y)->lo);
  (*res_d_z)->hi = bzla_bv_concat(mm, (*res_d_x)->hi, (*res_d_y)->hi);

  res = bzla_bvprop_is_valid(mm, *res_d_x) && bzla_bvprop_is_valid(mm, *res_d_y)
        && bzla_bvprop_is_valid(mm, *res_d_z);
DONE:
  bzla_bv_free(mm, lo_zx);
  bzla_bv_free(mm, lo_zy);
  bzla_bv_free(mm, hi_zx);
  bzla_bv_free(mm, hi_zy);
  bzla_bvprop_free(mm, d_zx);
  bzla_bvprop_free(mm, d_zy);
#endif
  return res;
}

bool
bzla_bvprop_sext(BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_z);

  uint32_t wx, wn, wz, lo_x_lsb, hi_x_lsb;
  BzlaBitVector *tmp0, *tmp1, *tmp2;
  BzlaBitVector *slice_lo_z_hi, *slice_hi_z_hi;
  BzlaBitVector *redor, *redand, *x_or_z, *x_and_z;

  *res_d_x = new_domain(mm);
  *res_d_z = new_domain(mm);

  wx = bzla_bv_get_width(d_x->hi);
  assert(wx == bzla_bv_get_width(d_x->lo));
  wz = bzla_bv_get_width(d_z->hi);
  assert(wz == bzla_bv_get_width(d_z->lo));
  wn = wz - wx;
  assert(wn);

  lo_x_lsb = bzla_bv_get_bit(d_x->lo, wx - 1);
  hi_x_lsb = bzla_bv_get_bit(d_x->hi, wx - 1);

  /* Note: The propagators for x and z from [1] are incorrect!
   * E.g. for x = 1 and z = 001 we expect an invalid result, but these
   * propagators produce x' = 1 and z' = 111. */

  if (wx > 1)
  {
    tmp0   = bzla_bv_slice(mm, d_x->lo, wx - 2, 0);
    tmp1   = bzla_bv_slice(mm, d_z->lo, wx - 2, 0);
    x_or_z = bzla_bv_or(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    tmp0    = bzla_bv_slice(mm, d_x->hi, wx - 2, 0);
    tmp1    = bzla_bv_slice(mm, d_z->hi, wx - 2, 0);
    x_and_z = bzla_bv_and(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
  }
  slice_lo_z_hi = wx > 1 ? bzla_bv_slice(mm, d_z->lo, wz - 1, wx - 1) : d_z->lo;
  slice_hi_z_hi = wx > 1 ? bzla_bv_slice(mm, d_z->hi, wz - 1, wx - 1) : d_z->hi;

  redor  = bzla_bv_redor(mm, slice_lo_z_hi);
  redand = bzla_bv_redand(mm, slice_hi_z_hi);

  /**
   * lo_x' = (lo_x[wx-1:wx-1] | redor (lo_z[wz-1:wx-1]))
   *         :: (lo_x[wx-2:0] | lo_z[wx-2:0])
   */
  tmp1 = bzla_bv_slice(mm, d_x->lo, wx - 1, wx - 1);
  tmp0 = bzla_bv_or(mm, tmp1, redor);
  bzla_bv_free(mm, tmp1);
  if (wx > 1)
  {
    (*res_d_x)->lo = bzla_bv_concat(mm, tmp0, x_or_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_x)->lo = tmp0;
  }

  /**
   * hi_x' = (hi_x[wx-1:wx-1] & redand (hi_z[wz-1:wx-1]))
   *         :: (hi_x[wx-2:0] & hi_z[wx-2:0])
   */
  tmp1 = bzla_bv_slice(mm, d_x->hi, wx - 1, wx - 1);
  tmp0 = bzla_bv_and(mm, tmp1, redand);
  bzla_bv_free(mm, tmp1);
  if (wx > 1)
  {
    (*res_d_x)->hi = bzla_bv_concat(mm, tmp0, x_and_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_x)->hi = tmp0;
  }

  /**
   * lo_z' = (lo_z[wz-1:wx-1]
   *          | sext(redor (lo_z[wz-1:wx-1]), wn)
   *          | sext(lo_x[wx-1:wx-1], wn))
   *         :: (lo_z[wx-2:0] | lo_x[wx-2:0])
   */
  tmp0 = lo_x_lsb ? bzla_bv_ones(mm, wn + 1) : bzla_bv_zero(mm, wn + 1);
  tmp1 = bzla_bv_or(mm, slice_lo_z_hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp2 = bzla_bv_sext(mm, redor, wn);
  tmp0 = bzla_bv_or(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);
  if (wx > 1)
  {
    (*res_d_z)->lo = bzla_bv_concat(mm, tmp0, x_or_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_z)->lo = tmp0;
  }

  /**
   * hi_z' = (hi_z[[wz-1:wx-1]
   *          & sext(redand (lo_z[wz-1:wx-1]), wn)
   *          & sext(hi_x[wx-1:wx-1], wn))
   *         :: (hi_z[wx-2:0] & hi_x[wx-2:0])
   */
  tmp0 = hi_x_lsb ? bzla_bv_ones(mm, wn + 1) : bzla_bv_zero(mm, wn + 1);
  tmp1 = bzla_bv_and(mm, slice_hi_z_hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp2 = bzla_bv_sext(mm, redand, wn);
  tmp0 = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);
  if (wx > 1)
  {
    (*res_d_z)->hi = bzla_bv_concat(mm, tmp0, x_and_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_z)->hi = tmp0;
  }

  if (wx > 1)
  {
    bzla_bv_free(mm, x_or_z);
    bzla_bv_free(mm, x_and_z);
    bzla_bv_free(mm, slice_lo_z_hi);
    bzla_bv_free(mm, slice_hi_z_hi);
  }
  bzla_bv_free(mm, redor);
  bzla_bv_free(mm, redand);

#if 0
  /* These are the propagators from [1] which are incorrect!
   * E.g. for x = 1 and z = 001 we expect an invalid result, but these
   * propagators produce x' = 1 and z' = 111. */

  uint32_t i, lo_z_bit, hi_z_bit;
  BzlaBvDomain *tmp_x = bzla_bvprop_new (mm, d_x->lo, d_x->hi);

  /**
   * lo_x' = lo_x | (lo_z & mask1) with mask1 = 0_[wn] :: ~0_[wx]
   * simplifies to
   * lo_x' = lo_x | lo_z[wx-1:0]
   */
  slice = bzla_bv_slice (mm, d_z->lo, wx-1, 0);
  (*res_tmp_x)->lo = bzla_bv_or (mm, tmp_x->lo, slice);
  bzla_bv_free (mm, slice);

  /**
   * hi_x' = hi_x & (hi_z & mask1)
   * simplifies to
   * hi_x' = hi_x & hi_z[wx-1:0]
   */
  slice = bzla_bv_slice (mm, d_z->hi, wx-1, 0);
  (*res_tmp_x)->hi = bzla_bv_and (mm, tmp_x->hi, slice);
  bzla_bv_free (mm, slice);

  if (!lo_x_lsb && !hi_x_lsb)     /* sign bit 0 */
  {
SEXT_SIGN_0:
    /**
     * lo_z' = (lo_x | mask2) | lo_z with mask2 = 0_[wx+wn]
     * simplifies to
     * lo_x' = uext(lo_x, wn) | lo_z
     */
    tmp0 = bzla_bv_uext(mm, tmp_x->lo, wn);
    (*res_d_z)->lo = bzla_bv_or (mm, d_z->lo, tmp0);
    bzla_bv_free (mm, tmp0);

    /**
     * hi_z' = (hi_x | mask2) & hi_z
     * simplifies to
     * hi_z' = uext(hi_x, wn) & hi_z
     */
    tmp0 = bzla_bv_uext(mm, tmp_x->hi, wn);
    (*res_d_z)->hi = bzla_bv_and (mm, d_z->hi, tmp0);
    bzla_bv_free (mm, tmp0);
  }
  else if (lo_x_lsb && hi_x_lsb)  /* sign bit 1 */
  {
SEXT_SIGN_1:
    tmp0 = bzla_bv_ones (mm, wn);
    /**
     * lo_z' = lo_x | mask2 with mask2 = ~0_[wn] :: 0_[wx]
     * simplifies to
     * lo_z' = ~0_[wn] :: lo_x
     */
    (*res_d_z)->lo = bzla_bv_concat (mm, tmp0, tmp_x->lo);
    /**
     * hi_z' = hi_x | mask2
     * simplifies to
     * hi_z' = ~0_[wn] :: hi_x
     */
    (*res_d_z)->hi = bzla_bv_concat (mm, tmp0, tmp_x->hi);
    bzla_bv_free (mm, tmp0);
  }
  else                            /* sign bit x */
  {
    assert (!lo_x_lsb && hi_x_lsb);

    for (i = wz - 1; i >= wx - 1; i--)
    {
      lo_z_bit = bzla_bv_get_bit (d_z->lo, i);
      hi_z_bit = bzla_bv_get_bit (d_z->hi, i);
      /* if exists z_i = 0 with i >= wx - 1 apply rule for zero sign bit */
      if (!lo_z_bit && !hi_z_bit)
      {
        bzla_bv_set_bit (tmp_x->lo, wx - 1, 0);
        goto SEXT_SIGN_0;
      }
      /* if exists z_i = 1 with i >= wx - 1 apply rule for one sign bit */
      if (lo_z_bit && hi_z_bit)
      {
        bzla_bv_set_bit (tmp_x->lo, wx - 1, 1);
        goto SEXT_SIGN_1;
      }
    }
    /**
     * lo_z' = lo_z | (lo_x | mask3) with mask3 = 0_[wz]
     * simplifies to
     * lo_x' = lo_z | uext(lo_x, wn)
     */
    tmp0 = bzla_bv_uext (mm, tmp_x->lo, wn);
    (*res_d_x)->lo = bzla_bv_or (mm, d_z->lo, tmp0);
    bzla_bv_free (mm, tmp0);

    /**
     * hi_z' = hi_z & (hi_x | mask2) with mask2 = ~0_[wn] :: 0_[wx]
     * simplifies to
     * hi_z' = hi_z & (~0_[wn] :: hi_x)
     */
    tmp0 = bzla_bv_ones (mm, wn);
    tmp1 = bzla_bv_concat (mm, tmp0, tmp_x->hi);
    (*res_d_x)->lo = bzla_bv_and (mm, d_z->hi, tmp1);
    bzla_bv_free (mm, tmp0);
    bzla_bv_free (mm, tmp1);
  }
  bzla_bvprop_free (mm, tmp_x);
#endif
  return bzla_bvprop_is_valid(mm, *res_d_x)
         && bzla_bvprop_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_ite(BzlaMemMgr *mm,
                BzlaBvDomain *d_c,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_c,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_c);
  assert(bzla_bvprop_is_valid(mm, d_c));
  assert(bzla_bv_get_width(d_c->lo) == 1);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_c);
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  bool res;
  uint32_t bw;
  bool progress, c_is_fixed;
  BzlaBvDomain *tmp_bvc, *res_tmp_bvc, *tmp_x, *tmp_y, *tmp_z, *tmp_c;
  BzlaBitVector *not_hi_x, *not_lo_x, *not_hi_y, *not_hi_z, *not_hi_bvc;
  BzlaBitVector *ones, *zero, *tmp0, *tmp1, *tmp2;

  res = true;

  bw = bzla_bv_get_width(d_x->lo);
  assert(bw == bzla_bv_get_width(d_x->hi));
  assert(bw == bzla_bv_get_width(d_y->lo));
  assert(bw == bzla_bv_get_width(d_y->hi));
  assert(bw == bzla_bv_get_width(d_z->lo));
  assert(bw == bzla_bv_get_width(d_z->hi));

  ones = bzla_bv_ones(mm, bw);
  zero = bzla_bv_zero(mm, bw);

  if (bzla_bvprop_is_fixed(mm, d_c))
  {
    c_is_fixed = true;
    if (bzla_bv_get_bit(d_c->lo, 0) == 0)
    {
      tmp_bvc = bzla_bvprop_new(mm, zero, zero);
    }
    else
    {
      assert(bzla_bv_get_bit(d_c->lo, 0) == 1);
      tmp_bvc = bzla_bvprop_new(mm, ones, ones);
    }
  }
  else
  {
    c_is_fixed = false;
    tmp_bvc    = bzla_bvprop_new_init(mm, bw);
  }

  tmp_x = bzla_bvprop_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvprop_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvprop_new(mm, d_z->lo, d_z->hi);
  tmp_c = bzla_bvprop_new(mm, d_c->lo, d_c->hi);

  not_hi_x   = 0;
  not_lo_x   = 0;
  not_hi_y   = 0;
  not_hi_z   = 0;
  not_hi_bvc = 0;

  do
  {
    progress = false;

    res_tmp_bvc = new_domain(mm);
    *res_d_x    = new_domain(mm);
    *res_d_y    = new_domain(mm);
    *res_d_z    = new_domain(mm);

    if (not_hi_x) bzla_bv_free(mm, not_hi_x);
    if (not_lo_x) bzla_bv_free(mm, not_lo_x);
    if (not_hi_y) bzla_bv_free(mm, not_hi_y);
    if (not_hi_z) bzla_bv_free(mm, not_hi_z);
    if (not_hi_bvc) bzla_bv_free(mm, not_hi_bvc);

    not_hi_x   = bzla_bv_not(mm, tmp_x->hi);
    not_lo_x   = bzla_bv_not(mm, tmp_x->lo);
    not_hi_y   = bzla_bv_not(mm, tmp_y->hi);
    not_hi_z   = bzla_bv_not(mm, tmp_z->hi);
    not_hi_bvc = bzla_bv_not(mm, tmp_bvc->hi);

    /* lo_bvc' = lo_bvc | (lo_z & (~hi_y)) | ((~hi_z) & lo_y) */
    tmp0            = bzla_bv_and(mm, not_hi_z, tmp_y->lo);
    tmp1            = bzla_bv_and(mm, tmp_z->lo, not_hi_y);
    tmp2            = bzla_bv_or(mm, tmp0, tmp1);
    res_tmp_bvc->lo = bzla_bv_or(mm, tmp_bvc->lo, tmp2);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* hi_bvc' = hi_bvc & (~lo_z | hi_x) & (hi_z | (~lo_x)) */
    tmp0 = bzla_bv_or(mm, tmp_z->hi, not_lo_x);
    tmp1 = bzla_bv_not(mm, tmp_z->lo);
    tmp2 = bzla_bv_or(mm, tmp1, tmp_x->hi);
    bzla_bv_free(mm, tmp1);
    tmp1            = bzla_bv_and(mm, tmp0, tmp2);
    res_tmp_bvc->hi = bzla_bv_and(mm, tmp_bvc->hi, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* lo_x' = lo_x | (lo_z & (lo_bvc | (~hi_y))) */
    tmp0           = bzla_bv_or(mm, tmp_bvc->lo, not_hi_y);
    tmp1           = bzla_bv_and(mm, tmp_z->lo, tmp0);
    (*res_d_x)->lo = bzla_bv_or(mm, tmp_x->lo, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* hi_x' = hi_x & (~((~hi_z) & (lo_bvc | lo_y))) */
    tmp0           = bzla_bv_or(mm, tmp_bvc->lo, tmp_y->lo);
    tmp1           = bzla_bv_and(mm, not_hi_z, tmp0);
    tmp2           = bzla_bv_not(mm, tmp1);
    (*res_d_x)->hi = bzla_bv_and(mm, tmp_x->hi, tmp2);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* lo_y' = lo_y | (lo_z & ((~hi_bvc) | (~hi_x))) */
    tmp0           = bzla_bv_or(mm, not_hi_bvc, not_hi_x);
    tmp1           = bzla_bv_and(mm, tmp_z->lo, tmp0);
    (*res_d_y)->lo = bzla_bv_or(mm, tmp_y->lo, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* hi_y' = hi_y & (hi_z | (hi_bvc & ~lo_x)) */
    tmp0           = bzla_bv_and(mm, tmp_bvc->hi, not_lo_x);
    tmp1           = bzla_bv_or(mm, tmp_z->hi, tmp0);
    (*res_d_y)->hi = bzla_bv_and(mm, tmp_y->hi, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* lo_z' = lo_z | (lo_bvc & lo_x) | ((~hi_bvc) & lo_y) | (lo_x & lo_y) */
    tmp0 = bzla_bv_and(mm, tmp_x->lo, tmp_y->lo);
    tmp1 = bzla_bv_and(mm, not_hi_bvc, tmp_y->lo);
    tmp2 = bzla_bv_or(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    tmp0           = bzla_bv_and(mm, tmp_bvc->lo, tmp_x->lo);
    tmp1           = bzla_bv_or(mm, tmp0, tmp2);
    (*res_d_z)->lo = bzla_bv_or(mm, tmp_z->lo, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* hi_z' = hi_z & (~lo_bvc | hi_x) & (hi_bvc | hi_y) & (hi_x | hi_y) */
    tmp0 = bzla_bv_or(mm, tmp_x->hi, tmp_y->hi);
    tmp1 = bzla_bv_or(mm, tmp_bvc->hi, tmp_y->hi);
    tmp2 = bzla_bv_and(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    tmp0 = bzla_bv_not(mm, tmp_bvc->lo);
    tmp1 = bzla_bv_or(mm, tmp0, tmp_x->hi);
    bzla_bv_free(mm, tmp0);
    tmp0           = bzla_bv_and(mm, tmp1, tmp2);
    (*res_d_z)->hi = bzla_bv_and(mm, tmp_z->hi, tmp0);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    if (!bzla_bvprop_is_valid(mm, res_tmp_bvc)
        || !bzla_bvprop_is_valid(mm, *res_d_x)
        || !bzla_bvprop_is_valid(mm, *res_d_y)
        || !bzla_bvprop_is_valid(mm, *res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, tmp_x);
      bzla_bvprop_free(mm, tmp_y);
      bzla_bvprop_free(mm, tmp_z);
      bzla_bvprop_free(mm, res_tmp_bvc);
      tmp_x = *res_d_x;
      tmp_y = *res_d_y;
      tmp_z = *res_d_z;
      goto DONE;
    }

    if (bw > 1 && !progress)
    {
      progress = made_progress(tmp_x,
                               tmp_y,
                               tmp_z,
                               tmp_bvc,
                               *res_d_x,
                               *res_d_y,
                               *res_d_z,
                               res_tmp_bvc);
    }

    bzla_bvprop_free(mm, tmp_x);
    bzla_bvprop_free(mm, tmp_y);
    bzla_bvprop_free(mm, tmp_z);
    bzla_bvprop_free(mm, tmp_bvc);
    tmp_x   = *res_d_x;
    tmp_y   = *res_d_y;
    tmp_z   = *res_d_z;
    tmp_bvc = res_tmp_bvc;

    if (bw > 1 && !c_is_fixed && progress)
    {
      if (!bzla_bvprop_sext(mm, tmp_c, tmp_bvc, res_d_c, &res_tmp_bvc))
      {
        res = false;
        bzla_bvprop_free(mm, tmp_c);
        tmp_c = *res_d_c;
        bzla_bvprop_free(mm, res_tmp_bvc);
        goto DONE;
      }
      bzla_bvprop_free(mm, tmp_c);
      bzla_bvprop_free(mm, tmp_bvc);
      tmp_c   = *res_d_c;
      tmp_bvc = res_tmp_bvc;
    }
  } while (progress);

  assert(bzla_bvprop_is_valid(mm, tmp_bvc));
  assert(bzla_bvprop_is_valid(mm, tmp_c));
  assert(bzla_bvprop_is_valid(mm, tmp_x));
  assert(bzla_bvprop_is_valid(mm, tmp_y));
  assert(bzla_bvprop_is_valid(mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;
  *res_d_c = tmp_c;

  bzla_bv_free(mm, not_hi_x);
  bzla_bv_free(mm, not_lo_x);
  bzla_bv_free(mm, not_hi_y);
  bzla_bv_free(mm, not_hi_z);
  bzla_bv_free(mm, not_hi_bvc);

  bzla_bv_free(mm, ones);
  bzla_bv_free(mm, zero);
  bzla_bvprop_free(mm, tmp_bvc);

  return res;
}

bool
bzla_bvprop_add(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  bool progress, res;
  uint32_t bw;
  BzlaBitVector *one;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_z;
  BzlaBvDomain *tmp_cin, *tmp_cout;
  BzlaBvDomain *tmp_x_xor_y, *tmp_x_and_y;
  BzlaBvDomain *tmp_cin_and_x_xor_y;

  res = true;

  bw = bzla_bv_get_width(d_x->lo);
  assert(bw == bzla_bv_get_width(d_x->hi));
  assert(bw == bzla_bv_get_width(d_y->lo));
  assert(bw == bzla_bv_get_width(d_y->hi));
  assert(bw == bzla_bv_get_width(d_z->lo));
  assert(bw == bzla_bv_get_width(d_z->hi));
  one = bzla_bv_one(mm, bw);

  /* cin = x...x0 */
  tmp_cin = bzla_bvprop_new_init(mm, bw);
  bzla_bv_set_bit(tmp_cin->hi, 0, 0);
  /* cout = x...x */
  tmp_cout = bzla_bvprop_new_init(mm, bw);

  /**
   * full adder:
   * z    = x ^ y ^ cin
   * cout = (x & y) | (cin & (x ^ y))
   * cin  = cout << 1
   */

  tmp_x = bzla_bvprop_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvprop_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvprop_new(mm, d_z->lo, d_z->hi);

  tmp_x_xor_y         = bzla_bvprop_new_init(mm, bw);
  tmp_x_and_y         = bzla_bvprop_new_init(mm, bw);
  tmp_cin_and_x_xor_y = bzla_bvprop_new_init(mm, bw);

  do
  {
    progress = false;

    /* x_xor_y = x ^ y */
    if (!bzla_bvprop_xor(
            mm, tmp_x, tmp_y, tmp_x_xor_y, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_y);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_x));
    assert(bzla_bvprop_is_valid(mm, *res_d_y));
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress(
          tmp_x, tmp_y, tmp_x_xor_y, 0, *res_d_x, *res_d_y, *res_d_z, 0);
    }
    bzla_bvprop_free(mm, tmp_x);
    bzla_bvprop_free(mm, tmp_y);
    bzla_bvprop_free(mm, tmp_x_xor_y);
    tmp_x       = *res_d_x;
    tmp_y       = *res_d_y;
    tmp_x_xor_y = *res_d_z;

    /* z = x_xor_y ^ cin */
    if (!bzla_bvprop_xor(
            mm, tmp_x_xor_y, tmp_cin, tmp_z, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_y);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_x));
    assert(bzla_bvprop_is_valid(mm, *res_d_y));
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress(
          tmp_x_xor_y, tmp_cin, tmp_z, 0, *res_d_x, *res_d_y, *res_d_z, 0);
    }
    bzla_bvprop_free(mm, tmp_x_xor_y);
    bzla_bvprop_free(mm, tmp_cin);
    bzla_bvprop_free(mm, tmp_z);
    tmp_x_xor_y = *res_d_x;
    tmp_cin     = *res_d_y;
    tmp_z       = *res_d_z;

    /* x_and_y = x & y */
    if (!bzla_bvprop_and(
            mm, tmp_x, tmp_y, tmp_x_and_y, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_y);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_x));
    assert(bzla_bvprop_is_valid(mm, *res_d_y));
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress(
          tmp_x, tmp_y, tmp_x_and_y, 0, *res_d_x, *res_d_y, *res_d_z, 0);
    }
    bzla_bvprop_free(mm, tmp_x);
    bzla_bvprop_free(mm, tmp_y);
    bzla_bvprop_free(mm, tmp_x_and_y);
    tmp_x       = *res_d_x;
    tmp_y       = *res_d_y;
    tmp_x_and_y = *res_d_z;

    /* cin_and_x_xor_y = cin & x_xor_y */
    if (!bzla_bvprop_and(mm,
                         tmp_cin,
                         tmp_x_xor_y,
                         tmp_cin_and_x_xor_y,
                         res_d_x,
                         res_d_y,
                         res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_y);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_x));
    assert(bzla_bvprop_is_valid(mm, *res_d_y));
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress(tmp_cin,
                               tmp_x_xor_y,
                               tmp_cin_and_x_xor_y,
                               0,
                               *res_d_x,
                               *res_d_y,
                               *res_d_z,
                               0);
    }
    bzla_bvprop_free(mm, tmp_cin);
    bzla_bvprop_free(mm, tmp_x_xor_y);
    bzla_bvprop_free(mm, tmp_cin_and_x_xor_y);
    tmp_cin             = *res_d_x;
    tmp_x_xor_y         = *res_d_y;
    tmp_cin_and_x_xor_y = *res_d_z;

    /* cout = x_and_y | cin_and_x_xor_y */
    if (!bzla_bvprop_or(mm,
                        tmp_x_and_y,
                        tmp_cin_and_x_xor_y,
                        tmp_cout,
                        res_d_x,
                        res_d_y,
                        res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_y);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_x));
    assert(bzla_bvprop_is_valid(mm, *res_d_y));
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress(tmp_x_and_y,
                               tmp_cin_and_x_xor_y,
                               tmp_cout,
                               0,
                               *res_d_x,
                               *res_d_y,
                               *res_d_z,
                               0);
    }
    bzla_bvprop_free(mm, tmp_x_and_y);
    bzla_bvprop_free(mm, tmp_cin_and_x_xor_y);
    bzla_bvprop_free(mm, tmp_cout);
    tmp_x_and_y         = *res_d_x;
    tmp_cin_and_x_xor_y = *res_d_y;
    tmp_cout            = *res_d_z;

    /* cin  = cout << 1 */
    if (!bzla_bvprop_sll_const(mm, tmp_cout, tmp_cin, one, res_d_x, res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    assert(bzla_bvprop_is_valid(mm, *res_d_x));
    assert(bzla_bvprop_is_valid(mm, *res_d_z));
    if (!progress)
    {
      progress =
          made_progress(tmp_cout, 0, tmp_cin, 0, *res_d_x, 0, *res_d_z, 0);
    }
    bzla_bvprop_free(mm, tmp_cout);
    bzla_bvprop_free(mm, tmp_cin);
    tmp_cout = *res_d_x;
    tmp_cin  = *res_d_z;
  } while (progress);

  assert(bzla_bvprop_is_valid(mm, tmp_x));
  assert(bzla_bvprop_is_valid(mm, tmp_y));
  assert(bzla_bvprop_is_valid(mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  bzla_bvprop_free(mm, tmp_cin);
  bzla_bvprop_free(mm, tmp_cout);
  bzla_bvprop_free(mm, tmp_x_xor_y);
  bzla_bvprop_free(mm, tmp_x_and_y);
  bzla_bvprop_free(mm, tmp_cin_and_x_xor_y);

  bzla_bv_free(mm, one);

  return res;
}

bool
bzla_bvprop_mul(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvprop_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvprop_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvprop_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  /* z_[bw] = x_[bw] * y_[bw]
   * rewrites to
   * ite (y[bw-1:bw-1], x << (bw - 1), 0)
   *   + ite (y[bw-2:bw-2], x << (bw-2), 0)
   *   + ...
   *   + ite (y[1:1], x << 1, 0)
   *   + ite (y[0:0], x, 0)
   */

  uint32_t i, bw, n;
  bool res, progress;
  BzlaBitVector *bv;
  BzlaBvDomain *d, *tmp_x, *tmp_y, *tmp_z, *tmp_zero;
  BzlaBvDomain **tmp_c, **tmp_shift, **tmp_ite, **tmp0, **tmp1, **tmp_add;
  BzlaBvDomain *tmp_res_c;
  BzlaBvDomainPtrStack d_c_stack, d_shift_stack, d_ite_stack, d_add_stack;
  BzlaBitVectorPtrStack shift_stack;

  res = true;

  BZLA_INIT_STACK(mm, d_c_stack);
  BZLA_INIT_STACK(mm, d_shift_stack);
  BZLA_INIT_STACK(mm, d_ite_stack);
  BZLA_INIT_STACK(mm, d_add_stack);
  BZLA_INIT_STACK(mm, shift_stack);

  bw = bzla_bv_get_width(d_x->lo);
  assert(bw == bzla_bv_get_width(d_x->hi));
  assert(bw == bzla_bv_get_width(d_y->lo));
  assert(bw == bzla_bv_get_width(d_y->hi));
  assert(bw == bzla_bv_get_width(d_z->lo));
  assert(bw == bzla_bv_get_width(d_z->hi));

  bv       = bzla_bv_zero(mm, bw);
  tmp_zero = bzla_bvprop_new(mm, bv, bv);
  bzla_bv_free(mm, bv);

  tmp_x = bzla_bvprop_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvprop_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvprop_new(mm, d_z->lo, d_z->hi);

  if (bw == 1)
  {
    /* For bit-width 1, multiplication simplifies to d_z = ite (d_y, x, 0) */
    if (!bzla_bvprop_ite(
            mm, d_y, d_x, tmp_zero, d_z, &tmp_res_c, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      bzla_bvprop_free(mm, tmp_res_c);
      bzla_bvprop_free(mm, *res_d_x);
      bzla_bvprop_free(mm, *res_d_y);
      bzla_bvprop_free(mm, *res_d_z);
      goto DONE;
    }
    bzla_bvprop_free(mm, tmp_x);
    bzla_bvprop_free(mm, tmp_y);
    bzla_bvprop_free(mm, tmp_z);
    tmp_x = *res_d_x;
    tmp_y = tmp_res_c;
    tmp_z = *res_d_z;
    bzla_bvprop_free(mm, *res_d_y);
  }
  else
  {
    /**
     * The full implementation of
     *   ite (y[bw-1:bw-1], x << (bw - 1), 0)
     *     + ite (y[bw-2:bw-2], x << (bw-2), 0)
     *     + ...
     *     + ite (y[1:1], x << 1, 0)
     *     + ite (y[0:0], x, 0)
     * would require n left shift propagators, n ite propagators, and n - 1
     * add propagators (n = bw).
     * We can simplify that since for each ite, the initial result domain is
     * x...x = ite (condition, shift, 0). If the y bit at an index i (and
     * therefore the condition for the i-th ite) is 0, the result of the ite
     * is always 0 (that's the only possible propagation, no invalid results
     * possible). Hence we can skip all 0 bits of y (i.e., all ite with a 0
     * condition), except the last one (the last one is the end result).
     */

    for (i = 0; i < bw; i++)
    {
      n = bw - 1 - i;

      /* if y bit is zero, the result of the ite is zero, skip */
      if (i < bw - 1 && !bzla_bv_get_bit(d_y->lo, n)
          && !bzla_bv_get_bit(d_y->hi, n))
        continue;

      /* slice y into bw ite conditions */
      d     = new_domain(mm);
      d->lo = bzla_bv_slice(mm, d_y->lo, n, n);
      d->hi = bzla_bv_slice(mm, d_y->hi, n, n);
      BZLA_PUSH_STACK(d_c_stack, d);
      /* m shift propagators (m = number of 1 or x bits in y) */
      d = bzla_bvprop_new_init(mm, bw);
      BZLA_PUSH_STACK(d_shift_stack, d);
      /* m ite propagators */
      d = bzla_bvprop_new_init(mm, bw);
      BZLA_PUSH_STACK(d_ite_stack, d);
      /* m - 1 add propagators */
      if (BZLA_COUNT_STACK(d_c_stack) > 1)
      {
        d = bzla_bvprop_new_init(mm, bw);
        BZLA_PUSH_STACK(d_add_stack, d);
      }
      /* shift width */
      bv = bzla_bv_uint64_to_bv(mm, n, bw);
      BZLA_PUSH_STACK(shift_stack, bv);
    }

    /**
     * if m > 0: final add is end result
     * else    : there is a single ite which is the end result
     */
    if (BZLA_COUNT_STACK(d_add_stack))
    {
      /* last adder is end result: d_z = add_[m-1]*/
      d = bzla_bvprop_new(mm, d_z->lo, d_z->hi);
      bzla_bvprop_free(mm, BZLA_POP_STACK(d_add_stack));
      BZLA_PUSH_STACK(d_add_stack, d);
    }
    else
    {
      /**
       * We have at least one ite propagator, even if all bits in y are 0.
       * In case there is only a single ite propagator, it is the end result.
       */
      assert(BZLA_COUNT_STACK(d_ite_stack) == 1);
      if (BZLA_COUNT_STACK(d_ite_stack))
      {
        d = bzla_bvprop_new(mm, d_z->lo, d_z->hi);
        bzla_bvprop_free(mm, BZLA_POP_STACK(d_ite_stack));
        BZLA_PUSH_STACK(d_ite_stack, d);
      }
    }

    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(d_shift_stack));
    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(d_ite_stack));
    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(d_add_stack) + 1);
    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(shift_stack));

    do
    {
      progress = false;

      for (i = 0; i < BZLA_COUNT_STACK(d_c_stack); i++)
      {
        /**
         * x << bw - 1 - m where m is the current bit index.
         * The shift width of the current bit index (!= i) is stored at index i.
         * The current bit index is not explicit here, since we only generate
         * propagators for bits that 1/x (or for the last 0 bit if y = 0).
         */
        bv        = BZLA_PEEK_STACK(shift_stack, i);
        tmp_shift = &d_shift_stack.start[i];
        if (!bzla_bvprop_sll_const(mm, tmp_x, *tmp_shift, bv, res_d_x, res_d_z))
        {
          res = false;
          bzla_bvprop_free(mm, *res_d_x);
          bzla_bvprop_free(mm, *res_d_z);
          goto DONE;
        }
        assert(bzla_bvprop_is_valid(mm, *res_d_x));
        assert(bzla_bvprop_is_valid(mm, *res_d_z));
        if (!progress)
        {
          progress =
              made_progress(tmp_x, 0, *tmp_shift, 0, *res_d_x, 0, *res_d_z, 0);
        }
        bzla_bvprop_free(mm, tmp_x);
        bzla_bvprop_free(mm, *tmp_shift);
        tmp_x      = *res_d_x;
        *tmp_shift = *res_d_z;

        /* ite (y[bw-1-m:bw-1-m], x << bw - 1 - m, 0) */
        tmp_c   = &d_c_stack.start[i];
        tmp_ite = &d_ite_stack.start[i];
        if (!bzla_bvprop_ite(mm,
                             *tmp_c,
                             *tmp_shift,
                             tmp_zero,
                             *tmp_ite,
                             &tmp_res_c,
                             res_d_x,
                             res_d_y,
                             res_d_z))
        {
          res = false;
          bzla_bvprop_free(mm, tmp_res_c);
          bzla_bvprop_free(mm, *res_d_x);
          bzla_bvprop_free(mm, *res_d_y);
          bzla_bvprop_free(mm, *res_d_z);
          goto DONE;
        }
        assert(bzla_bvprop_is_valid(mm, *res_d_x));
        assert(bzla_bvprop_is_valid(mm, *res_d_y));
        assert(bzla_bvprop_is_valid(mm, *res_d_z));
        assert(bzla_bvprop_is_valid(mm, tmp_res_c));
        if (!progress)
        {
          progress = made_progress(*tmp_shift,
                                   tmp_zero,
                                   *tmp_ite,
                                   *tmp_c,
                                   *res_d_x,
                                   *res_d_y,
                                   *res_d_z,
                                   tmp_res_c);
        }
        bzla_bvprop_free(mm, *tmp_shift);
        assert(!bzla_bv_compare(tmp_zero->lo, (*res_d_y)->lo)
               && !bzla_bv_compare(tmp_zero->hi, (*res_d_y)->hi));
        bzla_bvprop_free(mm, *tmp_c);
        bzla_bvprop_free(mm, *tmp_ite);
        *tmp_shift = *res_d_x;
        bzla_bvprop_free(mm, *res_d_y);
        *tmp_ite = *res_d_z;
        *tmp_c   = tmp_res_c;

        /**
         * ite (y[bw-1:bw-1], x << (bw - 1), 0)
         *   + ite (y[bw-2:bw-2], x << (bw-2), 0)
         *   + ...
         *   + ite (y[1:1], x << 1, 0)
         *   + ite (y[0:0], x, 0)
         *
         * Note that we only create ite for bits in y that are 1/x. Thus, we
         * don't create 'bw' adders but 'm = number of 1/x bits - 1' adders.
         */
        if (i > 0)
        {
          tmp0 = i == 1 ? &d_ite_stack.start[i - 1] : &d_add_stack.start[i - 2];
          tmp1 = tmp_ite;
          tmp_add = &d_add_stack.start[i - 1];
          if (!bzla_bvprop_add(
                  mm, *tmp0, *tmp1, *tmp_add, res_d_x, res_d_y, res_d_z))
          {
            res = false;
            bzla_bvprop_free(mm, *res_d_x);
            bzla_bvprop_free(mm, *res_d_y);
            bzla_bvprop_free(mm, *res_d_z);
            goto DONE;
          }
          assert(bzla_bvprop_is_valid(mm, *res_d_x));
          assert(bzla_bvprop_is_valid(mm, *res_d_y));
          assert(bzla_bvprop_is_valid(mm, *res_d_z));
          if (!progress)
          {
            progress = made_progress(
                *tmp0, *tmp1, *tmp_add, 0, *res_d_x, *res_d_y, *res_d_z, 0);
          }
          bzla_bvprop_free(mm, *tmp0);
          bzla_bvprop_free(mm, *tmp1);
          bzla_bvprop_free(mm, *tmp_add);
          *tmp0    = *res_d_x;
          *tmp1    = *res_d_y;
          *tmp_add = *res_d_z;
        }
      }
    } while (progress);

    /* Collect y bits into the result for d_y. */
    for (i = 0, n = 0; i < bw; i++)
    {
      if (i < bw - 1 && !bzla_bv_get_bit(tmp_y->lo, bw - 1 - i)
          && !bzla_bv_get_bit(tmp_y->hi, bw - 1 - i))
        continue;
      assert(n < BZLA_COUNT_STACK(d_c_stack));
      d = BZLA_PEEK_STACK(d_c_stack, n);
      assert(bzla_bv_get_width(d->lo) == 1);
      assert(bzla_bv_get_width(d->hi) == 1);
      bzla_bv_set_bit(tmp_y->lo, bw - 1 - i, bzla_bv_get_bit(d->lo, 0));
      bzla_bv_set_bit(tmp_y->hi, bw - 1 - i, bzla_bv_get_bit(d->hi, 0));
      n += 1;
    }
    assert(n == BZLA_COUNT_STACK(d_c_stack));

    /* Result for d_z. */
    bzla_bvprop_free(mm, tmp_z);
    tmp_z = new_domain(mm);
    if (n > 1)
    {
      tmp_z->lo = bzla_bv_copy(mm, d_add_stack.start[n - 2]->lo);
      tmp_z->hi = bzla_bv_copy(mm, d_add_stack.start[n - 2]->hi);
    }
    else
    {
      assert(n == 1);
      tmp_z->lo = bzla_bv_copy(mm, d_ite_stack.start[0]->lo);
      tmp_z->hi = bzla_bv_copy(mm, d_ite_stack.start[0]->hi);
    }
  }
  assert(bzla_bvprop_is_valid(mm, tmp_x));
  assert(bzla_bvprop_is_valid(mm, tmp_y));
  assert(bzla_bvprop_is_valid(mm, tmp_z));
DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  bzla_bvprop_free(mm, tmp_zero);

  for (i = 0, n = BZLA_COUNT_STACK(d_c_stack); i < n; i++)
  {
    assert(!BZLA_EMPTY_STACK(d_c_stack));
    assert(!BZLA_EMPTY_STACK(d_shift_stack));
    assert(!BZLA_EMPTY_STACK(d_ite_stack));
    assert(!BZLA_EMPTY_STACK(shift_stack));
    bzla_bvprop_free(mm, BZLA_POP_STACK(d_c_stack));
    bzla_bvprop_free(mm, BZLA_POP_STACK(d_shift_stack));
    bzla_bvprop_free(mm, BZLA_POP_STACK(d_ite_stack));
    bzla_bv_free(mm, BZLA_POP_STACK(shift_stack));
    if (i < n - 1)
    {
      assert(!BZLA_EMPTY_STACK(d_add_stack));
      bzla_bvprop_free(mm, BZLA_POP_STACK(d_add_stack));
    }
  }
  BZLA_RELEASE_STACK(d_c_stack);
  BZLA_RELEASE_STACK(d_shift_stack);
  BZLA_RELEASE_STACK(d_ite_stack);
  BZLA_RELEASE_STACK(d_add_stack);
  BZLA_RELEASE_STACK(shift_stack);
  return res;
}
