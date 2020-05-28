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

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * (x = s) = t
 * (s = x) = t
 *
 * IC: true
 */
bool
bzla_is_cons_eq_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return true;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x < s = t
 * s < x = t
 *
 * IC:
 * pos_x = 0: ~t \/ xlo != ones
 * pos_x = 1: ~t \/ xhi != 0
 */
bool
bzla_is_cons_ult_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  uint32_t pos_x;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;

  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  if (pos_x == 0)
  {
    return bzla_bv_is_zero(t) || !bzla_bv_is_ones(x->lo);
  }
  return bzla_bv_is_zero(t) || !bzla_bv_is_zero(x->hi);
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x <s s = t
 * s <s x = t
 *
 * IC:
 * pos_x = 0: ~t \/ (const(x) => xlo != smax)
 * pos_x = 1: ~t \/ (const(x) => xlo != smin)
 */
bool
bzla_is_cons_slt_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  uint32_t pos_x;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;

  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  if (pos_x == 0)
  {
    return bzla_bv_is_zero(t) || !bzla_bvdomain_is_fixed(bzla->mm, x)
           || !bzla_bv_is_max_signed(x->lo);
  }
  return bzla_bv_is_zero(t) || !bzla_bvdomain_is_fixed(bzla->mm, x)
         || !bzla_bv_is_min_signed(x->lo);
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x << s = t
 * s << x = t
 *
 * IC:
 * pos_x = 0: \exists y. (y <= ctz(t) /\ mcb(x << y, t))
 * pos_x = 1: t = 0 \/ \exists y. (y <= ctz(t) /\ mcb(x, y))
 */
bool
bzla_is_cons_sll_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t i, pos_x, bw, bw_r, ctz_t;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBvDomain *x_slice;
  BzlaBitVector *max, *t_slice, *right, *left, *tmp;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  res = true;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  bzla_propinfo_set_result(bzla, pi, 0);

  if (ctz_t != bw)
  {
    if (pos_x == 0)
    {
      BzlaBitVectorPtrStack stack;
      BZLA_INIT_STACK(mm, stack);

      for (i = 0; i <= ctz_t; i++)
      {
        x_slice = bzla_bvdomain_slice(mm, x, bw - 1 - i, 0);
        t_slice = bzla_bv_slice(mm, t, bw - 1, i);
        if (bzla_bvdomain_check_fixed_bits(mm, x_slice, t_slice))
        {
          BZLA_PUSH_STACK(stack, t_slice);
        }
        else
        {
          bzla_bv_free(mm, t_slice);
        }
        bzla_bvdomain_free(mm, x_slice);
      }
      res = !BZLA_EMPTY_STACK(stack);
      if (res)
      {
        i     = bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(stack) - 1);
        right = BZLA_PEEK_STACK(stack, i);
        bw_r  = bzla_bv_get_width(right);
        if (bw == bw_r)
        {
          bzla_propinfo_set_result(
              bzla, pi, bzla_bvdomain_new_fixed(mm, right));
        }
        else
        {
          bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
          tmp  = bzla_bvdomain_gen_random(&gen);
          left = bzla_bv_slice(mm, tmp, bw - 1, bw_r);
          bzla_bvdomain_gen_delete(&gen);
          tmp = bzla_bv_concat(mm, left, right);
          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, tmp));
          bzla_bv_free(mm, tmp);
          bzla_bv_free(mm, left);
        }
      }
      while (!BZLA_EMPTY_STACK(stack))
      {
        bzla_bv_free(mm, BZLA_POP_STACK(stack));
      }
      BZLA_RELEASE_STACK(stack);
    }
    else
    {
      max = bzla_bv_uint64_to_bv(mm, ctz_t, bw);
      bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, 0, max);
      res = bzla_bvdomain_gen_has_next(&gen);
      if (res)
      {
        bzla_propinfo_set_result(
            bzla,
            pi,
            bzla_bvdomain_new_fixed(mm, bzla_bvdomain_gen_random(&gen)));
      }
      bzla_bv_free(mm, max);
      bzla_bvdomain_gen_delete(&gen);
    }
  }
  return res;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x >> s = t
 * s >> x = t
 *
 * IC:
 * pos_x = 0: \exists y. (y <= clz(t) /\ mcb(x >> y, t))
 * pos_x = 1: t = 0 \/ \exists y. (y <= clz(t) /\ mcb(x, y))
 */
bool
bzla_is_cons_srl_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t i, pos_x, bw, bw_l, clz_t;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBvDomain *x_slice;
  BzlaBitVector *max, *t_slice, *right, *left, *tmp;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  res = true;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  bzla_propinfo_set_result(bzla, pi, 0);

  if (clz_t != bw)
  {
    if (pos_x == 0)
    {
      BzlaBitVectorPtrStack stack;
      BZLA_INIT_STACK(mm, stack);

      for (i = 0; i <= clz_t; i++)
      {
        x_slice = bzla_bvdomain_slice(mm, x, bw - 1, i);
        t_slice = bzla_bv_slice(mm, t, bw - 1 - i, 0);
        if (bzla_bvdomain_check_fixed_bits(mm, x_slice, t_slice))
        {
          BZLA_PUSH_STACK(stack, t_slice);
        }
        else
        {
          bzla_bv_free(mm, t_slice);
        }
        bzla_bvdomain_free(mm, x_slice);
      }
      res = !BZLA_EMPTY_STACK(stack);
      if (res)
      {
        i    = bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(stack) - 1);
        left = BZLA_PEEK_STACK(stack, i);
        bw_l = bzla_bv_get_width(left);
        if (bw == bw_l)
        {
          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, left));
        }
        else
        {
          bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
          tmp   = bzla_bvdomain_gen_random(&gen);
          right = bzla_bv_slice(mm, tmp, bw - 1 - bw_l, 0);
          bzla_bvdomain_gen_delete(&gen);
          tmp = bzla_bv_concat(mm, left, right);
          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, tmp));
          bzla_bv_free(mm, tmp);
          bzla_bv_free(mm, right);
        }
      }
      while (!BZLA_EMPTY_STACK(stack))
      {
        bzla_bv_free(mm, BZLA_POP_STACK(stack));
      }
      BZLA_RELEASE_STACK(stack);
    }
    else
    {
      max = bzla_bv_uint64_to_bv(mm, clz_t, bw);
      bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, 0, max);
      res = bzla_bvdomain_gen_has_next(&gen);
      if (res)
      {
        bzla_propinfo_set_result(
            bzla,
            pi,
            bzla_bvdomain_new_fixed(mm, bzla_bvdomain_gen_random(&gen)));
      }
      bzla_bv_free(mm, max);
      bzla_bvdomain_gen_delete(&gen);
    }
  }
  return res;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x >>a s = t
 * s >>a x = t
 *
 * IC:
 *
 * pos_x = 0:
 * ((t = 0 \/ t = ones) => \exists y. (y[msb] = t[msb] /\ mcb(x, y))) /\
 * ((t != 0 /\ t != ones) => \exists y. (c => y <= clo(t) /\ ~c => y <= clz(t)
 *                                       /\ mcb(x, y))
 * with c = ((t << y)[msb] = 1)
 *
 * pos_x = 1:
 * t = 0 \/ t = ones \/
 * \exists y. (c => y < clo(t) /\ ~c => y < clz(t) /\ mcb(x, y)
 * with c = (t[msb] = 1)
 */
bool
bzla_is_cons_sra_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res, is_signed;
  uint32_t i, pos_x, bw, bw_l, cnt_t;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBvDomain *x_slice;
  BzlaBitVector *max, *t_slice, *right, *left, *tmp;
  BzlaBvDomainGenerator gen;
  BzlaBvDomainSignedGenerator sgen;
  BzlaMemMgr *mm;

  res = true;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);

  is_signed = bzla_bv_get_bit(t, bw - 1) == 1;
  cnt_t     = is_signed ? bzla_bv_get_num_leading_ones(t)
                    : bzla_bv_get_num_leading_zeros(t);

  bzla_propinfo_set_result(bzla, pi, 0);

  if (!is_signed && bzla_bv_is_zero(t))
  {
    if (pos_x == 0)
    {
      tmp = bzla_bv_zero(mm, bw);
      bzla_bvdomain_gen_signed_init_range(mm, bzla->rng, &sgen, x, tmp, 0);
      bzla_bv_free(mm, tmp);
      res = bzla_bvdomain_gen_signed_has_next(&sgen);
      if (res)
      {
        bzla_propinfo_set_result(
            bzla,
            pi,
            bzla_bvdomain_new_fixed(mm,
                                    bzla_bvdomain_gen_signed_random(&sgen)));
      }
      bzla_bvdomain_gen_signed_delete(&sgen);
    }
  }
  else if (is_signed && bzla_bv_is_ones(t))
  {
    if (pos_x == 0)
    {
      tmp = bzla_bv_ones(mm, bw);
      bzla_bvdomain_gen_signed_init_range(mm, bzla->rng, &sgen, x, 0, tmp);
      bzla_bv_free(mm, tmp);
      res = bzla_bvdomain_gen_signed_has_next(&sgen);
      if (res)
      {
        bzla_propinfo_set_result(
            bzla,
            pi,
            bzla_bvdomain_new_fixed(mm,
                                    bzla_bvdomain_gen_signed_random(&sgen)));
      }
      bzla_bvdomain_gen_signed_delete(&sgen);
    }
  }
  else if (pos_x)
  {
    max = bzla_bv_uint64_to_bv(mm, cnt_t - 1, bw);
    bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, 0, max);
    res = bzla_bvdomain_gen_has_next(&gen);
    if (res)
    {
      bzla_propinfo_set_result(
          bzla,
          pi,
          bzla_bvdomain_new_fixed(mm, bzla_bvdomain_gen_random(&gen)));
    }
    bzla_bv_free(mm, max);
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    BzlaBitVectorPtrStack stack;
    BZLA_INIT_STACK(mm, stack);

    for (i = 0; i < cnt_t; i++)
    {
      x_slice = bzla_bvdomain_slice(mm, x, bw - 1, i);
      t_slice = bzla_bv_slice(mm, t, bw - 1 - i, 0);
      if (bzla_bvdomain_check_fixed_bits(mm, x_slice, t_slice))
      {
        BZLA_PUSH_STACK(stack, t_slice);
      }
      else
      {
        bzla_bv_free(mm, t_slice);
      }
      bzla_bvdomain_free(mm, x_slice);
    }
    res = !BZLA_EMPTY_STACK(stack);
    if (res)
    {
      i    = bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(stack) - 1);
      left = BZLA_PEEK_STACK(stack, i);
      bw_l = bzla_bv_get_width(left);
      if (bw == bw_l)
      {
        bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, left));
      }
      else
      {
        bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
        tmp   = bzla_bvdomain_gen_random(&gen);
        right = bzla_bv_slice(mm, tmp, bw - 1 - bw_l, 0);
        bzla_bvdomain_gen_delete(&gen);
        tmp = bzla_bv_concat(mm, left, right);
        bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, tmp));
        bzla_bv_free(mm, tmp);
        bzla_bv_free(mm, right);
      }
    }

    while (!BZLA_EMPTY_STACK(stack))
    {
      bzla_bv_free(mm, BZLA_POP_STACK(stack));
    }
    BZLA_RELEASE_STACK(stack);
  }
  return res;
}
