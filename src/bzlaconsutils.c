/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

/*
 * Bit-vector operator invertibility checks based on [1] and [2].
 *
 * [1] Aina Niemetz, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare
 *     Tinelli: Solving Quantified Bit-Vectors Using Invertibility Conditions.
 *     CAV (2) 2018: 236-255
 *
 * [2] Aina Niemetz, Mathias Preiner: Ternary Propagation-Based Local Search
 *     for more Bit-Precise Reasoning.
 *     FMCAD 2020: 214-224
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
  (void) bzla;
  (void) pi;
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
  (void) bzla;
  (void) pi;
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
  (void) bzla;
  (void) pi;
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
  (void) bzla;

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

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x * s = t
 * s * x = t
 *
 * IC:
 * (t != 0 => xhi != 0) /\ (odd(t) => xhi[lsb] != 0) /\
 * (!odd(t) => \exists y. (mcb(x, y) /\ ctz(t) >= ctz(y))
 */
bool
bzla_is_cons_mul_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t i, pos_x, ctz_t, bw;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBitVector *tmp;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  bzla_propinfo_set_result(bzla, pi, 0);

  if (!bzla_bv_is_zero(t) && bzla_bv_is_zero(x->hi)) return false;

  if (bzla_bv_get_bit(t, 0) && bzla_bv_get_bit(x->hi, 0) == 0) return false;

  mm  = bzla->mm;
  res = true;
  bw  = bzla_bv_get_width(t);

  if (bzla_bv_get_bit(t, 0) == 0 && !bzla_bvdomain_is_fixed(mm, x))
  {
    tmp = bzla_bv_is_zero(t) ? bzla_bv_zero(mm, bw) : bzla_bv_one(mm, bw);
    bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, 0);
    bzla_bv_free(mm, tmp);
    tmp = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
    ctz_t = bzla_bv_get_num_trailing_zeros(t);
    for (i = 0, res = false; i <= ctz_t; i++)
    {
      if (!bzla_bvdomain_is_fixed_bit_false(x, i))
      {
        res = true;
        break;
      }
    }
    if (res)
    {
      if (ctz_t < bw)
      {
        do
        {
          i = bzla_rng_pick_rand(bzla->rng, 0, ctz_t);
        } while (bzla_bvdomain_is_fixed_bit_false(x, i));
        bzla_bv_set_bit(tmp, i, 1);
      }
      bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, tmp));
    }
    bzla_bv_free(mm, tmp);
  }
  return res;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x / s = t
 * s / x = t
 *
 * IC:
 *
 * pos_x = 0:
 * (t != ones => xhi >= t) /\ (t = 0 => xlo != ones) /\
 * ((t != 0 /\ t != ones /\ t != 1 /\ !mcb(x, t)) =>
 *  (!mulo(2, t) /\ \exists y,o.(mcb(x, y*t + o) /\ y >= 1 /\ o <= c
 *   /\ !mulo(y, t) /\ !addo(y * t, o))))
 * with c = min(y − 1, x hi − y · t)
 *
 * pos_x = 1:
 * (t = ones => (mcb(x, 0) \/ mcb(x, 1))) /\
 * (t != ones => (!mulo(xlo, t) /\
 *                \exists y. (y > 0 /\ mcb(x, y) /\ !mulo(y, t))))
 */
bool
bzla_is_cons_udiv_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t pos_x, bw, t_is_ones, t_is_zero;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBitVector *max, *bv_res;
  BzlaBitVector *zero, *one;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);

  bzla_propinfo_set_result(bzla, pi, 0);

  res       = true;
  t_is_zero = bzla_bv_is_zero(t);
  t_is_ones = bzla_bv_is_ones(t);

  if (pos_x == 0)
  {
    if (!t_is_ones && bzla_bv_compare(x->hi, t) < 0) return false;
    if (t_is_zero && bzla_bv_is_ones(x->lo)) return false;

    if (!t_is_zero && !t_is_ones && !bzla_bv_is_one(t)
        && !bzla_bvdomain_check_fixed_bits(mm, x, t))

    {
      bv_res = bzla_proputils_cons_udiv_const_pos0_aux(bzla, pi);
      res    = bv_res != NULL;
      if (res)
      {
        bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, bv_res));
        bzla_bv_free(mm, bv_res);
      }
    }
  }
  else
  {
    zero = bzla_bv_zero(mm, bw);
    one  = bzla_bv_one(mm, bw);
    if (t_is_ones && !bzla_bvdomain_check_fixed_bits(mm, x, zero)
        && !bzla_bvdomain_check_fixed_bits(mm, x, one))
    {
      bzla_bv_free(mm, zero);
      bzla_bv_free(mm, one);
      return false;
    }

    if (!t_is_ones)
    {
      if (bzla_bv_is_umulo(mm, x->lo, t))
      {
        bzla_bv_free(mm, zero);
        bzla_bv_free(mm, one);
        return false;
      }

      if (!bzla_bvdomain_is_fixed(mm, x))
      {
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, one, 0);
        bv_res = bzla_bvdomain_gen_random(&gen);
        while (bzla_bv_is_umulo(mm, bv_res, t))
        {
          max = bzla_bv_dec(mm, bv_res);
          bzla_bvdomain_gen_delete(&gen);
          bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, one, max);
          if (!bzla_bvdomain_gen_has_next(&gen))
          {
            res = false;
            bzla_bv_free(mm, max);
            break;
          }
          bv_res = bzla_bvdomain_gen_random(&gen);
          bzla_bv_free(mm, max);
        }
        if (res)
        {
          bzla_propinfo_set_result(
              bzla, pi, bzla_bvdomain_new_fixed(mm, bv_res));
        }
        bzla_bvdomain_gen_delete(&gen);
      }
    }
    bzla_bv_free(mm, zero);
    bzla_bv_free(mm, one);
  }
  return res;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x / s = t
 * s / x = t
 *
 * IC:
 *
 * pos_x = 0:
 * (t = ones => mcb(x, ones)) /\
 * (t != ones =>
 *   (t > (ones - t) => mcb (x, t)) /\
 *   (t < (ones - t) => mcb(x, t) \/ \exists y. (mcb(x, y) /\ y> 2*t))
 *
 * pos_x = 1:
 * mcb(x, 0) \/
 * ((t = ones => mcb(x, 0)) /\ (t != ones => \exists y. (mcb(x, y) /\ y > t)))
 */
bool
bzla_is_cons_urem_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res, check;
  int32_t cmp_t;
  uint32_t pos_x, bw, t_is_ones;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBitVector *tmp, *bv_res;
  BzlaBitVector *zero, *ones;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);

  bzla_propinfo_set_result(bzla, pi, 0);

  res       = true;
  t_is_ones = bzla_bv_is_ones(t);

  if (pos_x == 0)
  {
    check = bzla_bvdomain_check_fixed_bits(mm, x, t);

    if (t_is_ones && !check) return false;

    ones  = bzla_bv_ones(mm, bw);
    tmp   = bzla_bv_sub(mm, ones, t);
    cmp_t = bzla_bv_compare(t, tmp);
    bzla_bv_free(mm, tmp);
    bzla_bv_free(mm, ones);

    if (cmp_t > 0 && !check)
    {
      return false;
    }

    if (cmp_t < 0 && !check)
    {
      /* x > t:
       * pick s > t such that x = s + t does not overflow -> t < s < ones - t
       * -> 2*t + 1 <= x <= ones */
      bv_res = bzla_proputils_cons_urem_const_pos0_aux(bzla, pi);
      res    = bv_res != NULL;
      if (res)
      {
        bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new_fixed(mm, bv_res));
        bzla_bv_free(mm, bv_res);
      }
    }
  }
  else
  {
    zero  = bzla_bv_zero(mm, bw);
    check = bzla_bvdomain_check_fixed_bits(mm, x, zero);
    if (!check)
    {
      if (t_is_ones)
      {
        res = false;
      }
      else
      {
        tmp = bzla_bv_inc(mm, t);
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, 0);
        res = bzla_bvdomain_gen_has_next(&gen);
        if (res)
        {
          bzla_propinfo_set_result(
              bzla,
              pi,
              bzla_bvdomain_new_fixed(mm, bzla_bvdomain_gen_random(&gen)));
        }
        bzla_bv_free(mm, tmp);
        bzla_bvdomain_gen_delete(&gen);
      }
    }
    bzla_bv_free(mm, zero);
  }
  return res;
}

/**
 * Check consistency condition (with respect to const bits in x) for:
 *
 * x o s = t
 * s o x = t
 *
 * IC:
 * pos_x = 0: mcb(x, t[msb : bw(s)])
 * pos_x = 1: mcb(x, t[msb - bw(s): lsb])
 */
bool
bzla_is_cons_concat_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t pos_x, bw_t, bw_s;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBitVector *tmp;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw_t  = bzla_bv_get_width(t);
  bw_s  = bzla_bv_get_width(pi->bv[1 - pos_x]);

  if (pos_x == 0)
  {
    tmp = bzla_bv_slice(mm, t, bw_t - 1, bw_s);
  }
  else
  {
    tmp = bzla_bv_slice(mm, t, bw_t - 1 - bw_s, 0);
  }
  res = bzla_bvdomain_check_fixed_bits(mm, x, tmp);
  bzla_bv_free(mm, tmp);

  return res;
}
