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

#include "bzlainvutils.h"

#include <assert.h>

#include "bzlacore.h"
#include "bzlaproputils.h"
#include "utils/bzlautil.h"

/* -------------------------------------------------------------------------- */
/* Check invertibility without considering constant bits in x.                */
/* -------------------------------------------------------------------------- */

typedef BzlaBitVector *(*BzlaBitVectorBinFun)(BzlaMemMgr *,
                                              const BzlaBitVector *,
                                              const BzlaBitVector *);

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: true
 */
bool
bzla_is_inv_add(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  (void) pi;
  return true;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x & s = t
 * s & x = t
 *
 * IC: t & s = t
 */
bool
bzla_is_inv_and(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;

  bool res;
  const BzlaBitVector *s, *t;
  BzlaBitVector *t_and_s;
  BzlaMemMgr *mm;

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  mm      = bzla->mm;
  t_and_s = bzla_bv_and(mm, t, s);
  res     = bzla_bv_compare(t_and_s, t) == 0;
  bzla_bv_free(mm, t_and_s);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x o s = t
 * IC: s = t[bw(s) - 1 : 0]
 *
 * pos_x = 1:
 * s o x = t
 * IC: s = t[bw(t) - 1 : bw(t) - bw(s)]
 */
bool
bzla_is_inv_concat(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  (void) pi;

  const BzlaBitVector *s, *t;
  BzlaBitVector *slice;
  bool res;
  uint32_t bw_s, bw_t;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  s    = pi->bv[1 - pi->pos_x];
  t    = pi->target_value;
  bw_s = bzla_bv_get_width(s);
  bw_t = bzla_bv_get_width(t);

  if (pi->pos_x == 0)
  {
    slice = bzla_bv_slice(mm, t, bw_s - 1, 0);
  }
  else
  {
    assert(pi->pos_x == 1);
    slice = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bw_s);
  }
  res = bzla_bv_compare(s, slice) == 0;
  bzla_bv_free(mm, slice);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x == s = t
 * s == x = t
 *
 * IC: true
 */
bool
bzla_is_inv_eq(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  (void) pi;
  return true;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x * s = t
 * s * x = t
 *
 * IC: (-s | s ) & t = t
 */
bool
bzla_is_inv_mul(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  const BzlaBitVector *s, *t;
  BzlaBitVector *neg_s, *neg_s_or_s, *and_t;
  BzlaMemMgr *mm;

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  mm         = bzla->mm;
  neg_s      = bzla_bv_neg(mm, s);
  neg_s_or_s = bzla_bv_or(mm, neg_s, s);
  and_t      = bzla_bv_and(mm, neg_s_or_s, t);
  res        = bzla_bv_compare(and_t, t) == 0;
  bzla_bv_free(mm, neg_s);
  bzla_bv_free(mm, neg_s_or_s);
  bzla_bv_free(mm, and_t);
  return res;
}

typedef enum
{
  BZLA_BV_SHIFT_SLL,
  BZLA_BV_SHIFT_SRL,
  BZLA_BV_SHIFT_SRA,
} BzlaBvShiftKind;

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * SLL:
 *   pos_x = 0:
 *   x << s = t
 *   IC: (t >> s) << s = t
 *
 *   pos_x = 1:
 *   s << x = t
 *   IC: ctz(s) <= ctz(t) /\ ((t = 0) \/ (s << (ctz(t) - ctz(s))) = t)
 *
 * SRL:
 *   pos_x = 0:
 *   x >> s = t
 *   IC: (t << s) >> s = t
 *
 *   pos_x = 1:
 *   s >> x = t
 *   IC: clz(s) <= clz(t) /\ ((t = 0) \/ (s >> (clz(t) - clz(s))) = t)
 *
 * SRA:
 *   pos_x = 0:
 *   x >>a s = t
 *   IC: (s < bw(s) => (t << s) >>a s = t) /\
 *       (s >= bw(s) => (t = ones \/ t = 0))
 *
 *   pos_x = 1:
 *   s >>a x = t
 *   IC: (s[MSB] = 0 => is_inv_srl(s >> x = t)
 *       /\ (s[MSB] = 1 => is_inv_srl(~s >> x = ~t)
 */
static bool
is_inv_shift(Bzla *bzla, BzlaPropInfo *pi, BzlaBvShiftKind kind)
{
  assert(bzla);
  assert(pi);

  bool res;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;
  BzlaBitVector *shift1, *shift2, *bw_bv, *not_s = 0, *not_t = 0;
  int32_t pos_x, cmp;
  uint32_t bw, cnt_t, cnt_s;
  BzlaBitVectorBinFun shift1_fun, shift2_fun;
  uint32_t (*count_fun)(const BzlaBitVector *) = 0;
  BzlaBitVector *(*ishift_fun)(BzlaMemMgr *, const BzlaBitVector *, uint64_t);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(s);

  ishift_fun = 0;

  if (kind == BZLA_BV_SHIFT_SLL)
  {
    count_fun  = bzla_bv_get_num_trailing_zeros;
    shift1_fun = bzla_bv_srl;
    shift2_fun = bzla_bv_sll;
    ishift_fun = bzla_bv_sll_uint64;
  }
  else if (kind == BZLA_BV_SHIFT_SRL)
  {
    count_fun  = bzla_bv_get_num_leading_zeros;
    shift1_fun = bzla_bv_sll;
    shift2_fun = bzla_bv_srl;
    ishift_fun = bzla_bv_srl_uint64;
  }
  else
  {
    assert(kind == BZLA_BV_SHIFT_SRA);
    if (pos_x == 1)
    {
      if (bzla_bv_get_bit(s, bw - 1) == 1)
      {
        not_s = bzla_bv_not(mm, s);
        not_t = bzla_bv_not(mm, t);
        s     = not_s;
        t     = not_t;
      }

      count_fun  = bzla_bv_get_num_leading_zeros;
      shift1_fun = bzla_bv_sll;
      shift2_fun = bzla_bv_srl;
      ishift_fun = bzla_bv_srl_uint64;
      kind       = BZLA_BV_SHIFT_SRL;
    }
    else
    {
      shift1_fun = bzla_bv_sll;
      shift2_fun = bzla_bv_sra;
    }
  }

  if (pos_x == 0)
  {
    shift1 = shift1_fun(mm, t, s);
    shift2 = shift2_fun(mm, shift1, s);
    res    = bzla_bv_compare(shift2, t) == 0;
    bzla_bv_free(mm, shift1);
    bzla_bv_free(mm, shift2);
    bw_bv = bzla_bv_uint64_to_bv(mm, bw, bw);
    cmp   = bzla_bv_compare(s, bw_bv);
    if (cmp >= 0 && kind == BZLA_BV_SHIFT_SRA)
    {
      res = bzla_bv_is_zero(t) || bzla_bv_is_ones(t);
    }
    bzla_bv_free(mm, bw_bv);
  }
  else
  {
    assert(pos_x == 1);
    assert(count_fun);

    cnt_t = count_fun(t);
    cnt_s = count_fun(s);

    if (cnt_s > cnt_t)
    {
      res = false;
    }
    else
    {
      if (bzla_bv_is_zero(t))
      {
        res = true;
      }
      else
      {
        assert(ishift_fun);
        shift1 = ishift_fun(mm, s, cnt_t - cnt_s);
        res    = bzla_bv_compare(shift1, t) == 0;
        bzla_bv_free(mm, shift1);
      }
    }
  }
  if (not_s)
  {
    assert(not_t);
    bzla_bv_free(mm, not_s);
    bzla_bv_free(mm, not_t);
  }
  return res;
}

bool
bzla_is_inv_sll(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return is_inv_shift(bzla, pi, BZLA_BV_SHIFT_SLL);
}

bool
bzla_is_inv_srl(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return is_inv_shift(bzla, pi, BZLA_BV_SHIFT_SRL);
}

bool
bzla_is_inv_sra(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return is_inv_shift(bzla, pi, BZLA_BV_SHIFT_SRA);
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x < s = t (unsigned)
 * IC: t = 0 || s != 0
 *
 * pos_x = 1:
 * s < x = t (unsigned)
 * IC: t = 0 || s != ~0
 */
bool
bzla_is_inv_ult(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;

  const BzlaBitVector *s, *t;

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  bool res;
  if (pi->pos_x == 0)
  {
    res = bzla_bv_is_zero(t) || !bzla_bv_is_zero(s);
  }
  else
  {
    assert(pi->pos_x == 1);
    res = bzla_bv_is_zero(t) || !bzla_bv_is_ones(s);
  }
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x < s = t (signed)
 * IC: t = 0 || s != min_signed_value
 *
 * pos_x = 1:
 * s < x = t (signed)
 * IC: t = 0 || s != max_signed_value
 */
bool
bzla_is_inv_slt(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;

  const BzlaBitVector *s, *t;

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  bool res;
  if (pi->pos_x == 0)
  {
    res = bzla_bv_is_zero(t) || !bzla_bv_is_min_signed(s);
  }
  else
  {
    assert(pi->pos_x == 1);
    res = bzla_bv_is_zero(t) || !bzla_bv_is_max_signed(s);
  }
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x / s = t
 * IC: (s * t) / s = t
 *
 * pos_x = 1:
 * s / x = t
 * IC: s / (s / t) = t
 */
bool
bzla_is_inv_udiv(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  BzlaBitVector *udiv;
  const BzlaBitVector *s, *t;
  BzlaMemMgr *mm;

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  mm = bzla->mm;
  if (pi->pos_x == 0)
  {
    BzlaBitVector *s_mul_t = bzla_bv_mul(mm, s, t);
    udiv                   = bzla_bv_udiv(mm, s_mul_t, s);
    bzla_bv_free(mm, s_mul_t);
  }
  else
  {
    assert(pi->pos_x == 1);
    BzlaBitVector *s_udiv_t = bzla_bv_udiv(mm, s, t);
    udiv                    = bzla_bv_udiv(mm, s, s_udiv_t);
    bzla_bv_free(mm, s_udiv_t);
  }
  res = bzla_bv_compare(udiv, t) == 0;
  bzla_bv_free(mm, udiv);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x % s = t
 * IC: ~(-s) >= t
 *
 * pos_x = 1:
 * s % x = t
 * IC: (t + t - s) & s >= t
 */
bool
bzla_is_inv_urem(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  const BzlaBitVector *s, *t;
  BzlaBitVector *neg_s;
  BzlaMemMgr *mm;

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  mm    = bzla->mm;
  neg_s = bzla_bv_neg(mm, s);

  if (pi->pos_x == 0)
  {
    BzlaBitVector *not_neg_s = bzla_bv_not(mm, neg_s);
    res                      = bzla_bv_compare(t, not_neg_s) <= 0;
    bzla_bv_free(mm, not_neg_s);
  }
  else
  {
    assert(pi->pos_x == 1);
    BzlaBitVector *t_add_t = bzla_bv_add(mm, t, t);
    BzlaBitVector *sub_s   = bzla_bv_add(mm, t_add_t, neg_s);
    BzlaBitVector *and_s   = bzla_bv_and(mm, sub_s, s);
    res                    = bzla_bv_compare(t, and_s) <= 0;
    bzla_bv_free(mm, t_add_t);
    bzla_bv_free(mm, sub_s);
    bzla_bv_free(mm, and_s);
  }
  bzla_bv_free(mm, neg_s);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * c ? x : s = t
 * c ? s : x = t
 *
 * IC pos_x = 0:
 * s0 == t || s1 == t
 *
 * IC pos_x = 1:
 * s0 == true
 *
 * IC pos_x = 2:
 * s0 == false
 */
bool
bzla_is_inv_cond(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  const BzlaBitVector *t;

  t     = pi->target_value;
  pos_x = pi->pos_x;
  bzla_propinfo_set_result(bzla, pi, 0);

  if (pos_x == 0)
  {
    return bzla_bv_compare(pi->bv[1], t) == 0
           || bzla_bv_compare(pi->bv[2], t) == 0;
  }
  else if (pos_x == 1)
  {
    return bzla_bv_is_true(pi->bv[0]) || bzla_bv_compare(pi->bv[2], t) == 0;
  }
  return bzla_bv_is_false(pi->bv[0]) || bzla_bv_compare(pi->bv[1], t) == 0;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x[upper:lower] = t
 *
 * IC: true
 */
bool
bzla_is_inv_slice(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  (void) pi;
  return true;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * sign_extend(x, n) = t
 *
 * IC: (t_ext == ones) \/ (t_ext == zero)
 *     with t_x  = t[t_size - 1 - n : 0]
 *     and t_ext = t[bw_t - 1, bw_t - 1 - n] (includes MSB of t_x)
 */
bool
bzla_is_inv_sext(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res = false;
  BzlaMemMgr *mm;
  uint32_t n, bw;
  const BzlaBitVector *t;
  BzlaBitVector *t_ext, *t_x;

  /* Note: pi->exp is a concat representing a sign_extend. pi->bv store the
   * assignments to the concat's operands. */

  mm = bzla->mm;
  n  = bzla_bv_get_width(pi->bv[0]);
  t  = pi->target_value;

  bw    = bzla_bv_get_width(t);
  t_ext = bzla_bv_slice(mm, t, bw - 1, bw - n - 1);
  t_x   = bzla_bv_slice(mm, t, bw - 1 - n, 0);

  if (bzla_bv_is_zero(t_ext) || bzla_bv_is_ones(t_ext))
  {
    res = true;
    bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, t_x, t_x));
  }
  bzla_bv_free(mm, t_ext);
  bzla_bv_free(mm, t_x);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x ^ s = t
 * s ^ x = t
 *
 * IC: true
 */
bool
bzla_is_inv_xor(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  (void) pi;
  return true;
}

/* -------------------------------------------------------------------------- */
/* Check invertibility while considering constant bits in x.                  */
/* -------------------------------------------------------------------------- */

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: (((t - s) & hi_x) | lo_x) = t - s
 */
bool
bzla_is_inv_add_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  const BzlaBitVector *s, *t;
  BzlaBitVector *sub;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  bzla_propinfo_set_result(bzla, pi, 0);
  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  sub = bzla_bv_sub(mm, t, s);
  res = bzla_bvdomain_check_fixed_bits(mm, pi->bvd[pi->pos_x], sub);
  bzla_bv_free(mm, sub);
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x & s = t
 * s & x = t
 *
 * m = ~(lo_x ^ hi_x)  ... mask out all non-constant bits
 * IC: (s & t) = t && (s & hi_x) & m = t & m
 *
 * Intuition:
 * 1) x & s = t on all const bits of x
 * 2) s & t = t on all non-const bits of x
 */
bool
bzla_is_inv_and_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  const BzlaBitVector *s, *t;
  int32_t pos_x;
  BzlaBitVector *and1, *and2, *and3, *mask;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  if (!bzla_is_inv_and(bzla, pi)) return false;

  mask = bzla_bv_xnor(mm, x->lo, x->hi);
  and1 = bzla_bv_and(mm, s, x->hi);
  and2 = bzla_bv_and(mm, and1, mask);
  and3 = bzla_bv_and(mm, t, mask);
  res  = bzla_bv_compare(and2, and3) == 0;
  bzla_bv_free(mm, and1);
  bzla_bv_free(mm, and2);
  bzla_bv_free(mm, and3);
  bzla_bv_free(mm, mask);
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x o s = tx o ts
 * IC: mcb(x, tx) /\ s = ts
 *
 * s o x = ts o tx
 * IC: mcb(x, tx) /\ s = ts
 */
bool
bzla_is_inv_concat_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  int32_t pos_x;
  uint32_t bw_t, bw_s, bw_x;
  BzlaBitVector *t_x;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  if (!bzla_is_inv_concat(bzla, pi)) return false;

  mm = bzla->mm;
  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);
  bw_x = bzla_bvdomain_get_width(x);

  if (pos_x == 0)
  {
    t_x = bzla_bv_slice(mm, t, bw_t - 1, bw_s);
  }
  else
  {
    t_x = bzla_bv_slice(mm, t, bw_x - 1, 0);
  }

  res = bzla_bvdomain_check_fixed_bits(mm, x, t_x);
  bzla_bv_free(mm, t_x);
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x == s = t
 * s == x = t
 *
 * IC:
 * t = 0: (hi_x != lo_x) || (hi_x != s)
 * t = 1: ((s & hi_x) | lo_x) = s
 */
bool
bzla_is_inv_eq_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  int32_t pos_x;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *x;

  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  if (bzla_bv_is_false(t))
  {
    return bzla_bv_compare(x->hi, x->lo) || bzla_bv_compare(x->hi, s);
  }

  return bzla_bvdomain_check_fixed_bits(bzla->mm, x, s);
}

bool
bzla_is_inv_mul_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res = true, lsb_s;
  BzlaBitVector *mod_inv_s, *x;
  BzlaMemMgr *mm;
  int32_t pos_x;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *d_x;

  mm = bzla->mm;
  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  d_x   = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  res   = bzla_is_inv_mul(bzla, pi);

  if (res && !bzla_bv_is_zero(s) && bzla_bvdomain_has_fixed_bits(mm, d_x))
  {
    /* d_x is constant */
    if (bzla_bvdomain_is_fixed(mm, d_x))
    {
      x   = bzla_bv_mul(mm, d_x->lo, s);
      res = bzla_bv_compare(x, t) == 0;
      bzla_bv_free(mm, x);
    }
    else
    {
      lsb_s = bzla_bv_get_bit(s, 0) == 1;

      /* s odd */
      if (lsb_s)
      {
        mod_inv_s = bzla_bv_mod_inverse(mm, s);
        x         = bzla_bv_mul(mm, mod_inv_s, t);
        res       = bzla_bvdomain_check_fixed_bits(mm, d_x, x);
        if (res)
        {
          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, x, x));
        }
        bzla_bv_free(mm, x);
        bzla_bv_free(mm, mod_inv_s);
      }
      /* s even */
      else
      {
        /* Check if relevant bits of
         *   x' = (t >> ctz(s)) * (s >> ctz(s))^-1
         * match corresponding constant bits of d_x, i.e.
         * mcb(d_x[bw - ctz(s) - 1:0], x'[bw - ctz(s) - 1:0]). */

        BzlaBitVector *tmp_s, *tmp_t, *tmp_x, *x_lo_sliced, *x_hi_sliced;
        BzlaBitVector *lo, *hi, *mask_x;
        BzlaBvDomain *d_tmp_x_sliced;
        uint32_t bw   = bzla_bv_get_width(s);
        uint32_t tz_s = bzla_bv_get_num_trailing_zeros(s);
        assert(tz_s <= bzla_bv_get_num_trailing_zeros(t));

        tmp_s = bzla_bv_srl_uint64(mm, s, tz_s);
        tmp_t = bzla_bv_srl_uint64(mm, t, tz_s);

        assert(bzla_bv_get_bit(tmp_s, 0) == 1);

        mod_inv_s = bzla_bv_mod_inverse(mm, tmp_s);
        bzla_bv_free(mm, tmp_s);

        tmp_x = bzla_bv_mul(mm, mod_inv_s, tmp_t);
        bzla_bv_free(mm, tmp_t);
        bzla_bv_free(mm, mod_inv_s);

        /* Check if relevant bits of tmp_x match corresponding constant bits of
         * d_x, i.e. mcb(d_x[bw - ctz(s) - 1:0], tmp_x[bw - ctz(s) - 1:0]). */
        d_tmp_x_sliced = bzla_bvdomain_slice(mm, d_x, bw - tz_s - 1, 0);
        mask_x         = bzla_bv_slice(mm, tmp_x, bw - tz_s - 1, 0);
        res = bzla_bvdomain_check_fixed_bits(mm, d_tmp_x_sliced, mask_x);

        if (res)
        {
          /* Result domain is d_x[bw - 1:ctz(s)] o tmp_x[bw - ctz(s) - 1:0] */
          x_lo_sliced = bzla_bv_slice(mm, d_x->lo, bw - 1, bw - tz_s);
          x_hi_sliced = bzla_bv_slice(mm, d_x->hi, bw - 1, bw - tz_s);
          lo          = bzla_bv_concat(mm, x_lo_sliced, mask_x);
          hi          = bzla_bv_concat(mm, x_hi_sliced, mask_x);

          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, lo, hi));
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, hi);
          bzla_bv_free(mm, x_lo_sliced);
          bzla_bv_free(mm, x_hi_sliced);
        }

        bzla_bvdomain_free(mm, d_tmp_x_sliced);
        bzla_bv_free(mm, mask_x);
        bzla_bv_free(mm, tmp_x);
      }
    }
  }
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * SLL:
 *   pos_x = 0:
 *   x << s = t
 *   IC: (t >> s) << s = t /\ mcb(x << s, t)
 *
 *   pos_x = 1:
 *   s << x = t
 *   IC: is_inv_sll /\
 *       ((t = 0) => (hi_x >= ctz(t) - ctz(s) \/ (s = 0)))
 *        /\ ((t != 0) => mcb(x, ctz(t) - ctz(s)))
 *
 * SRL:
 *   pos_x = 0:
 *   x >> s = t
 *   IC: (t << s) >> s = t /\ mcb(x >> s, t)
 *
 *   pos_x = 1:
 *   s >> x = t
 *   IC: is_inv_srl /\
 *       ((t = 0) => (hi_x >= clz(t) - clz(s) \/ (s = 0)))
 *        /\ ((t != 0) => mcb(x, clz(t) - clz(s)))
 *
 * SRA:
 *   pos_x = 0:
 *   x >>a s = t
 *   IC: is_inv_sra /\ mcb(x >>a s, t)
 *
 *   pos_x = 1:
 *   s >>a x = t
 *   IC: is_inv_sra /\
 *       (s[MSB] = 0 => is_inv_srl) /\ (s[MSB] = 1 => is_inv_srl(~s >> x = ~t))
 */
static bool
is_inv_shift_const(Bzla *bzla, BzlaPropInfo *pi, BzlaBvShiftKind kind)
{
  assert(bzla);
  assert(pi);

  uint32_t pos_x, bw, cnt_s, cnt_t;
  bool res;
  BzlaBitVector *shift_hi, *shift_lo, *and, * or ;
  BzlaBitVector *bv, *min, *not_s = 0, *not_t = 0;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;
  BzlaBitVectorBinFun bv_fun                   = 0;
  uint32_t (*count_fun)(const BzlaBitVector *) = 0;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;

  pos_x = pi->pos_x;
  mm    = bzla->mm;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(s);

  if (kind == BZLA_BV_SHIFT_SLL)
  {
    bv_fun    = bzla_bv_sll;
    count_fun = bzla_bv_get_num_trailing_zeros;
    res       = bzla_is_inv_sll(bzla, pi);
  }
  else if (kind == BZLA_BV_SHIFT_SRL)
  {
    bv_fun    = bzla_bv_srl;
    count_fun = bzla_bv_get_num_leading_zeros;
    res       = bzla_is_inv_srl(bzla, pi);
  }
  else
  {
    assert(kind == BZLA_BV_SHIFT_SRA);
    res = bzla_is_inv_sra(bzla, pi);

    /* For pox_x = 1 we can use SRL to check invertibility of SRA. */
    if (pos_x == 1)
    {
      if (res && bzla_bv_get_bit(s, bw - 1) == 1)
      {
        not_s = bzla_bv_not(mm, s);
        not_t = bzla_bv_not(mm, t);
        s     = not_s;
        t     = not_t;
      }

      bv_fun    = bzla_bv_srl;
      count_fun = bzla_bv_get_num_leading_zeros;
    }
    else
    {
      bv_fun = bzla_bv_sra;
    }
  }

  if (!res) return false;

  bzla_propinfo_set_result(bzla, pi, 0);

  /* x <> s = t: mcb(x <> s, t) for <> in {<<, >>, >>a} */
  if (pos_x == 0)
  {
    assert(bv_fun);
    shift_hi = bv_fun(mm, x->hi, s);
    shift_lo = bv_fun(mm, x->lo, s);
    and      = bzla_bv_and(mm, shift_hi, t);
    or       = bzla_bv_or(mm, shift_lo, t);
    res      = bzla_bv_compare(and, t) == 0 && bzla_bv_compare(or, t) == 0;
    bzla_bv_free(mm, or);
    bzla_bv_free(mm, and);
    bzla_bv_free(mm, shift_lo);
    bzla_bv_free(mm, shift_hi);
  }
  else
  {
    assert(pos_x == 1);
    if (bzla_bvdomain_is_fixed(mm, x))
    {
      shift_lo = bv_fun(mm, s, x->lo);
      res      = bzla_bv_compare(shift_lo, t) == 0;
      if (res)
      {
        bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, x->lo, x->lo));
      }
      bzla_bv_free(mm, shift_lo);
    }
    else
    {
      assert(count_fun);
      cnt_s = count_fun(s);
      cnt_t = count_fun(t);
      assert(cnt_s <= cnt_t);

      /* Minimum number of bits required to shift left (right) s to match
       * trailing (leading) zeroes/ones of t. */
      min = bzla_bv_uint64_to_bv(mm, cnt_t - cnt_s, bzla_bv_get_width(s));
      if (bzla_bv_is_zero(t))
      {
        res = bzla_bv_compare(x->hi, min) >= 0 || bzla_bv_is_zero(s);
        if (res)
        {
          /* If s is zero, any value of x is an inverse. */
          bzla_bvdomain_gen_init_range(
              mm, bzla->rng, &gen, x, bzla_bv_is_zero(s) ? 0 : min, 0);
          assert(bzla_bvdomain_gen_has_next(&gen));
          bv = bzla_bvdomain_gen_random(&gen);
          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, bv, bv));
          bzla_bvdomain_gen_delete(&gen);
        }
      }
      else
      {
        res = bzla_bvdomain_check_fixed_bits(mm, x, min);
#ifndef NDEBUG
        if (res)
        {
          bv = bv_fun(mm, s, min);
          assert(bzla_bv_compare(bv, t) == 0);
          bzla_bv_free(mm, bv);
        }
#endif
        if (res)
        {
          bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, min, min));
        }
      }
      bzla_bv_free(mm, min);
    }
  }
  if (not_s)
  {
    assert(not_t);
    bzla_bv_free(mm, not_s);
    bzla_bv_free(mm, not_t);
  }
  assert(pos_x != 0 || pi->res_x == 0);
  return res;
}

bool
bzla_is_inv_sll_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return is_inv_shift_const(bzla, pi, BZLA_BV_SHIFT_SLL);
}

bool
bzla_is_inv_srl_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return is_inv_shift_const(bzla, pi, BZLA_BV_SHIFT_SRL);
}

bool
bzla_is_inv_sra_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return is_inv_shift_const(bzla, pi, BZLA_BV_SHIFT_SRA);
}

bool
bzla_is_inv_udiv_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res = true;
  BzlaBitVector *tmp, *min, *max, *inc;
  BzlaMemMgr *mm;
  int32_t pos_x;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *x;

  mm  = bzla->mm;
  res = bzla_is_inv_udiv(bzla, pi);
  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  if (res && bzla_bvdomain_has_fixed_bits(mm, x))
  {
    /* x is constant */
    if (bzla_bvdomain_is_fixed(mm, x))
    {
      if (pos_x == 0)
      {
        tmp = bzla_bv_udiv(mm, x->lo, s);
      }
      else
      {
        tmp = bzla_bv_udiv(mm, s, x->lo);
      }
      res = bzla_bv_compare(tmp, t) == 0;
      bzla_bv_free(mm, tmp);
    }
    else
    {
      if (pos_x == 0)
      {
        if (bzla_bv_is_zero(t))
        {
          res = bzla_bv_compare(x->lo, s) < 0;
        }
        /* If s == 0, we can always find an inverse value for x. */
        else if (!bzla_bv_is_zero(s))
        {
          min = bzla_bv_mul(mm, s, t);
          max = bzla_bv_add(mm, min, s);
          if (bzla_bv_compare(max, min) < 0)
          {
            bzla_bv_free(mm, max);
            max = bzla_bv_ones(mm, bzla_bv_get_width(x->lo));
          }
          else
          {
            tmp = bzla_bv_dec(mm, max);
            bzla_bv_free(mm, max);
            max = tmp;
          }

          BzlaBvDomainGenerator dgen;
          bzla_bvdomain_gen_init_range(mm, bzla->rng, &dgen, x, min, max);
          res = bzla_bvdomain_gen_has_next(&dgen);
          if (res)
          {
            pi->res_x =
                bzla_bvdomain_new(mm, bzla_bvdomain_gen_random(&dgen), max);
          }
          bzla_bvdomain_gen_delete(&dgen);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
      }
      else
      {
        assert(pos_x == 1);
        uint32_t bw = bzla_bv_get_width(s);

        if (!bzla_bv_is_zero(s) || !bzla_bv_is_zero(t))
        {
          tmp = bzla_bv_udiv(mm, s, x->hi);

          if (bzla_bv_compare(tmp, t) > 0)
          {
            res = false;
          }
          bzla_bv_free(mm, tmp);

          if (res)
          {
            if (bzla_bv_is_ones(t))
            {
              min = bzla_bv_zero(mm, bw);
              max = bzla_bv_is_ones(s) ? bzla_bv_one(mm, bw)
                                       : bzla_bv_copy(mm, min);
            }
            else if (bzla_bv_compare(s, t) == 0)
            {
              min = bzla_bv_one(mm, bzla_bv_get_width(s));
              max = bzla_bv_copy(mm, min);
            }
            else
            {
              inc = bzla_bv_inc(mm, t);
              tmp = bzla_bv_udiv(mm, s, inc);
              bzla_bv_free(mm, inc);
              min = bzla_bv_inc(mm, tmp);
              bzla_bv_free(mm, tmp);

              max = bzla_bv_udiv(mm, s, t);
            }

            BzlaBvDomainGenerator dgen;
            bzla_bvdomain_gen_init_range(mm, bzla->rng, &dgen, x, min, max);
            res = bzla_bvdomain_gen_has_next(&dgen);
            if (res)
            {
              pi->res_x =
                  bzla_bvdomain_new(mm, bzla_bvdomain_gen_random(&dgen), max);
            }
            bzla_bvdomain_gen_delete(&dgen);
            bzla_bv_free(mm, min);
            bzla_bv_free(mm, max);
          }
        }
      }
    }
  }

  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x < s = t (unsigned)
 * s < x = t (unsigned)
 *
 * IC pos_x = 0:
 * t = 1: t -> (s != 0 && lo_x < s)
 * t = 0: ~t -> (hi_x >= s)
 *
 *
 * IC pos_x = 1:
 * t = 1: t -> (s != ~0 && hi_x > s)
 * t = 0: ~t -> (lo_x <= s)
 */
bool
bzla_is_inv_ult_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *x;

  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  if (pos_x == 0)
  {
    /* x < s */
    if (bzla_bv_is_true(t))
    {
      return !bzla_bv_is_zero(s) && bzla_bv_compare(x->lo, s) == -1;
    }
    /* x >= s */
    return bzla_bv_compare(x->hi, s) >= 0;
  }
  assert(pos_x == 1);

  /* s < x */
  if (bzla_bv_is_true(t))
  {
    return !bzla_bv_is_ones(s) && bzla_bv_compare(x->hi, s) == 1;
  }
  /* s >= x */
  return bzla_bv_compare(x->lo, s) <= 0;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x < s = t (signed)
 * s < x = t (signed)
 *
 * IC pos_x = 0:
 * t = 1:
 * t -> s != min_signed_value
 *       && ((MSB(x) = 0 && lo_x < s)
 *           || (MSB(x) != 0 && 1 o lo_x[bw-2:0] < s))
 * t = 0:
 * ~t -> (MSB(x) = 1 && hi_x >= s)
 *        || (MSB(x) != 1 && 0 o hi_x[bw-2:0] >= s))
 *
 *
 * IC pos_x = 1:
 * t = 1:
 * t -> s != max_signed_value
 *       && ((MSB(x) = 1 && s < hi_x)
 *           || (MSB(x) != 1 && s < 0 o hi_x[bw-2:0]))
 * t = 0:
 * ~t -> (MSB(x) = 0 && s >= lo_x)
 *        || (MSB(x) != 0 && s >= 1 o lo_x[bw-2:0]))
 */
bool
bzla_is_inv_slt_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  int32_t pos_x;
  uint32_t bw;
  bool msb_false, msb_true;
  BzlaBitVector *tmp;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw    = bzla_bvdomain_get_width(x);
  mm    = bzla->mm;

  msb_false = bzla_bvdomain_is_fixed_bit_false(x, bw - 1);
  msb_true  = bzla_bvdomain_is_fixed_bit_true(x, bw - 1);
  if (pos_x == 0)
  {
    /* x < s */
    if (bzla_bv_is_true(t))
    {
      if (bzla_bv_is_min_signed(s)) return false;
      if (msb_false) return bzla_bv_signed_compare(x->lo, s) == -1;
      tmp = bzla_bv_copy(mm, x->lo);
      bzla_bv_set_bit(tmp, bw - 1, 1);
      res = !msb_false && bzla_bv_signed_compare(tmp, s) == -1;
      bzla_bv_free(mm, tmp);
      return res;
    }
    /* x >= s */
    if (msb_true)
    {
      return bzla_bv_signed_compare(x->hi, s) >= 0;
    }
    tmp = bzla_bv_copy(mm, x->hi);
    bzla_bv_set_bit(tmp, bw - 1, 0);
    res = !msb_true && bzla_bv_signed_compare(tmp, s) >= 0;
    bzla_bv_free(mm, tmp);
    return res;
  }
  assert(pos_x == 1);

  /* s < x */
  if (bzla_bv_is_true(t))
  {
    if (bzla_bv_is_max_signed(s)) return false;
    if (msb_true)
    {
      return bzla_bv_signed_compare(s, x->hi) == -1;
    }
    tmp = bzla_bv_copy(mm, x->hi);
    bzla_bv_set_bit(tmp, bw - 1, 0);
    res = !msb_true && bzla_bv_signed_compare(s, tmp) == -1;
    bzla_bv_free(mm, tmp);
    return res;
  }
  /* s >= x */
  if (msb_false)
  {
    return bzla_bv_signed_compare(s, x->lo) >= 0;
  }
  tmp = bzla_bv_copy(mm, x->lo);
  bzla_bv_set_bit(tmp, bw - 1, 1);
  res = !msb_false && bzla_bv_signed_compare(s, tmp) >= 0;
  bzla_bv_free(mm, tmp);
  return res;
}

bool
bzla_is_inv_urem_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  BzlaBitVector *rem;
  BzlaMemMgr *mm;
  int32_t pos_x;
  const BzlaBitVector *s, *t;
  const BzlaBvDomain *x;

  mm  = bzla->mm;
  res = bzla_is_inv_urem(bzla, pi);
  bzla_propinfo_set_result(bzla, pi, 0);
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  if (res && bzla_bvdomain_has_fixed_bits(mm, x))
  {
    if (bzla_bvdomain_is_fixed(mm, x))
    {
      rem = pos_x ? bzla_bv_urem(mm, s, x->lo) : bzla_bv_urem(mm, x->lo, s);
      res = bzla_bv_compare(rem, t) == 0;
      bzla_bv_free(mm, rem);
    }
    else
    {
      uint32_t bw;
      BzlaBitVector *n, *n_hi, *ones, *hi, *sub, *mul, *bv, *one;

      bw   = bzla_bv_get_width(t);
      ones = bzla_bv_ones(mm, bw);
      if (pos_x)
      {
        if (bzla_bv_compare(s, t) == 0)
        {
          /* s = t: x = 0 or random x > t */
          res = bzla_bv_is_zero(x->lo) || bzla_bv_compare(x->hi, t) > 0;
        }
        else
        {
          /* s % x = t
           *
           * s = x * n + t
           *
           * In general, x = s - t is always a solution with n = 1, but
           * fixed bits of x may not match s - t. In this case, we look for a
           * factor n s.t. x = (s - t) / n, where fixed bits match. */

          assert(bzla_bv_compare(t, s) <= 0);

          n = bzla_bv_sub(mm, s, t);

          /* Is (s - t) a solution?
           *
           * -> if yes we do not store it in d_res_x to enforce that
           *    inv_urem() selects one of several possible choices rather
           *    than only this solution
           */
          res = bzla_bvdomain_check_fixed_bits(mm, x, n);
          if (!res)
          {
            bv  = 0;
            one = bzla_bv_one(mm, bw);
            if (bzla_bv_is_zero(t)
                && bzla_bvdomain_check_fixed_bits(mm, x, one))
            {
              /* we don't store it in d_res_x for the same reason as above */
              res = true;
            }
            else
            {
              /* s - t does not match const bits of x and one is not a
               * possible solution. Find factor n of (s - t) s.t. n > t and n
               * matches the const bits of x. Pick x = n.  */
              bv = bzla_bvdomain_get_factor(mm, n, x, t, 10000, bzla->rng);
              assert(!bv || bzla_bvdomain_check_fixed_bits(mm, x, bv));
              res = bv != 0;
              if (res)
              {
                bzla_propinfo_set_result(
                    bzla, pi, bzla_bvdomain_new(mm, bv, bv));
#ifndef NDEBUG
                BzlaBitVector *tmp = bzla_bv_urem(mm, s, bv);
                assert(bzla_bv_compare(tmp, t) == 0);
                bzla_bv_free(mm, tmp);
#endif
                bzla_bv_free(mm, bv);
              }
            }
            bzla_bv_free(mm, one);
          }
          bzla_bv_free(mm, n);
        }
      }
      else
      {
        if (bzla_bv_is_zero(s) || bzla_bv_is_ones(t))
        {
          /* x % 0 = t: x = t
           * t = ones : s = 0, x = ones */
          res = bzla_bvdomain_check_fixed_bits(mm, x, t);
        }
        else
        {
          assert(bzla_bv_compare(s, t) > 0);
          if (!bzla_bvdomain_check_fixed_bits(mm, x, t))
          {
            /* simplest solution (0 <= res < s: res = t) does not apply, thus
             * x = s * n + t with n s.t. (s * n + t) does not overflow */

            sub = bzla_bv_sub(mm, ones, s);
            if (bzla_bv_compare(sub, t) < 0)
            {
              /* overflow for n = 1 -> only simplest solution possible, but
               * simplest possible solution not applicable */
              res = false;
            }
            else
            {
              bzla_bv_free(mm, sub);
              /**
               * x = s * n + t, with n s.t. (s * n + t) does not overflow
               * -> n <= (~0 - t) / s (truncated)
               * -> ~0 - s * n >= t
               */
              sub = bzla_bv_sub(mm, ones, t);
              /* n_hi = (~0 - t) / s */
              n_hi = bzla_bv_udiv(mm, sub, s);
              assert(!bzla_bv_is_zero(n_hi));
              bzla_bv_free(mm, sub);
              /* ~0 - s * n_hi < t ? decrease n_hi until */
              mul = bzla_bv_mul(mm, s, n_hi);
              sub = bzla_bv_sub(mm, ones, mul);
              while (bzla_bv_compare(sub, t) < 0)
              {
                bv   = n_hi;
                n_hi = bzla_bv_dec(mm, n_hi);
                bzla_bv_free(mm, bv);
                bzla_bv_free(mm, mul);
                mul = bzla_bv_mul(mm, s, n_hi);
                bzla_bv_free(mm, sub);
                sub = bzla_bv_sub(mm, ones, mul);
              }

              /* hi = s * n_hi + t (upper bound for x) */
              hi = bzla_bv_add(mm, mul, t);
              bzla_bv_free(mm, mul);
              BzlaBvDomainGenerator gen;
              /* x->lo <= x <= hi */
              bzla_bvdomain_gen_init_range(
                  mm, 0, &gen, (BzlaBvDomain *) x, 0, hi);
              res = false;
              while (bzla_bvdomain_gen_has_next(&gen))
              {
                bv = bzla_bvdomain_gen_next(&gen);
                assert(bzla_bvdomain_check_fixed_bits(mm, x, bv));
                rem = bzla_bv_urem(mm, bv, s);
                if (bzla_bv_compare(rem, t) == 0)
                {
                  res = true;
                  bzla_bv_free(mm, rem);
                  bzla_propinfo_set_result(
                      bzla, pi, bzla_bvdomain_new(mm, bv, hi));
                  break;
                }
                bzla_bv_free(mm, rem);
              }
              bzla_bvdomain_gen_delete(&gen);
              bzla_bv_free(mm, hi);
              bzla_bv_free(mm, n_hi);
            }
            bzla_bv_free(mm, sub);
          }
        }
      }
      bzla_bv_free(mm, ones);
    }
  }
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * c ? x : s = t
 * c ? s : x = t
 *
 * IC pos_x = 0:
 * (!is_fixed(x) && (s0 = t || s1 = t))
 * || (is_fixed_true(x) && s0 = t)
 * || (is_fixed_false(x) && s1 = t)
 * (s0 the value for e[1] and s1 the value for e[2])
 *
 * IC pos_x = 1:
 * s0 = true && check_fixed_bits(t, x)
 *
 * IC pos_x = 2:
 * s0 == false && check_fixed_bits(t, x)
 *
 * with
 * check_fixed_bits(x,s) := ((s & hi_x) | lo_x) = s
 */
bool
bzla_is_inv_cond_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool cmp0, cmp1;
  BzlaMemMgr *mm;
  int32_t pos_x;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;

  mm = bzla->mm;
  bzla_propinfo_set_result(bzla, pi, 0);
  t     = pi->target_value;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];

  if (pos_x == 1)
  {
    if (bzla_bv_is_true(pi->bv[0])
        && bzla_bvdomain_check_fixed_bits(bzla->mm, x, t))
    {
      bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, t, t));
      return true;
    }
    if (bzla_bv_is_false(pi->bv[0]) && bzla_bv_compare(pi->bv[2], t) == 0)
    {
      return true;
    }
  }
  else if (pos_x == 2)
  {
    if (bzla_bv_is_false(pi->bv[0])
        && bzla_bvdomain_check_fixed_bits(bzla->mm, x, t))
    {
      bzla_propinfo_set_result(bzla, pi, bzla_bvdomain_new(mm, t, t));
      return true;
    }
    if (bzla_bv_is_true(pi->bv[0]) && bzla_bv_compare(pi->bv[1], t) == 0)
    {
      return true;
    }
  }
  else
  {
    /* s0: value for e[1] */
    /* s1: value for e[2] */
    bool res = false;
    assert(bzla_bvdomain_get_width(x) == 1);
    cmp0 = bzla_bv_compare(pi->bv[1], t) == 0;
    cmp1 = bzla_bv_compare(pi->bv[2], t) == 0;
    if (bzla_bvdomain_is_fixed_bit_true(x, 0))
    {
      res = cmp0;
    }
    else if (bzla_bvdomain_is_fixed_bit_false(x, 0))
    {
      res = cmp1;
    }
    else
    {
      res = cmp0 || cmp1;
    }
    if (res)
    {
      uint64_t val;
      if (cmp0 && cmp1)
      {
        val = bzla_rng_flip_coin(bzla->rng);
      }
      else
      {
        val = cmp0 ? 1 : 0;
      }
      bzla_propinfo_set_result(
          bzla, pi, bzla_bvdomain_new_fixed_uint64(mm, val, 1));
    }
    return res;
  }
  return false;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x[upper:lower] = t
 *
 * IC: mcb(x[upper:lower], t)
 */
bool
bzla_is_inv_slice_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  BzlaBvDomain *x_sliced;
  BzlaMemMgr *mm;
  const BzlaBvDomain *x;
  uint32_t upper, lower;
  const BzlaBitVector *t;

  x     = pi->bvd[0];
  t     = pi->target_value;
  upper = bzla_node_bv_slice_get_upper(pi->exp);
  lower = bzla_node_bv_slice_get_lower(pi->exp);

  mm       = bzla->mm;
  x_sliced = bzla_bvdomain_slice(mm, x, upper, lower);
  res      = bzla_bvdomain_check_fixed_bits(mm, x_sliced, t);
  bzla_bvdomain_free(mm, x_sliced);

  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * sign_extend(x, n) = t_ext o t_x
 *
 * IC: ((t_ext == ones) \/ (t_ext == zero)) /\ check_fixed_bits(x, t_x)
 */
bool
bzla_is_inv_sext_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  if (!bzla_is_inv_sext(bzla, pi)) return false;
  return bzla_bvdomain_check_fixed_bits(
      bzla->mm, pi->bvd[pi->pos_x], pi->res_x->lo);
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x ^ s = t
 * s ^ x = t
 *
 * IC: check_fixed_bits(x, s ^ t)
 */
bool
bzla_is_inv_xor_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t pos_x;
  BzlaBitVector * xor ;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  pos_x = pi->pos_x;

  xor = bzla_bv_xor(mm, pi->bv[1 - pos_x], pi->target_value);
  res = bzla_bvdomain_check_fixed_bits(mm, pi->bvd[pos_x], xor);
  bzla_bv_free(mm, xor);

  return res;
}
