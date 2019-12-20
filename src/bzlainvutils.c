/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 *
 *  Bit-vector operator invertibility checks based on [1].
 *
 *  [1] Aina Niemetz, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare
 *      Tinelli: Solving Quantified Bit-Vectors Using Invertibility Conditions.
 *      CAV (2) 2018: 236-255
 *
 */

#include "bzlainvutils.h"

#include <assert.h>

/* -------------------------------------------------------------------------- */
/* Check invertibility without considering constant bits in x.                */
/* -------------------------------------------------------------------------- */

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: true
 */
bool
bzla_is_inv_add(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) mm;
  (void) x;
  (void) t;
  (void) s;
  (void) pos_x;
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
bzla_is_inv_and(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;
  (void) pos_x;

  BzlaBitVector *t_and_s = bzla_bv_and(mm, t, s);
  bool res               = bzla_bv_compare(t_and_s, t) == 0;
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
bzla_is_inv_concat(BzlaMemMgr *mm,
                   const BzlaBvDomain *x,
                   const BzlaBitVector *t,
                   const BzlaBitVector *s,
                   uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;

  BzlaBitVector *slice;
  bool res;
  uint32_t bw_s, bw_t;

  bw_s = bzla_bv_get_width(s);
  bw_t = bzla_bv_get_width(t);
  if (pos_x == 0)
  {
    slice = bzla_bv_slice(mm, t, bw_s - 1, 0);
  }
  else
  {
    assert(pos_x == 1);
    slice = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bw_s);
  }
  BzlaBitVector *s_eq_slice = bzla_bv_eq(mm, s, slice);
  res                       = bzla_bv_is_true(s_eq_slice);
  bzla_bv_free(mm, slice);
  bzla_bv_free(mm, s_eq_slice);
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
bzla_is_inv_eq(BzlaMemMgr *mm,
               const BzlaBvDomain *x,
               const BzlaBitVector *t,
               const BzlaBitVector *s,
               uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) mm;
  (void) x;
  (void) t;
  (void) s;
  (void) pos_x;
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
bzla_is_inv_mul(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;
  (void) pos_x;

  BzlaBitVector *neg_s      = bzla_bv_neg(mm, s);
  BzlaBitVector *neg_s_or_s = bzla_bv_or(mm, neg_s, s);
  BzlaBitVector *and_t      = bzla_bv_and(mm, neg_s_or_s, t);
  BzlaBitVector *eq_t       = bzla_bv_eq(mm, and_t, t);
  bool res                  = bzla_bv_is_true(eq_t);
  bzla_bv_free(mm, neg_s);
  bzla_bv_free(mm, neg_s_or_s);
  bzla_bv_free(mm, and_t);
  bzla_bv_free(mm, eq_t);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x << s = t
 * IC: (t >> s) << s = t
 *
 * pos_x = 1:
 * s << x = t
 * IC: (\/ s << i = t)  i = 0..bw(s)-1
 */
bool
bzla_is_inv_sll(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;

  bool res;
  if (pos_x == 0)
  {
    BzlaBitVector *t_srl_s = bzla_bv_srl(mm, t, s);
    BzlaBitVector *sll_s   = bzla_bv_sll(mm, t_srl_s, s);
    BzlaBitVector *eq_t    = bzla_bv_eq(mm, sll_s, t);
    res                    = bzla_bv_is_true(eq_t);
    bzla_bv_free(mm, t_srl_s);
    bzla_bv_free(mm, sll_s);
    bzla_bv_free(mm, eq_t);
  }
  else
  {
    assert(pos_x == 1);
    res = false;
    for (uint32_t i = 0, bw_s = bzla_bv_get_width(s); i <= bw_s && !res; i++)
    {
      BzlaBitVector *bv_i    = bzla_bv_uint64_to_bv(mm, i, bw_s);
      BzlaBitVector *s_sll_i = bzla_bv_sll(mm, s, bv_i);
      BzlaBitVector *eq_t    = bzla_bv_eq(mm, s_sll_i, t);
      res                    = bzla_bv_is_true(eq_t);

      bzla_bv_free(mm, bv_i);
      bzla_bv_free(mm, s_sll_i);
      bzla_bv_free(mm, eq_t);
    }
  }
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x >>a s = t
 * IC: (s < bw(s) -> (t << s) >>a s = t) /\ (s >= bw(s) -> (t = ~0 \/ t = 0))
 *
 * pos_x = 1:
 * s <<a x = t
 * IC: (\/ s >>a i = t)  i = 0..bw(s)-1
 */
bool
bzla_is_inv_sra(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;

  bool res;
  uint32_t bw_s = bzla_bv_get_width(s);

  if (pos_x == 0)
  {
    BzlaBitVector *bv_bw_s    = bzla_bv_uint64_to_bv(mm, bw_s, bw_s);
    BzlaBitVector *s_ult_bw_s = bzla_bv_ult(mm, s, bv_bw_s);

    res = true;
    if (bzla_bv_is_true(s_ult_bw_s))
    {
      BzlaBitVector *t_sll_s = bzla_bv_sll(mm, t, s);
      BzlaBitVector *sra_s   = bzla_bv_sra(mm, t_sll_s, s);
      BzlaBitVector *eq_t    = bzla_bv_eq(mm, sra_s, t);
      res                    = bzla_bv_is_true(eq_t);
      bzla_bv_free(mm, t_sll_s);
      bzla_bv_free(mm, sra_s);
      bzla_bv_free(mm, eq_t);
    }
    bzla_bv_free(mm, s_ult_bw_s);
    if (res)
    {
      BzlaBitVector *s_uge_bw_s = bzla_bv_ulte(mm, bv_bw_s, s);
      res = (!bzla_bv_is_true(s_uge_bw_s) || bzla_bv_is_ones(t)
             || bzla_bv_is_zero(t));
      bzla_bv_free(mm, s_uge_bw_s);
    }
    bzla_bv_free(mm, bv_bw_s);
  }
  else
  {
    assert(pos_x == 1);
    res = false;
    for (uint32_t i = 0; i < bw_s && !res; i++)
    {
      BzlaBitVector *bv_i    = bzla_bv_uint64_to_bv(mm, i, bw_s);
      BzlaBitVector *s_sra_i = bzla_bv_sra(mm, s, bv_i);
      BzlaBitVector *eq_t    = bzla_bv_eq(mm, s_sra_i, t);
      res                    = bzla_bv_is_true(eq_t);
      bzla_bv_free(mm, bv_i);
      bzla_bv_free(mm, s_sra_i);
      bzla_bv_free(mm, eq_t);
    }
  }
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x >> s = t
 * IC: (t << s) >> s = t
 *
 * pos_x = 1:
 * s >> x = t
 * IC: (\/ s >> i = t)  i = 0..bw(s)-1
 */
bool
bzla_is_inv_srl(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;

  bool res;
  if (pos_x == 0)
  {
    BzlaBitVector *t_sll_s = bzla_bv_sll(mm, t, s);
    BzlaBitVector *srl_s   = bzla_bv_srl(mm, t_sll_s, s);
    BzlaBitVector *eq_t    = bzla_bv_eq(mm, srl_s, t);
    res                    = bzla_bv_is_true(eq_t);
    bzla_bv_free(mm, t_sll_s);
    bzla_bv_free(mm, srl_s);
    bzla_bv_free(mm, eq_t);
  }
  else
  {
    assert(pos_x == 1);
    res = false;
    for (uint32_t i = 0, bw_s = bzla_bv_get_width(s); i <= bw_s && !res; i++)
    {
      BzlaBitVector *bv_i    = bzla_bv_uint64_to_bv(mm, i, bw_s);
      BzlaBitVector *s_srl_i = bzla_bv_srl(mm, s, bv_i);
      BzlaBitVector *eq_t    = bzla_bv_eq(mm, s_srl_i, t);
      res                    = bzla_bv_is_true(eq_t);
      bzla_bv_free(mm, bv_i);
      bzla_bv_free(mm, s_srl_i);
      bzla_bv_free(mm, eq_t);
    }
  }
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * pos_x = 0:
 * x < s = t
 * IC: t = 0 || s != 0
 *
 * pos_x = 1:
 * s < x = t
 * IC: t = 0 || s != ~0
 */
bool
bzla_is_inv_ult(BzlaMemMgr *mm,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) mm;
  (void) x;

  bool res;
  if (pos_x == 0)
  {
    res = bzla_bv_is_zero(t) || !bzla_bv_is_zero(s);
  }
  else
  {
    assert(pos_x == 1);
    res = bzla_bv_is_zero(t) || !bzla_bv_is_ones(s);
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
bzla_is_inv_udiv(BzlaMemMgr *mm,
                 const BzlaBvDomain *x,
                 const BzlaBitVector *t,
                 const BzlaBitVector *s,
                 uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;

  BzlaBitVector *udiv;
  bool res;
  if (pos_x == 0)
  {
    BzlaBitVector *s_mul_t = bzla_bv_mul(mm, s, t);
    udiv                   = bzla_bv_udiv(mm, s_mul_t, s);
    bzla_bv_free(mm, s_mul_t);
  }
  else
  {
    assert(pos_x == 1);
    BzlaBitVector *s_udiv_t = bzla_bv_udiv(mm, s, t);
    udiv                    = bzla_bv_udiv(mm, s, s_udiv_t);
    bzla_bv_free(mm, s_udiv_t);
  }
  BzlaBitVector *eq_t = bzla_bv_eq(mm, udiv, t);
  res                 = bzla_bv_is_true(eq_t);
  bzla_bv_free(mm, udiv);
  bzla_bv_free(mm, eq_t);
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
bzla_is_inv_urem(BzlaMemMgr *mm,
                 const BzlaBvDomain *x,
                 const BzlaBitVector *t,
                 const BzlaBitVector *s,
                 uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) x;

  bool res;
  BzlaBitVector *neg_s = bzla_bv_neg(mm, s);
  if (pos_x == 0)
  {
    BzlaBitVector *not_neg_s = bzla_bv_not(mm, neg_s);
    BzlaBitVector *uge_t     = bzla_bv_ulte(mm, t, not_neg_s);
    res                      = bzla_bv_is_true(uge_t);
    bzla_bv_free(mm, not_neg_s);
    bzla_bv_free(mm, uge_t);
  }
  else
  {
    assert(pos_x == 1);
    BzlaBitVector *t_add_t = bzla_bv_add(mm, t, t);
    BzlaBitVector *sub_s   = bzla_bv_add(mm, t_add_t, neg_s);
    BzlaBitVector *and_s   = bzla_bv_and(mm, sub_s, s);
    BzlaBitVector *uge_t   = bzla_bv_ulte(mm, t, and_s);
    res                    = bzla_bv_is_true(uge_t);
    bzla_bv_free(mm, t_add_t);
    bzla_bv_free(mm, sub_s);
    bzla_bv_free(mm, and_s);
    bzla_bv_free(mm, uge_t);
  }
  bzla_bv_free(mm, neg_s);
  return res;
}

/**
 * Check invertibility condition (without considering const bits in x) for:
 *
 * x[:] = t
 *
 * IC: true
 */
bool
bzla_is_inv_slice(BzlaMemMgr *mm,
                  const BzlaBvDomain *x,
                  const BzlaBitVector *t,
                  const BzlaBitVector *s,
                  uint32_t pos_x)
{
  assert(mm);
  assert(t);
  assert(s);
  (void) mm;
  (void) x;
  (void) t;
  (void) s;
  (void) pos_x;
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
bzla_is_inv_add_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;

  bool res;
  BzlaBitVector *sub, *and, * or ;

  sub = bzla_bv_sub(mm, t, s);
  and = bzla_bv_and(mm, sub, x->hi);
  or  = bzla_bv_or(mm, and, x->lo);
  res = bzla_bv_compare(or, sub) == 0;
  bzla_bv_free(mm, or);
  bzla_bv_free(mm, and);
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
bzla_is_inv_and_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);

  bool res;
  BzlaBitVector *and1, *and2, *and3, *mask;

  if (!bzla_is_inv_and(mm, x, t, s, pos_x)) return false;

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
 * x o s = t
 * IC: (t_h & hi_x) | lo_x = t_h /\ s = t_l
 *     with
 *     t_h = t[bw(t) - 1 : bw(s)]
 *     t_l = t[bw(s) - 1 : 0]
 *
 * s o x = t
 * IC: (t_l & hi_x) | lo_x = t_l /\ s = t_h
 *     with
 *     t_h = t[bw(t) - 1 : bw(x)]
 *     t_l = t[bw(x) - 1 : 0]
 */
bool
bzla_is_inv_concat_const(BzlaMemMgr *mm,
                         const BzlaBvDomain *x,
                         const BzlaBitVector *t,
                         const BzlaBitVector *s,
                         uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);

  bool res;
  uint32_t bw_t, bw_s, bw_x;
  BzlaBitVector *t_h, *t_l, *t_and, *t_s, *and, * or ;

  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);
  bw_x = bzla_bvprop_get_width(x);

  if (pos_x == 0)
  {
    t_h   = bzla_bv_slice(mm, t, bw_t - 1, bw_s);
    t_l   = bzla_bv_slice(mm, t, bw_s - 1, 0);
    t_and = t_h;
    t_s   = t_l;
  }
  else
  {
    t_h   = bzla_bv_slice(mm, t, bw_t - 1, bw_x);
    t_l   = bzla_bv_slice(mm, t, bw_x - 1, 0);
    t_and = t_l;
    t_s   = t_h;
  }

  and = bzla_bv_and(mm, t_and, x->hi);
  or  = bzla_bv_or(mm, and, x->lo);
  res = bzla_bv_compare(or, t_and) == 0 && bzla_bv_compare(s, t_s) == 0;
  bzla_bv_free(mm, t_h);
  bzla_bv_free(mm, t_l);
  bzla_bv_free(mm, or);
  bzla_bv_free(mm, and);
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
bzla_is_inv_eq_const(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;

  bool res;
  BzlaBitVector *and, * or ;

  if (bzla_bv_is_false(t))
  {
    return bzla_bv_compare(x->hi, x->lo) || bzla_bv_compare(x->hi, s);
  }

  and = bzla_bv_and(mm, s, x->hi);
  or  = bzla_bv_or(mm, and, x->lo);
  res = bzla_bv_compare(or, s) == 0;
  bzla_bv_free(mm, or);
  bzla_bv_free(mm, and);
  return res;
}

bool
bzla_is_inv_mul_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  return true;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * pos_x = 0:
 * x << s = t
 * IC: (t >> s) << s = t
 *     /\ (hi_x << s) & t = t
 *     /\ (lo_x << s) | t = t
 *
 * pos_x = 1:
 * s << x = t
 * IC: (\/ s << i = t)  i = 0..bw(s)-1 for all possible i given x
 */
bool
bzla_is_inv_sll_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);

  bool res, invalid;
  BzlaBitVector *shift1, *shift2, *and, * or ;
  BzlaBitVector *bv_i, *eq;

  if (pos_x == 0)
  {
    if (!bzla_is_inv_sll(mm, x, t, s, pos_x)) return false;
    shift1 = bzla_bv_sll(mm, x->hi, s);
    shift2 = bzla_bv_sll(mm, x->lo, s);
    and    = bzla_bv_and(mm, shift1, t);
    or     = bzla_bv_or(mm, shift2, t);
    res    = bzla_bv_compare(and, t) == 0 && bzla_bv_compare(or, t) == 0;
    bzla_bv_free(mm, or);
    bzla_bv_free(mm, and);
    bzla_bv_free(mm, shift2);
    bzla_bv_free(mm, shift1);
  }
  else
  {
    assert(pos_x == 1);
    res = false;
    for (uint32_t i = 0, bw_s = bzla_bv_get_width(s); i <= bw_s && !res; i++)
    {
      bv_i = bzla_bv_uint64_to_bv(mm, i, bw_s);

      /* check if bv_i is a possible value given x */
      and     = bzla_bv_and(mm, bv_i, x->hi);
      or      = bzla_bv_or(mm, bv_i, x->lo);
      invalid = bzla_bv_compare(or, bv_i) != 0;
      bzla_bv_free(mm, or);
      bzla_bv_free(mm, and);
      if (invalid)
      {
        bzla_bv_free(mm, bv_i);
        continue;
      }

      /* add to IC */
      shift1 = bzla_bv_sll(mm, s, bv_i);
      eq     = bzla_bv_eq(mm, shift1, t);
      res    = bzla_bv_is_true(eq);

      bzla_bv_free(mm, bv_i);
      bzla_bv_free(mm, shift1);
      bzla_bv_free(mm, eq);
    }
  }
  return res;
}

bool
bzla_is_inv_sra_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  return true;
}

bool
bzla_is_inv_srl_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  return true;
}

bool
bzla_is_inv_udiv_const(BzlaMemMgr *mm,
                       const BzlaBvDomain *x,
                       const BzlaBitVector *t,
                       const BzlaBitVector *s,
                       uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  return true;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x < s = t
 * s < x = t
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
bzla_is_inv_ult_const(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);

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

bool
bzla_is_inv_urem_const(BzlaMemMgr *mm,
                       const BzlaBvDomain *x,
                       const BzlaBitVector *t,
                       const BzlaBitVector *s,
                       uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  return true;
}

bool
bzla_is_inv_slice_const(BzlaMemMgr *mm,
                        const BzlaBvDomain *x,
                        const BzlaBitVector *t,
                        const BzlaBitVector *s,
                        uint32_t pos_x)
{
  assert(mm);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  return true;
}
