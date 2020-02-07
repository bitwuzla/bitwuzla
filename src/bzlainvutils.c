/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018-2020 Aina Niemetz.
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

#include "bzlacore.h"

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
bzla_is_inv_add(Bzla *bzla,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x,
                BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) bzla;
  (void) x;
  (void) t;
  (void) s;
  (void) pos_x;
  (void) d_res_x;
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
bzla_is_inv_and(Bzla *bzla,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x,
                BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) pos_x;
  (void) d_res_x;

  bool res;
  BzlaBitVector *t_and_s;
  BzlaMemMgr *mm;

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
bzla_is_inv_concat(Bzla *bzla,
                   const BzlaBvDomain *x,
                   const BzlaBitVector *t,
                   const BzlaBitVector *s,
                   uint32_t pos_x,
                   BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) d_res_x;

  BzlaBitVector *slice;
  bool res;
  uint32_t bw_s, bw_t;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
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
bzla_is_inv_eq(Bzla *bzla,
               const BzlaBvDomain *x,
               const BzlaBitVector *t,
               const BzlaBitVector *s,
               uint32_t pos_x,
               BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) bzla;
  (void) x;
  (void) t;
  (void) s;
  (void) pos_x;
  (void) d_res_x;
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
bzla_is_inv_mul(Bzla *bzla,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x,
                BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) pos_x;
  (void) d_res_x;

  bool res;
  BzlaBitVector *neg_s, *neg_s_or_s, *and_t;
  BzlaMemMgr *mm;

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
bzla_is_inv_sll(Bzla *bzla,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x,
                BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) d_res_x;

  bool res;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  if (pos_x == 0)
  {
    BzlaBitVector *t_srl_s = bzla_bv_srl(mm, t, s);
    BzlaBitVector *sll_s   = bzla_bv_sll(mm, t_srl_s, s);
    res                    = bzla_bv_compare(sll_s, t) == 0;
    bzla_bv_free(mm, t_srl_s);
    bzla_bv_free(mm, sll_s);
  }
  else
  {
    assert(pos_x == 1);
    res = false;
    for (uint32_t i = 0, bw_s = bzla_bv_get_width(s); i <= bw_s && !res; i++)
    {
      BzlaBitVector *bv_i    = bzla_bv_uint64_to_bv(mm, i, bw_s);
      BzlaBitVector *s_sll_i = bzla_bv_sll(mm, s, bv_i);
      res                    = bzla_bv_compare(s_sll_i, t) == 0;

      bzla_bv_free(mm, bv_i);
      bzla_bv_free(mm, s_sll_i);
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
bzla_is_inv_srl(Bzla *bzla,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x,
                BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) d_res_x;

  bool res;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  if (pos_x == 0)
  {
    BzlaBitVector *t_sll_s = bzla_bv_sll(mm, t, s);
    BzlaBitVector *srl_s   = bzla_bv_srl(mm, t_sll_s, s);
    res                    = bzla_bv_compare(srl_s, t) == 0;
    bzla_bv_free(mm, t_sll_s);
    bzla_bv_free(mm, srl_s);
  }
  else
  {
    assert(pos_x == 1);
    res = false;
    for (uint32_t i = 0, bw_s = bzla_bv_get_width(s); i <= bw_s && !res; i++)
    {
      BzlaBitVector *bv_i    = bzla_bv_uint64_to_bv(mm, i, bw_s);
      BzlaBitVector *s_srl_i = bzla_bv_srl(mm, s, bv_i);
      res                    = bzla_bv_compare(s_srl_i, t) == 0;
      bzla_bv_free(mm, bv_i);
      bzla_bv_free(mm, s_srl_i);
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
bzla_is_inv_ult(Bzla *bzla,
                const BzlaBvDomain *x,
                const BzlaBitVector *t,
                const BzlaBitVector *s,
                uint32_t pos_x,
                BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) bzla;
  (void) x;
  (void) d_res_x;

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
bzla_is_inv_udiv(Bzla *bzla,
                 const BzlaBvDomain *x,
                 const BzlaBitVector *t,
                 const BzlaBitVector *s,
                 uint32_t pos_x,
                 BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) d_res_x;

  bool res;
  BzlaBitVector *udiv;
  BzlaMemMgr *mm;

  mm = bzla->mm;
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
bzla_is_inv_urem(Bzla *bzla,
                 const BzlaBvDomain *x,
                 const BzlaBitVector *t,
                 const BzlaBitVector *s,
                 uint32_t pos_x,
                 BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(t);
  assert(s);
  (void) x;
  (void) d_res_x;

  bool res;
  BzlaBitVector *neg_s;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  neg_s = bzla_bv_neg(mm, s);

  if (pos_x == 0)
  {
    BzlaBitVector *not_neg_s = bzla_bv_not(mm, neg_s);
    res                      = bzla_bv_compare(t, not_neg_s) <= 0;
    bzla_bv_free(mm, not_neg_s);
  }
  else
  {
    assert(pos_x == 1);
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
 * x[upper:lower] = t
 *
 * IC: true
 */
bool
bzla_is_inv_slice(Bzla *bzla,
                  const BzlaBvDomain *x,
                  const BzlaBitVector *t,
                  uint32_t upper,
                  uint32_t lower)
{
  assert(bzla);
  assert(t);
  (void) bzla;
  (void) x;
  (void) t;
  (void) upper;
  (void) lower;
  return true;
}

/* -------------------------------------------------------------------------- */
/* Check invertibility while considering constant bits in x.                  */
/* -------------------------------------------------------------------------- */

/** Check if const bits of domain 'd' match const bits of bit-vector 'bv'. */
static bool
check_const_bits(BzlaMemMgr *mm, const BzlaBvDomain *d, const BzlaBitVector *bv)
{
  bool res;
  BzlaBitVector *and, * or ;
  and = bzla_bv_and(mm, bv, d->hi);
  or  = bzla_bv_or(mm, and, d->lo);
  res = bzla_bv_compare(or, bv) == 0;
  bzla_bv_free(mm, or);
  bzla_bv_free(mm, and);
  return res;
}

/** Check if const bits of domain 'd' match given value 'val'. */
static bool
check_const_bits_val(BzlaMemMgr *mm, const BzlaBvDomain *d, uint32_t val)
{
  bool res;
  uint32_t bw;
  BzlaBitVector *bv;
  bw  = bzla_bv_get_width(d->lo);
  bv  = val ? bzla_bv_ones(mm, bw) : bzla_bv_new(mm, bw);
  res = check_const_bits(mm, d, bv);
  bzla_bv_free(mm, bv);
  return res;
}

/** Check if const bits of domain 'd1' match const bits of domain 'd2'. */
static bool
check_const_domain_bits(BzlaMemMgr *mm,
                        const BzlaBvDomain *d1,
                        const BzlaBvDomain *d2)
{
  bool res;
  BzlaBitVector *const_d1, *const_d2, *common, *masked_d1, *masked_d2;

  const_d1  = bzla_bv_xnor(mm, d1->lo, d1->hi);
  const_d2  = bzla_bv_xnor(mm, d2->lo, d2->hi);
  common    = bzla_bv_and(mm, const_d1, const_d2);
  masked_d1 = bzla_bv_and(mm, common, d1->lo);
  masked_d2 = bzla_bv_and(mm, common, d2->lo);

  res = bzla_bv_compare(masked_d1, masked_d2) == 0;

  bzla_bv_free(mm, const_d1);
  bzla_bv_free(mm, const_d2);
  bzla_bv_free(mm, common);
  bzla_bv_free(mm, masked_d1);
  bzla_bv_free(mm, masked_d2);
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x + s = t
 * s + x = t
 *
 * IC: (((t - s) & hi_x) | lo_x) = t - s
 */
bool
bzla_is_inv_add_const(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  (void) d_res_x;

  bool res;
  BzlaBitVector *sub;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  sub = bzla_bv_sub(mm, t, s);
  res = check_const_bits(mm, x, sub);
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
bzla_is_inv_and_const(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

  bool res;
  BzlaBitVector *and1, *and2, *and3, *mask;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (!bzla_is_inv_and(bzla, x, t, s, pos_x, 0)) return false;

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
bzla_is_inv_concat_const(Bzla *bzla,
                         const BzlaBvDomain *x,
                         const BzlaBitVector *t,
                         const BzlaBitVector *s,
                         uint32_t pos_x,
                         BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

  bool res;
  uint32_t bw_t, bw_s, bw_x;
  BzlaBitVector *t_h, *t_l, *t_and, *t_s, *and, * or ;
  BzlaMemMgr *mm;

  mm = bzla->mm;

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
bzla_is_inv_eq_const(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) pos_x;
  (void) d_res_x;

  if (bzla_bv_is_false(t))
  {
    return bzla_bv_compare(x->hi, x->lo) || bzla_bv_compare(x->hi, s);
  }

  return check_const_bits(bzla->mm, x, s);
}

bool
bzla_is_inv_mul_const(Bzla *bzla,
                      const BzlaBvDomain *d_x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(d_x);
  assert(t);
  assert(s);
  (void) pos_x;

  bool res = true, lsb_s;
  BzlaBitVector *mod_inv_s, *x;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  res = bzla_is_inv_mul(bzla, d_x, t, s, pos_x, 0);

  if (res && !bzla_bv_is_zero(s) && bzla_bvprop_has_fixed_bits(mm, d_x))
  {
    /* d_x is constant */
    if (bzla_bvprop_is_fixed(mm, d_x))
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
        res       = check_const_bits(mm, d_x, x);
        if (d_res_x && res)
        {
          *d_res_x = bzla_bvprop_new(mm, x, x);
        }
        bzla_bv_free(mm, x);
        bzla_bv_free(mm, mod_inv_s);
      }
      /* s even */
      else
      {
        /* d_x = (t >> ctz(s)) * (s >> ctz(s))^-1 */

        BzlaBitVector *tmp_s, *tmp_t, *tmp_x, *mask_lo, *mask_hi, *ones;
        BzlaBitVector *lo, *hi;
        BzlaBvDomain *d_tmp_x;
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

        /* create domain of d_x with the most ctz(s) bits set to 'd_x'. */
        ones    = bzla_bv_ones(mm, bzla_bv_get_width(tmp_x));
        mask_lo = bzla_bv_srl_uint64(mm, ones, tz_s);
        mask_hi = bzla_bv_not(mm, mask_lo);
        bzla_bv_free(mm, ones);

        lo      = bzla_bv_and(mm, mask_lo, tmp_x);
        hi      = bzla_bv_or(mm, mask_hi, tmp_x);
        d_tmp_x = bzla_bvprop_new(mm, lo, hi);
        bzla_bv_free(mm, tmp_x);
        bzla_bv_free(mm, mask_lo);
        bzla_bv_free(mm, mask_hi);
        bzla_bv_free(mm, lo);
        bzla_bv_free(mm, hi);

        res = check_const_domain_bits(mm, d_tmp_x, d_x);
        if (d_res_x && res)
        {
          *d_res_x = d_tmp_x;
        }
        else
        {
          bzla_bvprop_free(mm, d_tmp_x);
        }
      }
    }
  }
  return res;
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
bzla_is_inv_sll_const(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

  bool res;
  uint32_t bw, i, cnt;
  BzlaBitVector *shift1, *shift2, *and, * or ;
  BzlaBitVector *bv, *bv_bw;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;
  BzlaBitVectorPtrStack results;

  mm = bzla->mm;

  if (pos_x == 0)
  {
    if (!bzla_is_inv_sll(bzla, x, t, s, pos_x, 0)) return false;
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
    res = false;
    BZLA_INIT_STACK(mm, results);
    assert(pos_x == 1);
    bw    = bzla_bv_get_width(s);
    bv_bw = bzla_bv_uint64_to_bv(mm, bw, bw);
    res   = bzla_bv_compare(x->hi, bv_bw) >= 0 && bzla_bv_is_zero(t);
    bzla_bv_free(mm, bv_bw);
    if (bzla_bvprop_is_fixed(mm, x))
    {
      shift1 = bzla_bv_sll(mm, s, x->lo);
      res    = bzla_bv_compare(shift1, t) == 0;
      if (res)
      {
        BZLA_PUSH_STACK(results, bzla_bv_copy(mm, x->lo));
      }
      bzla_bv_free(mm, shift1);
    }
    else
    {
      bzla_bvprop_gen_init(mm, &bzla->rng, &gen, x);
      while (bzla_bvprop_gen_has_next(&gen))
      {
        bv = bzla_bvprop_gen_next(&gen);
        if (check_const_bits(mm, x, bv))
        {
          shift1 = bzla_bv_sll(mm, s, bv);
          if (bzla_bv_compare(shift1, t) == 0)
          {
            if (!res) res = true;
            if (!d_res_x)
            {
              bzla_bv_free(mm, shift1);
              break;
            }
            BZLA_PUSH_STACK(results, bzla_bv_copy(mm, bv));
          }
          bzla_bv_free(mm, shift1);
        }
      }
      bzla_bvprop_gen_delete(&gen);
    }
    if (d_res_x && (cnt = BZLA_COUNT_STACK(results)))
    {
      assert(!res || cnt);
      i        = bzla_rng_pick_rand(&bzla->rng, 0, cnt - 1);
      *d_res_x = bzla_bvprop_new(
          mm, BZLA_PEEK_STACK(results, i), BZLA_PEEK_STACK(results, i));
    }
    while (!BZLA_EMPTY_STACK(results))
    {
      bzla_bv_free(mm, BZLA_POP_STACK(results));
    }
    BZLA_RELEASE_STACK(results);
  }
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * pos_x = 0:
 * x << s = t
 * IC: (t << s) >> s = t
 *     /\ (hi_x >> s) & t = t
 *     /\ (lo_x >> s) | t = t
 *
 * pos_x = 1:
 * s >> x = t
 * IC: (\/ s >> i = t)  i = 0..bw(s)-1 for all possible i given x
 */
bool
bzla_is_inv_srl_const(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

  bool res, invalid;
  uint32_t bw_s;
  BzlaBitVector *shift1, *shift2, *and, * or ;
  BzlaBitVector *bv_i, *bv_bw;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (pos_x == 0)
  {
    if (!bzla_is_inv_srl(bzla, x, t, s, pos_x, 0)) return false;
    shift1 = bzla_bv_srl(mm, x->hi, s);
    shift2 = bzla_bv_srl(mm, x->lo, s);
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
    bw_s  = bzla_bv_get_width(s);
    bv_bw = bzla_bv_uint64_to_bv(mm, bw_s, bw_s);
    res   = bzla_bv_compare(x->hi, bv_bw) >= 0 && bzla_bv_is_zero(t);
    bzla_bv_free(mm, bv_bw);
    for (uint32_t i = 0; i <= bw_s && !res; i++)
    {
      bv_i = bzla_bv_uint64_to_bv(mm, i, bw_s);

      /* check if bv_i is a possible value given x */
      and = bzla_bv_and(mm, bv_i, x->hi);
      or  = bzla_bv_or(mm, bv_i, x->lo);
      invalid =
          bzla_bv_compare(or, bv_i) != 0 || bzla_bv_compare(and, bv_i) != 0;
      bzla_bv_free(mm, or);
      bzla_bv_free(mm, and);
      if (!invalid)
      {
        /* add to IC */
        shift1 = bzla_bv_srl(mm, s, bv_i);
        res    = bzla_bv_compare(shift1, t) == 0;
        bzla_bv_free(mm, shift1);
      }
      bzla_bv_free(mm, bv_i);
    }
  }
  return res;
}

bool
bzla_is_inv_udiv_const(Bzla *bzla,
                       const BzlaBvDomain *x,
                       const BzlaBitVector *t,
                       const BzlaBitVector *s,
                       uint32_t pos_x,
                       BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

  bool res = true;
  BzlaBitVector *tmp, *min, *max;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  res = bzla_is_inv_udiv(bzla, x, t, s, pos_x, 0);

  if (res && bzla_bvprop_has_fixed_bits(mm, x))
  {
    /* x is constant */
    if (bzla_bvprop_is_fixed(mm, x))
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

          if (bzla_bv_compare(x->lo, min) > 0)
          {
            bzla_bv_free(mm, min);
            min = bzla_bv_copy(mm, x->lo);
          }

          if (bzla_bv_compare(x->hi, max) < 0)
          {
            bzla_bv_free(mm, max);
            max = bzla_bv_copy(mm, x->hi);
          }

          BzlaBvDomainGenerator dgen;
          bzla_bvprop_gen_init_range(mm, 0, &dgen, x, min, max);
          res = bzla_bvprop_gen_has_next(&dgen);
          bzla_bvprop_gen_delete(&dgen);
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
              tmp = bzla_bv_inc(mm, t);
              min = bzla_bv_udiv(mm, s, tmp);
              bzla_bv_free(mm, tmp);
              max = bzla_bv_udiv(mm, s, t);
            }

            BzlaBvDomainGenerator dgen;
            bzla_bvprop_gen_init_range(mm, 0, &dgen, x, min, max);
            res = false;
            while (bzla_bvprop_gen_has_next(&dgen))
            {
              tmp = bzla_bv_udiv(mm, s, bzla_bvprop_gen_next(&dgen));
              res = bzla_bv_compare(tmp, t) == 0;
              bzla_bv_free(mm, tmp);
              if (res) break;
            }
            bzla_bvprop_gen_delete(&dgen);
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
bzla_is_inv_ult_const(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

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
bzla_is_inv_urem_const(Bzla *bzla,
                       const BzlaBvDomain *x,
                       const BzlaBitVector *t,
                       const BzlaBitVector *s,
                       uint32_t pos_x,
                       BzlaBvDomain **d_res_x)
{
  assert(bzla);
  assert(x);
  assert(t);
  assert(s);
  (void) d_res_x;

  bool res;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  res = bzla_is_inv_urem(bzla, x, t, s, pos_x, 0);

  if (res)
  {
    BzlaBitVectorPtrStack candidates;
    uint32_t bw;
    int32_t cmp;
    BzlaBitVector *n_hi, *one, *ones, *hi, *lo, *sub, *mul, *div, *rem, *bv;

    bw   = bzla_bv_get_width(t);
    ones = bzla_bv_ones(mm, bw);
    one  = bzla_bv_one(mm, bw);
    if (pos_x)
    {
      if (bzla_bvprop_is_fixed(mm, x))
      {
        rem = bzla_bv_urem(mm, s, x->lo);
        res = bzla_bv_compare(rem, t) == 0;
        bzla_bv_free(mm, rem);
      }
      else if (bzla_bv_compare(t, ones) == 0)
      {
        /* s % x = t = ones: s = ones, x = 0 */
        assert(bzla_bv_compare(s, ones) == 0);
        res = check_const_bits_val(mm, x, 0);
      }
      else
      {
        cmp = bzla_bv_compare(s, t);
        assert(cmp >= 0);
        if (cmp == 0)
        {
          /* s = t and t != ones: x = 0 or random x > t */
          res = bzla_bv_is_zero(x->lo) || bzla_bv_compare(x->hi, t) > 0;
        }
        else
        {
          /**
           * s > t:
           *
           * x > t, x = (s - t) / n
           * -> (s - t) / n > t and
           * -> (s - t) / t > n
           * -> 1 <= n < (s - t) / t
           *
           * bv division is truncating, thus:
           *
           *    1 <= n <= n_hi
           *
           * with: t = 0          : n_hi = s
           *       (s - t) % t = 0: n_hi = (s - t) / t - 1 if > t else t + 1
           *       (s - t) % t > 0: n_hi = (s - t) / t
           */
          sub = bzla_bv_sub(mm, s, t);
          if (bzla_bv_is_zero(t))
          {
            n_hi = bzla_bv_copy(mm, s);
          }
          else
          {
            bzla_bv_udiv_urem(mm, sub, t, &div, &rem);
            if (bzla_bv_is_zero(rem))
            {
              n_hi = bzla_bv_dec(mm, div);
              bzla_bv_free(mm, div);
            }
            else
            {
              n_hi = div;
            }
            bzla_bv_free(mm, rem);
            assert(bzla_bv_compare(n_hi, one) >= 0);
          }
          hi = sub;
          lo = bzla_bv_udiv(mm, sub, n_hi);
          if (bzla_bv_compare(lo, t) <= 0)
          {
            bzla_bv_free(mm, lo);
            lo = bzla_bv_inc(mm, t);
          }
          bzla_bv_free(mm, n_hi);
          BZLA_INIT_STACK(mm, candidates);
          BzlaBvDomainGenerator gen;
          bzla_bvprop_gen_init_range(mm, 0, &gen, (BzlaBvDomain *) x, lo, hi);
          while (bzla_bvprop_gen_has_next(&gen))
          {
            bv  = bzla_bvprop_gen_next(&gen);
            rem = bzla_bv_urem(mm, s, bv);
            if (bzla_bv_compare(rem, t) == 0)
            {
              if (check_const_bits(mm, x, bv))
              {
                BZLA_PUSH_STACK(candidates, bv);
              }
            }
            bzla_bv_free(mm, rem);
          }
          /* Note: The elements on stack 'candidates' are not valid anymore
           * since the bit-vector that bzla_bvprop_gen_next returns is not a
           * copy and gets released on the next bzla_bvprop_gen_next call. */
          res = !BZLA_EMPTY_STACK(candidates);
          BZLA_RELEASE_STACK(candidates);
          bzla_bvprop_gen_delete(&gen);
          bzla_bv_free(mm, hi);
          bzla_bv_free(mm, lo);
        }
      }
    }
    else
    {
      if (bzla_bvprop_is_fixed(mm, x))
      {
        rem = bzla_bv_urem(mm, x->lo, s);
        res = bzla_bv_compare(rem, t) == 0;
        bzla_bv_free(mm, rem);
      }
      else if (bzla_bv_is_zero(s) || bzla_bv_compare(t, ones) == 0)
      {
        /* x % 0 = t: x = t
         * t = ones : s = 0, x = ones */
        res = check_const_bits(mm, x, t);
      }
      else
      {
        assert(bzla_bv_compare(s, t) > 0);
        if (!check_const_bits(mm, x, t))
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
            BZLA_INIT_STACK(mm, candidates);
            BzlaBvDomainGenerator gen;
            /* x->lo <= x <= hi */
            bzla_bvprop_gen_init_range(mm, 0, &gen, (BzlaBvDomain *) x, 0, hi);
            while (bzla_bvprop_gen_has_next(&gen))
            {
              bv  = bzla_bvprop_gen_next(&gen);
              rem = bzla_bv_urem(mm, bv, s);
              if (bzla_bv_compare(rem, t) == 0)
              {
                if (check_const_bits(mm, x, bv))
                {
                  BZLA_PUSH_STACK(candidates, bv);
                }
              }
              bzla_bv_free(mm, rem);
            }
            res = !BZLA_EMPTY_STACK(candidates);
            BZLA_RELEASE_STACK(candidates);
            bzla_bvprop_gen_delete(&gen);
            bzla_bv_free(mm, hi);
            bzla_bv_free(mm, n_hi);
          }
          bzla_bv_free(mm, sub);
        }
      }
    }
    bzla_bv_free(mm, one);
    bzla_bv_free(mm, ones);
  }
  return res;
}

/**
 * Check invertibility condition with respect to const bits in x for:
 *
 * x[upper:lower] = t
 *
 * IC:
 * m = ~(lo_x ^ hi_x)[upper:lower]  ... mask out all non-constant bits
 * x[upper:lower] & m = t & m
 */
bool
bzla_is_inv_slice_const(Bzla *bzla,
                        const BzlaBvDomain *x,
                        const BzlaBitVector *t,
                        uint32_t upper,
                        uint32_t lower)
{
  assert(bzla);
  assert(x);
  assert(t);

  bool res;
  BzlaBitVector *mask, *mask_sliced, *x_mask, *t_mask;
  BzlaMemMgr *mm;

  mm          = bzla->mm;
  mask        = bzla_bv_xnor(mm, x->lo, x->hi);
  mask_sliced = bzla_bv_slice(mm, mask, upper, lower);

  x_mask = bzla_bv_slice(mm, x->lo, upper, lower);
  t_mask = bzla_bv_and(mm, mask_sliced, t);
  res    = bzla_bv_compare(x_mask, t_mask) == 0;

  bzla_bv_free(mm, mask);
  bzla_bv_free(mm, mask_sliced);
  bzla_bv_free(mm, x_mask);
  bzla_bv_free(mm, t_mask);

  return res;
}
