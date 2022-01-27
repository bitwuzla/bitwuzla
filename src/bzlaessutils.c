/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaessutils.h"

#include <assert.h>

#include "bzlacore.h"
#include "bzlainvutils.h"
#include "bzlaproputils.h"
#include "utils/bzlautil.h"

/* -------------------------------------------------------------------------- */

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
  (void) bzla;
  (void) pi;
  (void) pos_x;
  return false;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x & s = t
 * s & x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x & s = t) when solved for s
 * pos_x = 1: !is_inv (s & x = t) when solved for s
 */
bool
bzla_is_ess_and(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_and(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x ^ s = t
 * s ^ x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x ^ s = t) when solved for s
 * pos_x = 1: !is_inv (s ^ x = t) when solved for s
 */
bool
bzla_is_ess_xor(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  (void) bzla;
  (void) pi;
  (void) pos_x;
  return false;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x o s = t
 * s o x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x o s = t) when solved for s
 * pos_x = 1: !is_inv (s o x = t) when solved for s
 */
bool
bzla_is_ess_concat(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_concat(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * (x = s) = t
 * (s = x) = t
 *
 * EC:
 * pos_x = 0: !is_inv ((x = s) = t) when solved for s
 * pos_x = 1: !is_inv ((s = x) = t) when solved for s
 */
bool
bzla_is_ess_eq(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_eq(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x * s = t
 * s * x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x * s = t) when solved for s
 * pos_x = 1: !is_inv (s * x = t) when solved for s
 */
bool
bzla_is_ess_mul(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_mul(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x[u:l] = t
 *
 * EC: x[u:l] == t
 */
bool
bzla_is_ess_slice(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);
  (void) pos_x;

  bool res;
  BzlaBitVector *slice;
  slice = bzla_bv_slice(bzla->mm,
                        pi->bv[0],
                        bzla_node_bv_slice_get_upper(pi->exp),
                        bzla_node_bv_slice_get_lower(pi->exp));
  res   = bzla_bv_compare(slice, pi->target_value) != 0;
  bzla_bv_free(bzla->mm, slice);
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x << s = t
 * s << x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x << s = t) when solved for s
 * pos_x = 1: !is_inv (s << x = t) when solved for s
 */
bool
bzla_is_ess_sll(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_sll(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x >> s = t
 * s >> x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x >> s = t) when solved for s
 * pos_x = 1: !is_inv (s >> x = t) when solved for s
 */
bool
bzla_is_ess_srl(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_srl(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x >>a s = t
 * s >>a x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x >>a s = t) when solved for s
 * pos_x = 1: !is_inv (s >>a x = t) when solved for s
 */
bool
bzla_is_ess_sra(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_sra(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x / s = t
 * s / x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x / s = t) when solved for s
 * pos_x = 1: !is_inv (s / x = t) when solved for s
 */
bool
bzla_is_ess_udiv(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_udiv(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x < s = t
 * s < x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x < s = t) when solved for s
 * pos_x = 1: !is_inv (s < x = t) when solved for s
 */
bool
bzla_is_ess_ult(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_ult(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x <s s = t
 * s <s x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x <s s = t) when solved for s
 * pos_x = 1: !is_inv (s <s x = t) when solved for s
 */
bool
bzla_is_ess_slt(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_slt(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x % s = t
 * s % x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x % s = t) when solved for s
 * pos_x = 1: !is_inv (s % x = t) when solved for s
 */
bool
bzla_is_ess_urem(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_urem(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t.
 *
 * x  ? s0 : s1 = t
 * s0 ?  x : s1 = t
 * s0 ? s1 :  x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x  ? s0 : s1 = t) when solved for enabled s
 * pos_x = 1: false if branch not enabled
 *            else !is_inv (s0 ?  x : s1 = t) when solved for enabled s
 * pos_x = 2: false if branch not enabled
 *            else !is_inv (s0 ? s1 : s0 = t) when solved for enabled s
 */
bool
bzla_is_ess_cond(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  if (pos_x == 0)
  {
    pi->pos_x = bzla_bv_is_true(pi->bv[pos_x]) ? 1 : 2;
    res       = !bzla_is_inv_cond(bzla, pi);
  }
  else if (pos_x == 1)
  {
    if (bzla_bv_is_false(pi->bv[0]))
    {
      res = false;
    }
    else
    {
      pi->pos_x = 1;
      res       = !bzla_is_inv_cond(bzla, pi);
    }
  }
  else
  {
    if (bzla_bv_is_true(pi->bv[0]))
    {
      res = false;
    }
    else
    {
      pi->pos_x = 2;
      res       = !bzla_is_inv_cond(bzla, pi);
    }
  }
  pi->pos_x = tmp;
  return res;
}

/* -------------------------------------------------------------------------- */

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
  res          = !bzla_is_inv_add_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x & s = t
 * s & x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x & s = t) when solved for s (w.r.t. const bits in s)
 * pos_x = 1: !is_inv (s & x = t) when solved for s (w.r.t. const bits in s)
 */
bool
bzla_is_ess_and_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_and_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x ^ s = t
 * s ^ x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x & s = t) when solved for s (w.r.t. const bits in s)
 * pos_x = 1: !is_inv (s & x = t) when solved for s (w.r.t. const bits in s)
 */
bool
bzla_is_ess_xor_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_xor_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x o s = t
 * s o x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x o s = t) when solved for s
 * pos_x = 1: !is_inv (s o x = t) when solved for s
 */
bool
bzla_is_ess_concat_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_concat_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * (x = s) = t
 * (s = x) = t
 *
 * EC:
 * pos_x = 0: !is_inv ((x = s) = t) when solved for s
 * pos_x = 1: !is_inv ((s = x) = t) when solved for s
 */
bool
bzla_is_ess_eq_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_eq_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x * s = t
 * s * x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x * s = t) when solved for s
 * pos_x = 1: !is_inv (s * x = t) when solved for s
 */
bool
bzla_is_ess_mul_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_mul_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x[u:l] = t
 *
 * EC: x[u:l] == t
 */
bool
bzla_is_ess_slice_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);
  (void) pos_x;

  bool res;
  BzlaBitVector *slice;
  slice = bzla_bv_slice(bzla->mm,
                        pi->bv[0],
                        bzla_node_bv_slice_get_upper(pi->exp),
                        bzla_node_bv_slice_get_lower(pi->exp));
  res   = bzla_bv_compare(slice, pi->target_value) != 0;
  bzla_bv_free(bzla->mm, slice);
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x << s = t
 * s << x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x << s = t) when solved for s
 * pos_x = 1: !is_inv (s << x = t) when solved for s
 */
bool
bzla_is_ess_sll_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_sll_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x >> s = t
 * s >> x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x >> s = t) when solved for s
 * pos_x = 1: !is_inv (s >> x = t) when solved for s
 */
bool
bzla_is_ess_srl_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_srl_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x >>a s = t
 * s >>a x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x >>a s = t) when solved for s
 * pos_x = 1: !is_inv (s >>a x = t) when solved for s
 */
bool
bzla_is_ess_sra_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_sra_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x / s = t
 * s / x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x / s = t) when solved for s
 * pos_x = 1: !is_inv (s / x = t) when solved for s
 */
bool
bzla_is_ess_udiv_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_udiv_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x < s = t
 * s < x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x < s = t) when solved for s
 * pos_x = 1: !is_inv (s < x = t) when solved for s
 */
bool
bzla_is_ess_ult_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_ult_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x <s s = t
 * s <s x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x <s s = t) when solved for s
 * pos_x = 1: !is_inv (s <s x = t) when solved for s
 */
bool
bzla_is_ess_slt_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_slt_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x % s = t
 * s % x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x % s = t) when solved for s
 * pos_x = 1: !is_inv (s % x = t) when solved for s
 */
bool
bzla_is_ess_urem_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp = pi->pos_x;
  pi->pos_x    = 1 - pos_x;
  res          = !bzla_is_inv_urem_const(bzla, pi);
  pi->pos_x    = tmp;
  return res;
}

/*
 * Check if x is essential w.r.t. to t and constant bits in s for:
 *
 * x  ? s0 : s1 = t
 * s0 ?  x : s1 = t
 * s0 ? s1 :  x = t
 *
 * EC:
 * pos_x = 0: !is_inv (x ? s0 : s1 = t) when solved for enabled s
 * pos_x = 1: (fixed(s0) => (s0 = 1 => x != t) /\ (s0 = 0 => mcb(s1, t))) /\
 *            (!fixed(s0) => mcb(s1, t))
 * pos_x = 2: (fixed(s0) => (s0 = 1 => x != t) /\ (s0 = 0 => mcb(s2, t))) /\
 *            (!fixed(s0) => mcb(s2, t))
 */
bool
bzla_is_ess_cond_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x)
{
  assert(bzla);
  assert(pi);

  bool res;
  uint32_t tmp, pos_s0, pos_s1;
  const BzlaBitVector *x, *t;
  const BzlaBvDomain *s0, *s1;
  BzlaMemMgr *mm;

  mm     = bzla->mm;
  tmp    = pi->pos_x;
  pos_s0 = pos_x == 0 ? 1 : 0;
  pos_s1 = pos_x == 2 ? 1 : 2;
  x      = pi->bv[pos_x];
  s0     = pi->bvd[pos_s0];
  s1     = pi->bvd[pos_s1];
  t      = pi->target_value;

  if (pos_x == 0)
  {
    pi->pos_x = bzla_bv_is_true(pi->bv[pos_x]) ? 1 : 2;
    res       = !bzla_is_inv_cond_const(bzla, pi);
  }
  else if (bzla_bvdomain_is_fixed(mm, s0))
  {
    if (bzla_bv_is_true(s0->lo))
    {
      if (pos_x == 1)
      {
        res = bzla_bv_compare(x, t) != 0;
      }
      else
      {
        res = !bzla_bvdomain_check_fixed_bits(mm, s1, t);
      }
    }
    else
    {
      if (pos_x == 2)
      {
        res = bzla_bv_compare(x, t) != 0;
      }
      else
      {
        res = !bzla_bvdomain_check_fixed_bits(mm, s1, t);
      }
    }
  }
  else
  {
    res = bzla_bv_compare(x, t) != 0;
    if (res)
    {
      res = !bzla_bvdomain_check_fixed_bits(mm, s1, t);
    }
  }
  pi->pos_x = tmp;
  return res;
}
