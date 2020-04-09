/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlaproputils.h"

#include "bzlabv.h"
#include "bzlainvutils.h"
#include "bzlanode.h"
#include "bzlaprintmodel.h"
#include "bzlaslsutils.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "utils/bzlahash.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

/* ========================================================================== */

typedef int32_t (*BzlaPropSelectPath)(Bzla *, BzlaPropInfo *);

/* ========================================================================== */

/**
 * Create a bit-vector with all bits that are const bits in domain d_res_x
 * set to their const value, and all other bits set to their value in res_x.
 */
static void
set_const_bits(BzlaMemMgr *mm, const BzlaBvDomain *d, BzlaBitVector **res)
{
  assert(d);
  assert(res);
  assert(*res);
  BzlaBitVector *tmp = bzla_bv_and(mm, d->hi, *res);
  bzla_bv_free(mm, *res);
  *res = bzla_bv_or(mm, d->lo, tmp);
  bzla_bv_free(mm, tmp);
}

/* ========================================================================== */
/* Path selection (for down-propagation)                                      */
/* ========================================================================== */

#ifndef NBZLALOG
static void
select_path_log(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  BzlaNode *exp;
  char *a;
  BzlaMemMgr *mm = bzla->mm;

  exp = bzla_node_real_addr(pi->exp);

  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(exp));

  for (size_t i = 0; i < exp->arity; i++)
  {
    a = bzla_bv_to_char(mm, pi->bv[i]);
    BZLALOG(
        2, "       e[%zu]: %s (%s)", i, bzla_util_node2string(exp->e[i]), a);
    bzla_mem_freestr(mm, a);

    if (pi->bvd[i])
    {
      BZLALOG(2, "       domain[%zu]: %s", i, bzla_bvdomain_to_str(pi->bvd[i]));
    }
  }

  BZLALOG(2, "    * selected: %u", pi->pos_x);
  if (pi->bvd[pi->pos_x])
  {
    BZLALOG(2,
            "      domain[%u]: %s",
            pi->pos_x,
            bzla_bvdomain_to_str(pi->bvd[pi->pos_x]));
  }
}
#endif

static int32_t
select_path_non_const(const BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(exp->arity <= 2);
  assert(!bzla_node_is_bv_const(exp->e[0])
         || (exp->arity > 1 && !bzla_node_is_bv_const(exp->e[1])));

  uint32_t i;
  int32_t idx_x;

  for (i = 0, idx_x = -1; i < exp->arity; i++)
  {
    if (bzla_node_is_bv_const(exp->e[i]))
    {
      idx_x = i ? 0 : 1;
      break;
    }
  }
  assert(exp->arity == 1 || idx_x == -1
         || !bzla_node_is_bv_const(exp->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_random(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  int32_t idx_x = (int32_t) bzla_rng_pick_rand(&bzla->rng, 0, exp->arity - 1);
  assert(!bzla_node_is_bv_const(exp->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_add(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;

  pos_x = select_path_non_const(pi->exp);
  if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_and(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  uint32_t opt;
  int32_t i, pos_x;
  BzlaNode *exp;
  BzlaBitVector *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  exp = (BzlaNode *) pi->exp;
  s   = (BzlaBitVector **) pi->bv;
  t   = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const(exp);

  if (pos_x == -1)
  {
    opt = bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL);

    if (opt == BZLA_PROP_PATH_SEL_RANDOM)
    {
      pos_x = select_path_random(bzla, exp);
    }
    else if (bzla_node_bv_get_width(bzla, exp) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < exp->arity; i++)
      {
        if (bzla_bv_is_zero(s[i])) pos_x = pos_x == -1 ? i : -1;
      }
      if (pos_x == -1) pos_x = select_path_random(bzla, exp);
    }
    else if (opt == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* 1) all bits set in t must be set in both inputs, but
       * 2) all bits NOT set in t can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < exp->arity; i++)
      {
        tmp = bzla_bv_and(mm, t, s[i]);
        if (bzla_bv_compare(tmp, t)) pos_x = pos_x == -1 ? i : -1;
        bzla_bv_free(mm, tmp);
      }
    }
    if (pos_x == -1) pos_x = select_path_random(bzla, exp);
  }

  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_eq(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  pos_x = select_path_non_const(pi->exp);
  if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_ult(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  BzlaBitVector *ones, *t, **s;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const(pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      if (bzla_bv_is_one(t))
      {
        /* 1...1 < s[1] */
        if (!bzla_bv_compare(s[0], ones)) pos_x = 0;
        /* s[0] < 0 */
        if (bzla_bv_is_zero(s[1])) pos_x = pos_x == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, ones);
    }
    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }

  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_sll(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp, *t, **s;
  BzlaMemMgr *mm;

  pos_x = select_path_non_const(pi->exp);

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;
  bw = bzla_bv_get_width(t);
  assert(bzla_bv_get_width(s[0]) == bw);
  assert(bzla_bv_get_width(s[1]) == bw);

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (bw > 64)
      {
        bv_bw = bzla_bv_uint64_to_bv(mm, bw, bw);
        tmp   = bzla_bv_ugte(mm, s[1], bv_bw);
        if (bzla_bv_is_one(tmp) && !bzla_bv_is_zero(t))
        {
          bzla_bv_free(mm, bv_bw);
          bzla_bv_free(mm, tmp);
          pos_x = 1;
          goto DONE;
        }
        bzla_bv_free(mm, bv_bw);
        bzla_bv_free(mm, tmp);
        /* actual value is small enough to fit into 32 bit (max bit width
         * handled by Bitwuzla is INT32_MAX) */
        tmp   = bzla_bv_slice(mm, s[1], 32, 0);
        shift = bzla_bv_to_uint64(tmp);
        bzla_bv_free(mm, tmp);
      }
      else
      {
        shift = bzla_bv_to_uint64(s[1]);
      }
      /* if shift is greater than bit-width, result must be zero */
      if (!bzla_bv_is_zero(t) && shift >= bw)
      {
        pos_x = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of LSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(t, i))
          {
            pos_x = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(s[0], i) != bzla_bv_get_bit(t, j + i))
          {
            pos_x = pos_x == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }
DONE:
  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_srl(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp, *t, **s;
  BzlaMemMgr *mm;

  pos_x = select_path_non_const(pi->exp);

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;
  bw = bzla_bv_get_width(t);
  assert(bzla_bv_get_width(s[0]) == bw);
  assert(bzla_bv_get_width(s[1]) == bw);

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (bw > 64)
      {
        bv_bw = bzla_bv_uint64_to_bv(mm, bw, bw);
        tmp   = bzla_bv_ugte(mm, s[1], bv_bw);
        if (bzla_bv_is_one(tmp) && !bzla_bv_is_zero(t))
        {
          bzla_bv_free(mm, bv_bw);
          bzla_bv_free(mm, tmp);
          pos_x = 1;
          goto DONE;
        }
        bzla_bv_free(mm, bv_bw);
        bzla_bv_free(mm, tmp);
        /* actual value is small enough to fit into 32 bit (max bit width
         * handled by Bitwuzla is INT32_MAX) */
        tmp   = bzla_bv_slice(mm, s[1], 32, 0);
        shift = bzla_bv_to_uint64(tmp);
        bzla_bv_free(mm, tmp);
      }
      else
      {
        shift = bzla_bv_to_uint64(s[1]);
      }
      /* if shift is greater than bit-width, result must be zero */
      if (!bzla_bv_is_zero(t) && shift >= bw)
      {
        pos_x = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of MSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(t, bw - 1 - i))
          {
            pos_x = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(s[0], bw - 1 - i)
              != bzla_bv_get_bit(t, bw - 1 - (j + i)))
          {
            pos_x = pos_x == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }
DONE:
  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_mul(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  uint32_t ctz_bvmul;
  int32_t pos_x, lsb_s0, lsb_s1;
  bool iszero_s0, iszero_s1;
  BzlaBitVector *t, **s;

  pos_x = select_path_non_const(pi->exp);

  s = (BzlaBitVector **) pi->bv;
  t = (BzlaBitVector *) pi->target_value;

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      iszero_s0 = bzla_bv_is_zero(s[0]);
      iszero_s1 = bzla_bv_is_zero(s[1]);

      lsb_s0 = bzla_bv_get_bit(s[0], 0);
      lsb_s1 = bzla_bv_get_bit(s[1], 0);

      /* either s[0] or s[1] are 0 but t > 0 */
      if ((iszero_s0 || iszero_s1) && !bzla_bv_is_zero(t))
      {
        if (iszero_s0) pos_x = 0;
        if (iszero_s1) pos_x = pos_x == -1 ? 1 : -1;
      }
      /* t is odd but either s[0] or s[1] are even */
      else if (bzla_bv_get_bit(t, 0) && (!lsb_s0 || !lsb_s1))
      {
        if (!lsb_s0) pos_x = 0;
        if (!lsb_s1) pos_x = pos_x == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in t < number of 0-LSBs in s[0|1] */
      else
      {
        ctz_bvmul = bzla_bv_get_num_trailing_zeros(t);
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(s[0])) pos_x = 0;
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(s[1]))
          pos_x = pos_x == -1 ? 1 : -1;
      }
    }
    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }
  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_udiv(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x, cmp_udiv_max;
  BzlaBitVector *ones, *up, *lo, *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const(pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones         = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      cmp_udiv_max = bzla_bv_compare(t, ones);

      /* s[0] / s[1] = 1...1 -> choose x
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        pos_x = 1;
      else
      {
        /* 1...1 / x = 0 -> choose x */
        if (bzla_bv_is_zero(t) && !bzla_bv_compare(s[0], ones)) pos_x = 0;
        /* s[0] < t -> choose x */
        else if (bzla_bv_compare(s[0], t) < 0)
          pos_x = 0;
        else
        {
          up  = bzla_bv_udiv(mm, s[0], t);
          lo  = bzla_bv_inc(mm, t);
          tmp = bzla_bv_udiv(mm, s[0], lo);
          bzla_bv_free(mm, lo);
          lo = bzla_bv_inc(mm, tmp);

          if (bzla_bv_compare(lo, up) > 0) pos_x = 0;
          bzla_bv_free(mm, up);
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, tmp);
        }

        /* x / 0 != 1...1 -> choose x */
        if (bzla_bv_is_zero(s[1]) || bzla_bv_is_umulo(mm, s[1], t))
          pos_x = pos_x == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, ones);
    }
    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }

  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_urem(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  BzlaBitVector *ones, *sub, *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const(pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      sub  = bzla_bv_sub(mm, s[0], t);
      tmp  = bzla_bv_dec(mm, s[0]);

      /* t = 1...1 -> s[0] = 1...1 and s[1] = 0...0 */
      if (!bzla_bv_compare(t, ones))
      {
        if (!bzla_bv_is_zero(s[1])) pos_x = 1;
        if (bzla_bv_compare(s[0], ones)) pos_x = pos_x == -1 ? 0 : -1;
      }
      /* t > 0 and s[1] = 1 */
      else if (!bzla_bv_is_zero(t) && bzla_bv_is_one(s[1]))
      {
        pos_x = 1;
      }
      /* 0 < s[1] <= t */
      else if (!bzla_bv_is_zero(s[1]) && bzla_bv_compare(s[1], t) <= 0)
      {
        pos_x = pos_x == -1 ? 1 : -1;
      }
      /* s[0] < t or
       * s[0] > t and s[0] - t <= t or
       *                 and s[0] - 1 = t */
      else if (bzla_bv_compare(s[0], t) < 0
               || (bzla_bv_compare(s[0], t) > 0
                   && (bzla_bv_compare(sub, t) <= 0
                       || !bzla_bv_compare(tmp, t))))
      {
        pos_x = 0;
      }

      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, ones);
      bzla_bv_free(mm, sub);
    }

    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }

  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_concat(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  int32_t pos_x;
  uint32_t bw_t;
  BzlaBitVector *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  s     = (BzlaBitVector **) pi->bv;
  t     = (BzlaBitVector *) pi->target_value;
  pos_x = select_path_non_const(pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* s[0] o s[1] = t
       * -> s[0] resp. s[1] must match with t */
      bw_t = bzla_bv_get_width(t);
      tmp  = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bzla_bv_get_width(s[0]));
      if (bzla_bv_compare(tmp, s[0])) pos_x = 0;
      bzla_bv_free(mm, tmp);
      tmp = bzla_bv_slice(mm, t, bzla_bv_get_width(s[1]) - 1, 0);
      if (bzla_bv_compare(tmp, s[1])) pos_x = pos_x == -1 ? 1 : -1;
      bzla_bv_free(mm, tmp);
    }

    if (pos_x == -1) pos_x = select_path_random(bzla, pi->exp);
  }

  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_slice(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  assert(!bzla_node_is_bv_const(pi->exp->e[0]));

  pi->pos_x = 0;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  return 0;
}

static int32_t
select_path_cond(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);

  bool is_const_e1, is_const_e2;
  int32_t pos_x, *delta;
  uint32_t *prob, *nflips_cond;
  BzlaNode *exp;
  BzlaBitVector *s0;

  exp = (BzlaNode *) pi->exp;
  s0  = (BzlaBitVector *) pi->bv[0];

  if (bzla_node_is_bv_const(exp->e[0]))
  {
    /* pick enabled branch */
    assert(
        (exp->e[0] == bzla->true_exp && !bzla_node_is_bv_const(exp->e[1]))
        || (exp->e[0] != bzla->true_exp && !bzla_node_is_bv_const(exp->e[2])));
    pos_x = exp->e[0] == bzla->true_exp ? 1 : 2;
  }
  else
  {
    is_const_e1 = bzla_node_is_bv_const(exp->e[1]);
    is_const_e2 = bzla_node_is_bv_const(exp->e[2]);
    if (is_const_e1 && is_const_e2)
    {
      pos_x = 0;
    }
    else if ((is_const_e1 && bzla_bv_is_true(s0))
             || (is_const_e2 && bzla_bv_is_false(s0)))
    {
      /* enabled branch is const
       *
       * -> flip condition with probability BZLA_OPT_PROP_FLIP_COND_CONST_PROB,
       *    which is dynamically updated (depending on the number times this
       *    case has already bin encountered)
       *
       * -> else select other non-const branch
       */
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        prob        = &BZLA_PROP_SOLVER(bzla)->flip_cond_const_prob;
        delta       = &BZLA_PROP_SOLVER(bzla)->flip_cond_const_prob_delta;
        nflips_cond = &BZLA_PROP_SOLVER(bzla)->nflip_cond_const;
      }
      else
      {
        assert(bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
        prob        = &BZLA_SLS_SOLVER(bzla)->prop_flip_cond_const_prob;
        delta       = &BZLA_SLS_SOLVER(bzla)->prop_flip_cond_const_prob_delta;
        nflips_cond = &BZLA_SLS_SOLVER(bzla)->prop_nflip_cond_const;
      }
      if (bzla_rng_pick_with_prob(&bzla->rng, *prob))
      {
        pos_x = 0;
        *nflips_cond += 1;
        if (*nflips_cond
            == bzla_opt_get(bzla, BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          *nflips_cond = 0;
          *delta       = *prob == 0 ? 100 : (*prob == 1000 ? -100 : *delta);
          *prob += *delta;
        }
      }
      else
      {
        pos_x = is_const_e1 ? 2 : 1;
      }
    }
    else
    {
      /* enabled branch is not const, condition not const */
      if (bzla_rng_pick_with_prob(
              &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND)))
      {
        pos_x = 0;
      }
      else
      {
        pos_x = bzla_bv_is_true(s0) ? 1 : 2;
      }
    }
  }

  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log(bzla, pi);
#endif
  assert(!bzla_node_is_bv_const(pi->exp->e[pos_x]));
  return pos_x;
}

/* ========================================================================== */
/* Consistent value computation                                               */
/* ========================================================================== */

static void
record_cons_stats(Bzla *bzla, uint32_t *stats)
{
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    *stats += 1;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
}

#ifndef NDEBUG
static void
check_cons_dbg(Bzla *bzla, BzlaPropInfo *pi, bool same_bw)
{
  assert(bzla);
  assert(pi);
  assert(bzla_node_is_regular(pi->exp));
  assert(!same_bw
         || bzla_bv_get_width(pi->bv[1 - pi->pos_x])
                == bzla_bv_get_width(pi->target_value));
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 1);
  assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));
}
#endif

BzlaBitVector *
bzla_proputils_cons_add(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_add);
  return bzla_bv_new_random(
      bzla->mm, &bzla->rng, bzla_bv_get_width(pi->target_value));
}

BzlaBitVector *
bzla_proputils_cons_and(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t i, bw;
  BzlaBitVector *res;
  BzlaUIntStack dcbits;
  bool b;
  const BzlaBitVector *t;

  t = pi->target_value;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_and);

  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(bzla->mm, dcbits);

  res = bzla_bv_copy(bzla->mm, pi->bv[pi->pos_x]);

  /* s & res = t
   * -> all bits set in t must be set in res
   * -> all bits not set in t are chosen to be set randomly */
  for (i = 0, bw = bzla_bv_get_width(t); i < bw; i++)
  {
    if (bzla_bv_get_bit(t, i))
      bzla_bv_set_bit(res, i, 1);
    else if (b)
      BZLA_PUSH_STACK(dcbits, i);
    else
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
  }

  if (b && BZLA_COUNT_STACK(dcbits))
    bzla_bv_flip_bit(
        res,
        BZLA_PEEK_STACK(
            dcbits,
            bzla_rng_pick_rand(&bzla->rng, 0, BZLA_COUNT_STACK(dcbits) - 1)));

  BZLA_RELEASE_STACK(dcbits);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_eq(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif

  BzlaBitVector *res;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_eq);

  if (bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_EQ_FLIP)))
  {
    res = bzla_bv_copy(bzla->mm, pi->bv[pi->pos_x]);
    bzla_bv_flip_bit(
        res, bzla_rng_pick_rand(&bzla->rng, 0, bzla_bv_get_width(res) - 1));
  }
  else
  {
    res = bzla_bv_new_random(
        bzla->mm, &bzla->rng, bzla_bv_get_width(pi->bv[1 - pi->pos_x]));
  }
  return res;
}

static BzlaBitVector *
cons_ult_aux(Bzla *bzla, BzlaPropInfo *pi, bool with_const_bits)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif
  bool isult;
  uint32_t bw;
  BzlaBitVector *ones, *zero, *tmp, *res;
  BzlaMemMgr *mm;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaBvDomainGenerator gen;
  int32_t pos_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_ult);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = with_const_bits ? pi->bvd[pi->pos_x] : 0;
  s     = pi->bv[1 - pi->pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(s);
  isult = !bzla_bv_is_zero(t);

  if (pos_x == 1 && isult)
  {
    /* s < res = 1  ->  res > 0 */
    if (x)
    {
      if (bzla_bvdomain_is_fixed(mm, x))
      {
        if (bzla_bv_is_zero(x->lo))
        {
          /* non-recoverable conflict */
          return NULL;
        }
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_one(mm, bw);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, ones);
        if (!bzla_bvdomain_gen_has_next(&gen))
        {
          /* non-recoverable conflict */
          bzla_bvdomain_gen_delete(&gen);
          bzla_bv_free(mm, tmp);
          bzla_bv_free(mm, ones);
          return NULL;
        }
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bvdomain_gen_delete(&gen);
        bzla_bv_free(mm, tmp);
        bzla_bv_free(mm, ones);
      }
    }
    else
    {
      ones = bzla_bv_ones(mm, bw);
      tmp  = bzla_bv_one(mm, bw);
      res  = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, ones);
    }
  }
  else if (pos_x == 0 && isult)
  {
    /* res < s = 1  ->  0 <= res < 1...1 */
    if (x)
    {
      if (bzla_bvdomain_is_fixed(mm, x))
      {
        if (bzla_bv_is_ones(x->lo))
        {
          /* non-recoverable conflict */
          return NULL;
        }
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        zero = bzla_bv_zero(mm, bw);
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_dec(mm, ones);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, zero, tmp);
        if (!bzla_bvdomain_gen_has_next(&gen))
        {
          /* non-recoverable conflict */
          bzla_bvdomain_gen_delete(&gen);
          bzla_bv_free(mm, tmp);
          bzla_bv_free(mm, ones);
          bzla_bv_free(mm, zero);
          return NULL;
        }
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bv_free(mm, tmp);
        bzla_bv_free(mm, ones);
        bzla_bv_free(mm, zero);
        bzla_bvdomain_gen_delete(&gen);
      }
    }
    else
    {
      zero = bzla_bv_zero(mm, bw);
      ones = bzla_bv_ones(mm, bw);
      tmp  = bzla_bv_dec(mm, ones);
      res  = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, ones);
      bzla_bv_free(mm, zero);
    }
  }
  else if (x && bzla_bvdomain_is_fixed(mm, x))
  {
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    res = bzla_bv_new_random(mm, &bzla->rng, bw);
    if (x)
    {
      set_const_bits(mm, x, &res);
    }
  }

  return res;
}

BzlaBitVector *
bzla_proputils_cons_ult(Bzla *bzla, BzlaPropInfo *pi)
{
  return cons_ult_aux(bzla, pi, false);
}

BzlaBitVector *
bzla_proputils_cons_sll(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t bw, ctz_t, shift, max;
  BzlaBitVector *res, *bv_shift, *left, *right;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_sll);

  mm    = bzla->mm;
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  if (bw >= 64 && ctz_t == bw)
  {
    shift    = bw;
    bv_shift = bzla_bv_new_random(mm, &bzla->rng, bw);
  }
  else
  {
    max      = ctz_t < bw ? ctz_t : ((1u << bw) - 1);
    shift    = bzla_rng_pick_rand(&bzla->rng, 0, max);
    bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);
  }
  if (shift >= bw) shift = bw;

  if (pi->pos_x)
  {
    res = bv_shift;
  }
  else
  {
    if (shift == bw)
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      if (shift)
      {
        left  = bzla_bv_new_random(mm, &bzla->rng, shift);
        right = bzla_bv_slice(mm, t, bw - 1, shift);
        res   = bzla_bv_concat(mm, left, right);
        bzla_bv_free(mm, left);
        bzla_bv_free(mm, right);
      }
      else
      {
        res = bzla_bv_copy(mm, t);
      }
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_srl(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t bw, clz_t, shift, max;
  BzlaBitVector *res, *bv_shift, *left, *right;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_srl);

  mm    = bzla->mm;
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  if (bw >= 64 && clz_t == bw)
  {
    shift    = bw;
    bv_shift = bzla_bv_new_random(mm, &bzla->rng, bw);
  }
  else
  {
    max      = clz_t < bw ? clz_t : ((1u << bw) - 1);
    shift    = bzla_rng_pick_rand(&bzla->rng, 0, max);
    bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);
  }
  if (shift >= bw) shift = bw;

  if (pi->pos_x)
  {
    res = bv_shift;
  }
  else
  {
    if (shift == bw)
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      if (shift)
      {
        right = bzla_bv_new_random(mm, &bzla->rng, shift);
        left  = bzla_bv_slice(mm, t, bw - 1 - shift, 0);
        res   = bzla_bv_concat(mm, left, right);
        bzla_bv_free(mm, left);
        bzla_bv_free(mm, right);
      }
      else
      {
        res = bzla_bv_copy(mm, t);
      }
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_mul(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t r, bw, ctz_res, ctz_t;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_mul);

  mm  = bzla->mm;
  t   = pi->target_value;
  bw  = bzla_bv_get_width(t);
  res = bzla_bv_new_random(mm, &bzla->rng, bw);
  if (!bzla_bv_is_zero(t))
  {
    if (bzla_bv_is_zero(res))
    {
      bzla_bv_free(mm, res);
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    /* t odd -> choose odd value > 0 */
    if (bzla_bv_get_bit(t, 0))
    {
      if (!bzla_bv_get_bit(res, 0)) bzla_bv_set_bit(res, 0, 1);
    }
    /* t even -> choose random value > 0
     *               with number of 0-LSBs in res less or equal
     *               than in t */
    else
    {
      ctz_t = bzla_bv_get_num_trailing_zeros(t);
      /* choose res as 2^n with ctz(t) >= ctz(res) with prob 0.1 */
      if (bzla_rng_pick_with_prob(&bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        res = bzla_bv_zero(mm, bw);
        bzla_bv_set_bit(res, bzla_rng_pick_rand(&bzla->rng, 0, ctz_t - 1), 1);
      }
      /* choose res as t / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (bzla_rng_pick_with_prob(&bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        if ((r = bzla_rng_pick_rand(&bzla->rng, 0, ctz_t)))
        {
          tmp = bzla_bv_slice(mm, t, bw - 1, r);
          res = bzla_bv_uext(mm, tmp, r);
          bzla_bv_free(mm, tmp);
        }
        else
        {
          res = bzla_bv_copy(mm, t);
        }
      }
      /* choose random value with ctz(t) >= ctz(res) with prob 0.8 */
      else
      {
        ctz_res = bzla_bv_get_num_trailing_zeros(res);
        if (ctz_res > ctz_t)
          bzla_bv_set_bit(res, bzla_rng_pick_rand(&bzla->rng, 0, ctz_t - 1), 1);
      }
    }
  }

  return res;
}

BzlaBitVector *
bzla_proputils_cons_udiv(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t bw;
  BzlaBitVector *res, *tmp, *y, *offset, *max, *zero, *one, *ones;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  mm   = bzla->mm;
  t    = pi->target_value;
  bw   = bzla_bv_get_width(t);
  zero = bzla_bv_zero(mm, bw);
  one  = bzla_bv_one(mm, bw);
  ones = bzla_bv_ones(mm, bw);

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_udiv);

  if (pi->pos_x)
  {
    /* -> t = 1...1 then res = 0 or res = 1
     * -> else choose res s.t. res * t does not overflow */
    if (!bzla_bv_compare(t, ones))
      res = bzla_bv_uint64_to_bv(mm, bzla_rng_pick_rand(&bzla->rng, 0, 1), bw);
    else
    {
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, ones);
      while (bzla_bv_is_umulo(mm, res, t))
      {
        tmp = bzla_bv_sub(mm, res, one);
        bzla_bv_free(mm, res);
        res = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
        bzla_bv_free(mm, tmp);
      }
    }
  }
  else
  {
    if (bzla_bv_is_zero(t))
    {
      /* t = 0: res < 1...1 */
      tmp = bzla_bv_dec(mm, ones);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
    else if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1: choose random res */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /* Compute x = y * t + offset with
       *   y \in [1, ones / t]
       * and
       *   offset \in [0, min(y - 1, ones - y * t)].
       */
      max = bzla_bv_udiv(mm, ones, t);
      y   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, max);
      bzla_bv_free(mm, max);

      assert(!bzla_bv_is_umulo(mm, y, t));
      res = bzla_bv_mul(mm, y, t);

      tmp = bzla_bv_sub(mm, ones, res);
      max = bzla_bv_dec(mm, y);
      bzla_bv_free(mm, y);

      /* Make sure that adding the offset to (y * t) does not overflow. The
       * maximum value of the offset is the minimum of (y - 1, ones - (y * t)).
       */
      if (bzla_bv_compare(tmp, max) < 0)
      {
        bzla_bv_free(mm, max);
        max = tmp;
      }
      else
      {
        bzla_bv_free(mm, tmp);
      }
      /* Compute offset for adding to res. */
      offset = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, max);
      bzla_bv_free(mm, max);

      assert(!bzla_bv_is_uaddo(mm, res, offset));
      tmp = bzla_bv_add(mm, res, offset);
      bzla_bv_free(mm, res);
      bzla_bv_free(mm, offset);
      res = tmp;
    }
  }

  bzla_bv_free(mm, one);
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, ones);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_urem(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t bw;
  BzlaBitVector *res, *ones, *tmp, *max, *min;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_urem);

  mm = bzla->mm;
  t  = pi->target_value;
  bw = bzla_bv_get_width(t);

  if (pi->pos_x)
  {
    if (bzla_bv_is_ones(t))
    {
      /* t = 1...1  ->  res = 0 */
      res = bzla_bv_zero(mm, bw);
    }
    else if (bzla_rng_pick_with_prob(&bzla->rng, 100))
    {
      /* s % 0 = s = t */
      res = bzla_bv_zero(mm, bw);
    }
    else
    {
      /* else res > t */
      ones = bzla_bv_ones(mm, bw);
      tmp  = bzla_bv_inc(mm, t);
      res  = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, ones);
    }
  }
  else
  {
    if (bzla_bv_is_ones(t))
    {
      /* t = 1...1  ->  res = 1...1 */
      res = bzla_bv_ones(mm, bw);
    }
    else if (bzla_rng_pick_with_prob(&bzla->rng, 100))
    {
      /* x % 0 = x = t */
      res = bzla_bv_copy(mm, t);
    }
    else
    {
      /* else res >= t:
       * pick s > t such that x = s + t does not overflow -> t < s < ones - t */
      ones = bzla_bv_ones(mm, bw);
      max  = bzla_bv_sub(mm, ones, t);
      min  = bzla_bv_inc(mm, t);
      if (bzla_bv_compare(min, max) > 0)
      {
        res = bzla_bv_copy(mm, t);
      }
      else
      {
        tmp = bzla_bv_new_random_range(mm, &bzla->rng, bw, min, max);
        res = bzla_bv_add(mm, tmp, t);
        bzla_bv_free(mm, tmp);
      }
      bzla_bv_free(mm, min);
      bzla_bv_free(mm, max);
      bzla_bv_free(mm, ones);
    }
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_concat(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif
  int32_t bw_t, bw_s;
  BzlaBitVector *res;
  const BzlaBitVector *s, *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_concat);

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);

  res = pi->pos_x ? bzla_bv_slice(bzla->mm, t, bw_t - bw_s - 1, 0)
                  : bzla_bv_slice(bzla->mm, t, bw_t - 1, bw_s);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_slice(Bzla *bzla, BzlaPropInfo *pi)
{
  return bzla_proputils_inv_slice(bzla, pi);
}

BzlaBitVector *
bzla_proputils_cons_cond(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  assert(bzla_node_is_regular(pi->exp));
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 2);
  assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));

  BzlaBitVector *res;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_cond);

  mm = bzla->mm;

  if (pi->pos_x == 0)
  {
    res = bzla_rng_flip_coin(&bzla->rng) ? bzla_bv_one(mm, 1)
                                         : bzla_bv_zero(mm, 1);
  }
  else if ((pi->pos_x == 1 && bzla_bv_is_zero(pi->bv[0]))
           || (pi->pos_x == 2 && bzla_bv_is_one(pi->bv[0])))
  {
    /* return current assignment for disabled branch */
    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
  }
  else
  {
    res = bzla_bv_copy(mm, pi->target_value);
  }
  return res;
}

/* ========================================================================== */
/* Consistent value computation with respect to const bits                    */
/* ========================================================================== */

BzlaBitVector *
bzla_proputils_cons_add_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif

  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_add);

  mm = bzla->mm;
  x  = pi->bvd[pi->pos_x];
  if (bzla_bvdomain_is_fixed(mm, x)) return bzla_bv_copy(mm, x->lo);
  res = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(pi->target_value));
  set_const_bits(mm, x, &res);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_and_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_and);

  mm = bzla->mm;
  x  = pi->bvd[pi->pos_x];
  t  = pi->target_value;

  if (bzla_bvdomain_is_fixed(mm, x)) return bzla_bv_copy(mm, x->lo);

  for (uint32_t i = 0, bw = bzla_bv_get_width(t); i < bw; i++)
  {
    if (bzla_bv_get_bit(t, i) && bzla_bvdomain_is_fixed_bit_false(x, i))
    {
      /* non-recoverable conflict */
      return NULL;
    }
  }
  res = bzla_proputils_cons_and(bzla, pi);
  set_const_bits(mm, x, &res);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_eq_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif
  BzlaBitVector *res;
  const BzlaBvDomain *x;

  x = pi->bvd[pi->pos_x];
  if (bzla_bvdomain_is_fixed(bzla->mm, x))
  {
    record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_eq);
    return bzla_bv_copy(bzla->mm, x->lo);
  }
  res = bzla_proputils_cons_eq(bzla, pi);
  set_const_bits(bzla->mm, x, &res);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_ult_const(Bzla *bzla, BzlaPropInfo *pi)
{
  return cons_ult_aux(bzla, pi, true);
}

BzlaBitVector *
bzla_proputils_cons_sll_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  int32_t pos_x;
  uint32_t i, r, bw, bw_r, ctz_t, shift, max;
  BzlaBitVector *res, *left, *right, *zero, *tmp, *t_slice;
  BzlaBvDomain *x_slice;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_sll);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  if (pos_x)
  {
    if (bw >= 64 && ctz_t == bw)
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
      if (pos_x)
      {
        set_const_bits(mm, x, &res);
      }
    }
    else
    {
      max = ctz_t < bw ? ctz_t : ((1u << bw) - 1);
      if (pos_x)
      {
        tmp  = bzla_bv_uint64_to_bv(mm, max, bw);
        zero = bzla_bv_zero(mm, bw);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, zero, tmp);
        if (!bzla_bvdomain_gen_has_next(&gen))
        {
          /* non-recoverable conflict */
          bzla_bv_free(mm, zero);
          bzla_bv_free(mm, tmp);
          bzla_bvdomain_gen_delete(&gen);
          return NULL;
        }
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bv_free(mm, zero);
        bzla_bv_free(mm, tmp);
        bzla_bvdomain_gen_delete(&gen);
      }
      else
      {
        shift = bzla_rng_pick_rand(&bzla->rng, 0, max);
        res   = bzla_bv_uint64_to_bv(mm, shift, bw);
      }
    }
  }
  else if (bzla_bv_is_zero(t))
  {
    bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    BzlaBitVectorPtrStack stack;
    BZLA_INIT_STACK(mm, stack);

    for (i = ctz_t; i != UINT32_MAX; i--)
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
    if (BZLA_EMPTY_STACK(stack))
    {
      BZLA_RELEASE_STACK(stack);
      return NULL;
    }
    r     = bzla_rng_pick_rand(&bzla->rng, 0, BZLA_COUNT_STACK(stack) - 1);
    right = BZLA_PEEK_STACK(stack, r);
    bw_r  = bzla_bv_get_width(right);
    if (bw == bw_r)
    {
      res = bzla_bv_copy(mm, right);
    }
    else
    {
      bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
      tmp  = bzla_bvdomain_gen_random(&gen);
      left = bzla_bv_slice(mm, tmp, bw - 1, bw_r);
      bzla_bvdomain_gen_delete(&gen);
      res = bzla_bv_concat(mm, left, right);
      bzla_bv_free(mm, left);
    }

    while (!BZLA_EMPTY_STACK(stack))
    {
      bzla_bv_free(mm, BZLA_POP_STACK(stack));
    }
    BZLA_RELEASE_STACK(stack);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_srl_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  int32_t pos_x;
  uint32_t i, r, bw, bw_l, clz_t, shift, max;
  BzlaBitVector *res, *left, *right, *zero, *tmp, *t_slice;
  BzlaBvDomain *x_slice;
  const BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_srl);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  if (pos_x)
  {
    if (bw >= 64 && clz_t == bw)
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
      if (pos_x)
      {
        set_const_bits(mm, x, &res);
      }
    }
    else
    {
      max = clz_t < bw ? clz_t : ((1u << bw) - 1);
      if (pos_x)
      {
        tmp  = bzla_bv_uint64_to_bv(mm, max, bw);
        zero = bzla_bv_zero(mm, bw);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, zero, tmp);
        if (!bzla_bvdomain_gen_has_next(&gen))
        {
          /* non-recoverable conflict */
          bzla_bv_free(mm, zero);
          bzla_bv_free(mm, tmp);
          bzla_bvdomain_gen_delete(&gen);
          return NULL;
        }
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bv_free(mm, zero);
        bzla_bv_free(mm, tmp);
        bzla_bvdomain_gen_delete(&gen);
      }
      else
      {
        shift = bzla_rng_pick_rand(&bzla->rng, 0, max);
        res   = bzla_bv_uint64_to_bv(mm, shift, bw);
      }
    }
  }
  else if (bzla_bv_is_zero(t))
  {
    bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    BzlaBitVectorPtrStack stack;
    BZLA_INIT_STACK(mm, stack);

    for (i = clz_t; i != UINT32_MAX; i--)
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
    if (BZLA_EMPTY_STACK(stack))
    {
      BZLA_RELEASE_STACK(stack);
      return NULL;
    }
    r    = bzla_rng_pick_rand(&bzla->rng, 0, BZLA_COUNT_STACK(stack) - 1);
    left = BZLA_PEEK_STACK(stack, r);
    bw_l = bzla_bv_get_width(left);
    if (bw == bw_l)
    {
      res = bzla_bv_copy(mm, left);
    }
    else
    {
      bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
      tmp   = bzla_bvdomain_gen_random(&gen);
      right = bzla_bv_slice(mm, tmp, bw - 1 - bw_l, 0);
      bzla_bvdomain_gen_delete(&gen);
      res = bzla_bv_concat(mm, left, right);
      bzla_bv_free(mm, right);
    }

    while (!BZLA_EMPTY_STACK(stack))
    {
      bzla_bv_free(mm, BZLA_POP_STACK(stack));
    }
    BZLA_RELEASE_STACK(stack);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_mul_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  bool is_fixed, ctz_ok;
  uint32_t i, bw, ctz_t;
  BzlaBitVector *res, *one;
  const BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  mm = bzla->mm;
  t  = pi->target_value;
  x  = pi->bvd[pi->pos_x];
  bw = bzla_bv_get_width(t);

  res = bzla_proputils_cons_mul(bzla, pi);

  if (!bzla_bvdomain_check_fixed_bits(mm, x, res))
  {
    bzla_bv_free(mm, res);
    is_fixed = bzla_bvdomain_is_fixed(mm, x);

    if (!bzla_bv_is_zero(t))
    {
      if (is_fixed && bzla_bv_is_zero(x->lo))
      {
        /* non-recoverable conflict */
        return NULL;
      }
      one = bzla_bv_one(mm, bw);
      bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, one, 0);
      bzla_bv_free(mm, one);
    }
    else
    {
      bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
    }

    if (bzla_bv_get_bit(t, 0))
    {
      /* t odd, res must be odd */
      if (bzla_bvdomain_is_fixed_bit_false(x, 0))
      {
        /* non-recoverable conflict */
        bzla_bvdomain_gen_delete(&gen);
        return NULL;
      }
      if (is_fixed)
      {
        assert(bzla_bvdomain_is_fixed_bit_true(x, 0));
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        if (!bzla_bvdomain_gen_has_next(&gen))
        {
          /* non-recoverable conflict */
          bzla_bvdomain_gen_delete(&gen);
          return NULL;
        }
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bv_set_bit(res, 0, 1);
      }
    }
    else
    {
      /* t even, res can be either with ctz(t) >= ctz(res) */
      if (is_fixed)
      {
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      }

      if (!bzla_bv_is_zero(t))
      {
        ctz_t = bzla_bv_get_num_trailing_zeros(t);
        for (i = 0, ctz_ok = false; i < ctz_t; i++)
        {
          if (!bzla_bvdomain_is_fixed_bit_false(x, i))
          {
            ctz_ok = true;
            break;
          }
        }
        if (!ctz_ok && bzla_bvdomain_is_fixed_bit_false(x, ctz_t))
        {
          /* non-recoverable conflict */
          bzla_bvdomain_gen_delete(&gen);
          bzla_bv_free(mm, res);
          return NULL;
        }
        do
        {
          i = bzla_rng_pick_rand(&bzla->rng, 0, ctz_t);
        } while (bzla_bvdomain_is_fixed_bit_false(x, i));
        bzla_bv_set_bit(res, i, 1);
      }
    }
    bzla_bvdomain_gen_delete(&gen);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_udiv_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  int32_t pos_x;
  uint32_t bw;
  bool check_zero, check_one, check_t, force_t;
  BzlaBitVector *res, *min, *max, *tmp, *zero, *one, *ones;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_udiv);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);

  zero = bzla_bv_zero(mm, bw);
  one  = bzla_bv_one(mm, bw);
  ones = bzla_bv_ones(mm, bw);

  if (pos_x)
  {
    if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1 then res = 0 or res = 1 */

      check_zero = bzla_bvdomain_check_fixed_bits(mm, x, zero);
      check_one  = bzla_bvdomain_check_fixed_bits(mm, x, one);

      if (!check_zero)
      {
        if (!check_one)
        {
          /* non-recoverable conflict */
          res = NULL;
        }
        else
        {
          res = bzla_bv_one(mm, bw);
        }
      }
      else if (!check_one)
      {
        res = bzla_bv_zero(mm, bw);
      }
      else
      {
        res = bzla_rng_flip_coin(&bzla->rng) ? bzla_bv_zero(mm, bw)
                                             : bzla_bv_one(mm, bw);
      }
    }
    else
    {
      /* choose res s.t. res * t does not overflow */
      if (bzla_bv_is_umulo(mm, x->lo, t))
      {
        /* non-recoverable conflict */
        res = NULL;
      }
      else if (bzla_bvdomain_is_fixed(mm, x))
      {
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, one, 0);
        res = bzla_bvdomain_gen_random(&gen);
        while (bzla_bv_is_umulo(mm, res, t))
        {
          max = bzla_bv_dec(mm, res);
          bzla_bvdomain_gen_delete(&gen);
          bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, one, max);
          if (!bzla_bvdomain_gen_has_next(&gen))
          {
            /* non-recoverable conflict */
            res = NULL;
            bzla_bv_free(mm, max);
            break;
          }
          res = bzla_bvdomain_gen_random(&gen);
          bzla_bv_free(mm, max);
        }
        if (res) res = bzla_bv_copy(mm, res);
        bzla_bvdomain_gen_delete(&gen);
      }
    }
  }
  else
  {
    if (bzla_bv_is_zero(t))
    {
      /* t = 0: random res < 1...1 */
      if (bzla_bvdomain_is_fixed(mm, x))
      {
        if (bzla_bv_is_ones(x->lo))
        {
          /* non-recoverable conflict */
          res = NULL;
        }
        else
        {
          res = bzla_bv_copy(mm, x->lo);
        }
      }
      else
      {
        max = bzla_bv_dec(mm, ones);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, 0, max);
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bv_free(mm, max);
        bzla_bvdomain_gen_delete(&gen);
      }
    }
    else if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1: choose random res */
      bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bvdomain_gen_delete(&gen);
    }
    else if (!bzla_bv_compare(t, ones) || !bzla_bv_compare(t, one))
    {
      /* t = 1: choose random res > 0 */
      bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, one, 0);
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bvdomain_gen_delete(&gen);
    }
    else
    {
      /* simplest solution:
       *   x = t
       *
       * remaining solutions:
       *   min <= x <= ones with min = x->lo / t * t if x->lo / t > 1 and
       *                         min = 2 * t otherwise */

      if (bzla_bv_compare(x->hi, t) < 0)
      {
        /* non-recoverable conflict */
        res = NULL;
      }
      else
      {
        /* pick x = t with prob=10% if possible */
        check_t = bzla_bvdomain_check_fixed_bits(mm, x, t);
        if (check_t && bzla_rng_pick_with_prob(&bzla->rng, 100))
        {
          res = bzla_bv_copy(mm, t);
        }
        else
        {
          force_t = false;
          tmp     = bzla_bv_udiv(mm, x->lo, t);
          if (bzla_bv_compare(tmp, one) <= 0)
          {
            if (bzla_bv_is_uaddo(mm, t, t))
            {
              /* x = t the only solution */
              force_t = true;
              min     = NULL;
            }
            else
            {
              min = bzla_bv_add(mm, t, t);
            }
          }
          else
          {
            min = bzla_bv_mul(mm, tmp, t);
          }
          bzla_bv_free(mm, tmp);
          if (force_t)
          {
            if (!check_t)
            {
              /* non-recoverable conflict
               * x = t the only solution but not possible */
              res = NULL;
            }
            else
            {
              res = bzla_bv_copy(mm, t);
            }
          }
          else
          {
            assert(min);
            bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, min, ones);
            if (!bzla_bvdomain_gen_has_next(&gen))
            {
              if (!check_t)
              {
                /* non-recoverable conflict */
                res = NULL;
              }
              else
              {
                res = bzla_bv_copy(mm, t);
              }
            }
            else
            {
              res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
            }
            bzla_bvdomain_gen_delete(&gen);
          }
          if (min) bzla_bv_free(mm, min);
        }
      }
    }
  }
  bzla_bv_free(mm, one);
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, ones);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_urem_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  int32_t pos_x;
  uint32_t bw;
  bool check_t, check_zero;
  BzlaBitVector *res, *zero, *ones, *tmp, *max, *min;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_urem);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);
  zero  = bzla_bv_zero(mm, bw);
  ones  = bzla_bv_ones(mm, bw);

  if (pos_x)
  {
    check_zero = bzla_bvdomain_check_fixed_bits(mm, x, zero);
    if (check_zero && bzla_rng_pick_with_prob(&bzla->rng, 100))
    {
      res = bzla_bv_copy(mm, zero);
    }
    else
    {
      if (!bzla_bv_compare(t, ones))
      {
        /* t = 1...1  ->  res = 0 */
        if (!bzla_bvdomain_check_fixed_bits(mm, x, zero))
        {
          /* non-recoverable conflict*/
          res = NULL;
        }
        else
        {
          res = bzla_bv_copy(mm, zero);
        }
      }
      else
      {
        /* else res > t */
        tmp = bzla_bv_inc(mm, t);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, 0);
        if (!bzla_bvdomain_gen_has_next(&gen))
        {
          if (!check_zero)
          {
            /* non-recoverable conflict*/
            res = NULL;
          }
          else
          {
            res = bzla_bv_copy(mm, zero);
          }
        }
        else
        {
          res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        }
        bzla_bv_free(mm, tmp);
        bzla_bvdomain_gen_delete(&gen);
      }
    }
  }
  else
  {
    if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1  ->  res = 1...1 */
      if (!bzla_bvdomain_check_fixed_bits(mm, x, ones))
      {
        /* non-recoverable conflict*/
        res = NULL;
      }
      else
      {
        res = bzla_bv_copy(mm, ones);
      }
    }
    else
    {
      /* else x >= t:
       * pick s > t such that x = s + t does not overflow -> t < s < ones - t
       * -> 2*t + 1 <= x <= ones */

      max = bzla_bv_sub(mm, ones, t);
      min = bzla_bv_inc(mm, t);
      if (bzla_bv_compare(min, max) > 0)
      {
        if (!bzla_bvdomain_check_fixed_bits(mm, x, t))
        {
          /* non-recoverable conflict*/
          res = NULL;
        }
        else
        {
          res = bzla_bv_copy(mm, t);
        }
      }
      else
      {
        check_t = bzla_bvdomain_check_fixed_bits(mm, x, t);
        if (check_t && bzla_rng_pick_with_prob(&bzla->rng, 100))
        {
          res = bzla_bv_copy(mm, t);
        }
        else
        {
          assert(!bzla_bv_is_uaddo(mm, min, t));
          tmp = bzla_bv_add(mm, min, t);
          bzla_bv_free(mm, min);
          min = tmp;
          bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, min, ones);
          if (!bzla_bvdomain_gen_has_next(&gen))
          {
            if (!check_t)
            {
              /* non-recoverable conflict*/
              res = NULL;
            }
            else
            {
              res = bzla_bv_copy(mm, t);
            }
          }
          else
          {
            res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
          }
          bzla_bvdomain_gen_delete(&gen);
        }
      }
      bzla_bv_free(mm, min);
      bzla_bv_free(mm, max);
    }
  }

  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, ones);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_concat_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif
  int32_t pos_x, bw_t, bw_s, upper, lower;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_concat);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw_t  = bzla_bv_get_width(t);
  bw_s  = bzla_bv_get_width(s);

  if (pos_x == 1)
  {
    upper = bw_t - bw_s - 1;
    lower = 0;
  }
  else
  {
    upper = bw_t - 1;
    lower = bw_s;
  }

  res = bzla_bv_slice(mm, t, upper, lower);

  if (!bzla_bvdomain_check_fixed_bits(mm, x, res))
  {
    /* non-recoverable conflict */
    bzla_bv_free(mm, res);
    res = NULL;
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_slice_const(Bzla *bzla, BzlaPropInfo *pi)
{
  if (!bzla_is_inv_slice_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }
  return bzla_proputils_inv_slice_const(bzla, pi);
}

BzlaBitVector *
bzla_proputils_cons_cond_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  assert(bzla_node_is_regular(pi->exp));
  assert(!pi->pos_x || bzla_bv_get_width(pi->bv[0]) == 1);
  assert(pi->pos_x
         || bzla_bv_get_width(pi->bv[1]) == bzla_bv_get_width(pi->bv[2]));
  assert(pi->pos_x
         || bzla_bv_get_width(pi->bv[2])
                == bzla_bv_get_width(pi->target_value));
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 2);
  assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));

  int32_t pos_x;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_cond);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  if ((pi->pos_x == 1 && bzla_bv_is_zero(pi->bv[0]))
      || (pi->pos_x == 2 && bzla_bv_is_one(pi->bv[0])))
  {
    /* return current assignment for disabled branch */
    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
  }
  else if (pos_x != 0 && bzla_bvdomain_check_fixed_bits(mm, x, t))
  {
    res = bzla_bv_copy(mm, t);
  }
  else if (pos_x == 0)
  {
    if (bzla_bvdomain_is_fixed(mm, x))
    {
      res = bzla_bv_copy(mm, x->lo);
    }
    else
    {
      bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bvdomain_gen_delete(&gen);
    }
  }
  else
  {
    /* bits don't match, return current assignment */
    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
  }
  return res;
}

/* ========================================================================== */
/* Inverse value computation                                                  */
/* ========================================================================== */

static void
record_inv_stats(Bzla *bzla, uint32_t *stats)
{
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    *stats += 1;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }
}

#ifndef NDEBUG
static void
check_inv_dbg(Bzla *bzla,
              BzlaPropInfo *pi,
              BzlaPropIsInvFun is_inv_fun,
              BzlaPropIsInvFun is_inv_fun_const,
              bool same_bw)
{
  assert(bzla);
  assert(pi->exp);
  assert(bzla_node_is_regular(pi->exp));
  assert(pi->target_value);

  for (size_t i = 0; i < pi->exp->arity; ++i)
  {
    assert(pi->bv[i]);
  }

  assert(!same_bw
         || bzla_bv_get_width(pi->bv[1 - pi->pos_x])
                == bzla_bv_get_width(pi->target_value));
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 1);
  assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));
  assert(is_inv_fun(bzla, pi));
  assert(!pi->bvd[pi->pos_x]
         || !bzla_bvdomain_has_fixed_bits(bzla->mm, pi->bvd[pi->pos_x])
         || is_inv_fun_const(bzla, pi));
}

static void
check_result_binary_dbg(Bzla *bzla,
                        BzlaBitVector *(*fun)(BzlaMemMgr *,
                                              const BzlaBitVector *,
                                              const BzlaBitVector *),
                        BzlaPropInfo *pi,
                        const BzlaBitVector *res,
                        char *op)
{
  assert(bzla);
  assert(fun);
  assert(pi);
  assert(res);
  assert(op);

  (void) op;

  const BzlaBitVector *s;
  BzlaBitVector *tmp;
  char *str_s, *str_t, *str_res;

  s   = pi->bv[1 - pi->pos_x];
  tmp = pi->pos_x ? fun(bzla->mm, s, res) : fun(bzla->mm, res, s);

  assert(!bzla_bv_compare(tmp, pi->target_value));
  str_t   = bzla_bv_to_char(bzla->mm, pi->target_value);
  str_s   = bzla_bv_to_char(bzla->mm, s);
  str_res = bzla_bv_to_char(bzla->mm, res);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s %s %s",
          pi->pos_x,
          bzla_util_node2string(pi->exp),
          str_t,
          pi->pos_x ? str_s : str_res,
          op,
          pi->pos_x ? str_res : str_s);
  bzla_bv_free(bzla->mm, tmp);
  bzla_mem_freestr(bzla->mm, str_t);
  bzla_mem_freestr(bzla->mm, str_s);
  bzla_mem_freestr(bzla->mm, str_res);
}
#endif

/* -------------------------------------------------------------------------- */
/* INV: add                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_add(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_add, bzla_is_inv_add_const, true);
#endif
  BzlaBitVector *res;
  const BzlaBitVector *s, *t;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_add);

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;

  /* invertibility condition: true, res = t - s */
  res = bzla_bv_sub(bzla->mm, t, s);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_add, pi, res, "+");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_and(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_and, bzla_is_inv_and_const, true);
#endif
  uint32_t i, bw;
  int32_t bit_and, bit_e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  BzlaUIntStack dcbits;
  bool b;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_and);

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;
  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(mm, dcbits);

  res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
  assert(res);

  for (i = 0, bw = bzla_bv_get_width(t); i < bw; i++)
  {
    bit_and = bzla_bv_get_bit(t, i);
    bit_e   = bzla_bv_get_bit(s, i);

    assert(!bit_and || bit_e);

    /* ----------------------------------------------------------------------
     * res & s = s & res = t
     *
     * -> all bits set in t and s must be set in res
     * -> all bits not set in t but set in s must not be set in res
     * -> all bits not set in s can be chosen to be set randomly
     * ---------------------------------------------------------------------- */
    if (bit_and)
      bzla_bv_set_bit(res, i, 1);
    else if (bit_e)
      bzla_bv_set_bit(res, i, 0);
    else if (b)
      BZLA_PUSH_STACK(dcbits, i);
    else
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
  }

  if (b && BZLA_COUNT_STACK(dcbits))
    bzla_bv_flip_bit(
        res,
        BZLA_PEEK_STACK(
            dcbits,
            bzla_rng_pick_rand(&bzla->rng, 0, BZLA_COUNT_STACK(dcbits) - 1)));

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_and, pi, res, "AND");
#endif

  BZLA_RELEASE_STACK(dcbits);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_eq(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_eq, bzla_is_inv_eq_const, false);
#endif
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;
  s  = pi->bv[1 - pi->pos_x];
  t  = pi->target_value;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_eq);

  /**
   * invertibility condition: true
   * (res = s) = t   ->   t = 0: choose random res != s
   *                      t = 1: res = s
   */

  if (bzla_bv_is_zero(t))
  {
    if (bzla_rng_pick_with_prob(&bzla->rng,
                                bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_EQ_FLIP)))
    {
      res = 0;
      do
      {
        if (res) bzla_bv_free(bzla->mm, res);
        res = bzla_bv_copy(bzla->mm, pi->bv[pi->pos_x]);
        bzla_bv_flip_bit(
            res, bzla_rng_pick_rand(&bzla->rng, 0, bzla_bv_get_width(res) - 1));
      } while (!bzla_bv_compare(res, s));
    }
    else
    {
      res = 0;
      do
      {
        if (res) bzla_bv_free(mm, res);
        res = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(s));
      } while (!bzla_bv_compare(res, s));
    }
  }
  else
  {
    res = bzla_bv_copy(mm, s);
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_eq, pi, res, "=");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_ult(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_ult, bzla_is_inv_ult_const, false);
#endif
  bool isult;
  int32_t pos_x;
  uint32_t bw;
  BzlaBitVector *res, *zero, *one, *ones, *tmp;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);

  bw    = bzla_bv_get_width(s);
  zero  = bzla_bv_zero(mm, bw);
  one   = bzla_bv_one(mm, bw);
  ones  = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(t);

  res = 0;

  if (pos_x)
  {
    /* s < x = t ---------------------------------------------------------- */
    assert(!isult || bzla_bv_compare(s, ones)); /* CONFLICT: 1...1 < x */
    if (!isult)
    {
      /* s >= x */
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, s);
    }
    else
    {
      /* s < x */
      tmp = bzla_bv_add(mm, s, one);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    /* x < s = t ---------------------------------------------------------- */
    assert(!isult || !bzla_bv_is_zero(s)); /* CONFLICT: x < 0  */
    if (!isult)
    {
      /* x >= s */
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, s, ones);
    }
    else
    {
      /* x < s */
      tmp = bzla_bv_sub(mm, s, one);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_ult, pi, res, "<");
#endif
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, one);
  bzla_bv_free(mm, ones);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: sll                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sll(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_sll, bzla_is_inv_sll_const, true);
#endif
  int32_t pos_x;
  uint32_t bw, i, ctz_s, ctz_t, shift;
  BzlaBitVector *res, *tmp, *ones;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sll);

  res   = 0;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  /* ------------------------------------------------------------------------
   * s << x = t
   *
   * -> identify possible shift value via zero LSB in t
   *    (considering zero LSB in s)
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 << x = 0...0 -> choose res randomly */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /**
       * -> ctz(s) > ctz (t) -> conflict
       * -> shift = ctz(t) - ctz(s)
       *      -> if t = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       * -> else conflict
       */
      ctz_s = bzla_bv_get_num_trailing_zeros(s);
      assert(ctz_s <= ctz_t); /* CONFLICT: ctz_s > ctz_t */
      shift = ctz_t - ctz_s;
      if (bzla_bv_is_zero(t))
      {
        /**
         * x...x0 << x = 0...0
         * -> choose random shift <= res < bw
         */
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        res  = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
        bzla_bv_free(mm, ones);
        bzla_bv_free(mm, tmp);
      }
      else
      {
#ifndef NDEBUG
        uint32_t j;
        for (i = 0, j = shift, res = 0; i < bw - j; i++)
        {
          /* CONFLICT: shifted bits must match */
          assert(bzla_bv_get_bit(s, i) == bzla_bv_get_bit(t, j + i));
        }
#endif
        res = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
      }
    }
  }
  /* ------------------------------------------------------------------------
   * x << s = t
   *
   * -> x = t >> s
   *    set irrelevant MSBs (the ones that get shifted out) randomly
   * ------------------------------------------------------------------------ */
  else
  {
    /* actual value is small enough to fit into 32 bit (max bit width handled
     * by Bitwuzla is INT32_MAX) */
    if (bw > 64)
    {
      tmp   = bzla_bv_slice(mm, s, 32, 0);
      shift = bzla_bv_to_uint64(tmp);
      bzla_bv_free(mm, tmp);
    }
    else
    {
      shift = bzla_bv_to_uint64(s);
    }

    /* CONFLICT: the LSBs shifted must be zero */
    assert((shift >= bw || ctz_t >= shift) && (shift < bw || ctz_t == bw));

    res = bzla_bv_srl(mm, t, s);
    for (i = 0; i < shift && i < bw; i++)
    {
      bzla_bv_set_bit(res,
                      bzla_bv_get_width(res) - 1 - i,
                      bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_sll, pi, res, "<<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_srl(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_srl, bzla_is_inv_srl_const, true);
#endif
  int32_t pos_x;
  uint32_t bw, i, clz_s, clz_t, shift;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);

  res   = 0;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pi->pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  /* ------------------------------------------------------------------------
   * s >> x = t
   *
   * -> identify possible shift value via zero MSBs in t
   *    (considering zero MSBs in s)
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 >> x = 0...0 -> choose random res */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /**
       * clz(s) > clz(t) -> conflict
       *
       * -> shift = clz(t) - clz(s)
       *      -> if t = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       * -> else conflict
       */
      clz_s = bzla_bv_get_num_leading_zeros(s);
      assert(clz_s <= clz_t);
      shift = clz_t - clz_s;
      if (bzla_bv_is_zero(t))
      {
        /**
         * x...x0 >> x = 0...0
         * -> choose random shift <= res < bw
         */
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        res  = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
        bzla_bv_free(mm, ones);
        bzla_bv_free(mm, tmp);
      }
      else
      {
#ifndef NDEBUG
        uint32_t j;
        for (i = 0, j = shift, res = 0; i < bw - j; i++)
        {
          /* CONFLICT: shifted bits must match */
          assert(bzla_bv_get_bit(s, bw - 1 - i)
                 == bzla_bv_get_bit(t, bw - 1 - (j + i)));
        }
#endif
        res = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
      }
    }
  }
  /* ------------------------------------------------------------------------
   * x >> s = t
   *
   * -> x = t << s
   *    set irrelevant LSBs (the ones that get shifted out) randomly
   * ------------------------------------------------------------------------ */
  else
  {
    /* actual value is small enough to fit into 32 bit (max bit width handled
     * by Bitwuzla is INT32_MAX) */
    if (bw > 64)
    {
      tmp   = bzla_bv_slice(mm, s, 32, 0);
      shift = bzla_bv_to_uint64(tmp);
      bzla_bv_free(mm, tmp);
    }
    else
    {
      shift = bzla_bv_to_uint64(s);
    }

    /* CONFLICT: the MSBs shifted must be zero */
    assert((shift >= bw || clz_t >= shift) && (shift < bw || clz_t == bw));

    res = bzla_bv_sll(mm, t, s);
    for (i = 0; i < shift && i < bw; i++)
    {
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_srl, pi, res, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_mul(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_mul, bzla_is_inv_mul_const, true);
#endif
  int32_t lsb_s, ispow2_s;
  uint32_t i, j, bw;
  BzlaBitVector *res, *inv, *tmp, *tmp2;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

  s   = pi->bv[1 - pi->pos_x];
  t   = pi->target_value;
  bw  = bzla_bv_get_width(t);
  res = 0;

  /* ------------------------------------------------------------------------
   * s * res = t
   *
   * -> if s = 0: * t = 0 -> choose random value for res
   *              * t > 0 -> conflict
   *
   * -> if t odd and s even -> conflict
   *
   * -> if s odd -> determine res via modular inverse (extended euklid)
   *                  (unique solution)
   *
   * -> else if s is even (non-unique, multiple solutions possible!)
   *      * s = 2^n: + if number of 0-LSBs in t < n -> conflict
   *                 + else res = t >> n
   *                     (with all bits shifted in randomly set to 0 or 1)
   *      * else: s = 2^n * m, m is odd
   *              + if number of 0-LSBs in t < n -> conflict
   *              + else c' = t >> n
   *                (with all bits shifted in randomly set to 0 or 1)
   *                -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
   * ------------------------------------------------------------------------ */

  lsb_s = bzla_bv_get_bit(s, 0);
#ifndef NDEBUG
  int32_t t_lsb;
  t_lsb = bzla_bv_get_bit(t, 0);
  assert(!t_lsb || lsb_s); /* CONFLICT: t odd and s is even */
#endif

  if (bzla_bv_is_zero(s))
  {
    /* s = 0 -> if t = 0 choose random value, else conflict */
    assert(bzla_bv_is_zero(t)); /* CONFLICT: s = 0 but t != 0 */
    res = bzla_bv_new_random(mm, &bzla->rng, bw);
  }
  else
  {
    /* ----------------------------------------------------------------------
     * s odd
     *
     * -> determine res via modular inverse (extended euklid)
     *    (unique solution)
     * ---------------------------------------------------------------------- */
    if (lsb_s)
    {
      inv = bzla_bv_mod_inverse(mm, s);
      res = bzla_bv_mul(mm, inv, t);
      bzla_bv_free(mm, inv);
    }
    /* ----------------------------------------------------------------------
     * s even
     * (non-unique, multiple solutions possible!)
     *
     * if s = 2^n: + if number of 0-LSBs in t < n -> conflict
     *             + else res = t >> n
     *                      (with all bits shifted in set randomly)
     * else: s = 2^n * m, m is odd
     *       + if number of 0-LSBs in t < n -> conflict
     *       + else c' = t >> n (with all bits shifted in set randomly)
     *         res = c' * m^-1 (with m^-1 the mod inverse of m)
     * ---------------------------------------------------------------------- */
    else
    {
      if ((ispow2_s = bzla_bv_power_of_two(s)) >= 0)
      {
        for (i = 0; i < bw; i++)
        {
          if (bzla_bv_get_bit(t, i)) break;
        }

        /* CONFLICT: number of 0-LSBs in t < n (for s = 2^n) */
        assert(i >= (uint32_t) ispow2_s);

        /**
         * res = t >> n with all bits shifted in set randomly
         * (note: bw is not necessarily power of 2 -> do not use srl)
         */
        tmp = bzla_bv_slice(mm, t, bw - 1, ispow2_s);
        res = bzla_bv_uext(mm, tmp, ispow2_s);
        assert(bzla_bv_get_width(res) == bw);
        for (i = 0; i < (uint32_t) ispow2_s; i++)
          bzla_bv_set_bit(
              res, bw - 1 - i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
        bzla_bv_free(mm, tmp);
      }
      else
      {
        for (i = 0; i < bw; i++)
        {
          if (bzla_bv_get_bit(t, i)) break;
        }
        for (j = 0; j < bw; j++)
        {
          if (bzla_bv_get_bit(s, j)) break;
        }

        /* CONFLICT: number of 0-LSB in t < number of 0-LSB in s */
        assert(i >= j);

        /**
         * c' = t >> n (with all bits shifted in set randomly)
         * (note: bw is not necessarily power of 2 -> do not use srl)
         * -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
         */
        tmp = bzla_bv_slice(mm, t, bw - 1, j);
        res = bzla_bv_uext(mm, tmp, j);
        assert(bzla_bv_get_width(res) == bw);
        bzla_bv_free(mm, tmp);

        tmp  = bzla_bv_slice(mm, s, bw - 1, j);
        tmp2 = bzla_bv_uext(mm, tmp, j);
        assert(bzla_bv_get_width(tmp2) == bw);
        assert(bzla_bv_get_bit(tmp2, 0));
        inv = bzla_bv_mod_inverse(mm, tmp2);
        bzla_bv_free(mm, tmp);
        bzla_bv_free(mm, tmp2);
        tmp = res;
        res = bzla_bv_mul(mm, tmp, inv);
        /* choose one of all possible values */
        for (i = 0; i < j; i++)
          bzla_bv_set_bit(
              res, bw - 1 - i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
        bzla_bv_free(mm, tmp);
        bzla_bv_free(mm, inv);
      }
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_mul, pi, res, "*");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_udiv(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_udiv, bzla_is_inv_udiv_const, true);
#endif
  int32_t pos_x;
  uint32_t bw;
  BzlaBitVector *res, *lo, *up, *one, *ones, *tmp;
  BzlaMemMgr *mm;
  BzlaRNG *rng;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_udiv);

  rng   = &bzla->rng;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(s);

  one  = bzla_bv_one(mm, bw);
  ones = bzla_bv_ones(mm, bw); /* 2^bw - 1 */

  res = 0;

  /* ------------------------------------------------------------------------
   * s / x = t
   *
   * -> if t = 2^bw - 1: + s = t = 2^bw - 1 -> x = 1 or x = 0
   *                     + s != t -> x = 0
   * -> if t = 0 and 0 < s < 2^bw - 1 choose random x > s
   *             and s = 0            choose random x > 0
   *             else conflict
   * -> if s < t -> conflict
   * -> if t is a divisor of s choose with 0.5 prob out of
   *      + x = t / s
   *      + choose s s.t. s / x = t
   * -> else choose s s.t. s / x = t
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
    if (!bzla_bv_compare(t, ones))
    {
      if (!bzla_bv_compare(s, t) && bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
        /**
         * s = t = 2^bw - 1 -> choose either x = 0 or x = 1
         * with prob 0.5
         */
        res = bzla_bv_one(mm, bw);
      }
      else
      {
        /* t = 2^bw - 1 and s != t -> x = 0 */
        res = bzla_bv_zero(mm, bw);
      }
    }
    else if (bzla_bv_is_zero(t))
    {
      if (bzla_bv_is_zero(s))
      {
        /* t = 0 and s = 0 -> choose random x > 0 */
        res = bzla_bv_new_random_range(mm, rng, bw, one, ones);
      }
      else
      {
        assert(bzla_bv_compare(s, ones)); /* CONFLICT: s = ~0  and t = 0 */

        /* t = 0 and 0 < s < 2^bw - 1 -> choose random x > s */
        tmp = bzla_bv_inc(mm, s);
        res = bzla_bv_new_random_range(mm, rng, bw, tmp, ones);
        bzla_bv_free(mm, tmp);
      }
    }
    else
    {
      assert(bzla_bv_compare(s, t) >= 0); /* CONFLICT: s < t */

      /**
       * if t is a divisor of s, choose x = s / t
       * with prob = 0.5 and a s s.t. s / x = t otherwise
       */
      tmp = bzla_bv_urem(mm, s, t);
      if (bzla_bv_is_zero(tmp) && bzla_rng_pick_with_prob(rng, 500))
      {
        bzla_bv_free(mm, tmp);
        res = bzla_bv_udiv(mm, s, t);
      }
      else
      {
        /**
         * choose x out of all options that yield s / x = t
         * Note: udiv always truncates the results towards 0.
         */

        /* determine upper and lower bounds for x:
         * up = s / t
         * lo = s / (t + 1) + 1
         * if lo > up -> conflict */
        bzla_bv_free(mm, tmp);
        up  = bzla_bv_udiv(mm, s, t); /* upper bound */
        tmp = bzla_bv_inc(mm, t);
        lo  = bzla_bv_udiv(mm, s, tmp); /* lower bound (excl.) */
        bzla_bv_free(mm, tmp);
        tmp = lo;
        lo  = bzla_bv_inc(mm, tmp); /* lower bound (incl.) */
        bzla_bv_free(mm, tmp);

        assert(bzla_bv_compare(lo, up) <= 0); /* CONFLICT: lo > up */

        /* choose lo <= x <= up */
        res = bzla_bv_new_random_range(mm, rng, bw, lo, up);
        bzla_bv_free(mm, lo);
        bzla_bv_free(mm, up);
      }
    }
  }

  /* ------------------------------------------------------------------------
   * x / s = t
   *
   * -> if t = 2^bw - 1 and s = 1 x = 2^bw-1
   *                    and s = 0, choose random x > 0
   *                    and s > 0 -> conflict
   * -> if s = 0 and t < 2^bw - 1 -> conflict
   * -> if s * t does not overflow, choose with 0.5 prob out of
   *      + x = s * t
   *      + choose x s.t. x / s = t
   * -> else choose x s.t. x / s = t
   * ------------------------------------------------------------------------ */
  else
  {
    if (!bzla_bv_compare(t, ones))
    {
      if (!bzla_bv_compare(s, one))
      {
        /* t = 2^bw-1 and s = 1 -> x = 2^bw-1 */
        res = bzla_bv_copy(mm, ones);
      }
      else
      {
        assert(bzla_bv_is_zero(s)); /* CONFLICT: t = ~0 and s != 0 */
        /* t = 2^bw - 1 and s = 0 -> choose random x */
        res = bzla_bv_new_random(mm, rng, bw);
      }
    }
    else
    {
      /* if s * t does not overflow, choose x = s * t
       * with prob = 0.5 and a s s.t. x / s = t otherwise
       * -------------------------------------------------------------------- */

      assert(!bzla_bv_is_umulo(mm, s, t)); /* CONFLICT: overflow: s * t */
      if (bzla_rng_pick_with_prob(rng, 500))
        res = bzla_bv_mul(mm, s, t);
      else
      {
        /**
         * choose x out of all options that yield
         * x / s = t
         * Note: udiv always truncates the results towards 0.
         */

        /* determine upper and lower bounds for x:
         * up = s * (t + 1) - 1
         *      if s * (t + 1) does not overflow
         *      else 2^bw - 1
         * lo = s * t */
        lo  = bzla_bv_mul(mm, s, t);
        tmp = bzla_bv_inc(mm, t);
        if (bzla_bv_is_umulo(mm, s, tmp))
        {
          bzla_bv_free(mm, tmp);
          up = bzla_bv_copy(mm, ones);
        }
        else
        {
          up = bzla_bv_mul(mm, s, tmp);
          bzla_bv_free(mm, tmp);
          tmp = bzla_bv_dec(mm, up);
          bzla_bv_free(mm, up);
          up = tmp;
        }

        res = bzla_bv_new_random_range(
            mm, &bzla->rng, bzla_bv_get_width(s), lo, up);

        bzla_bv_free(mm, up);
        bzla_bv_free(mm, lo);
      }
    }
  }

  bzla_bv_free(mm, ones);
  bzla_bv_free(mm, one);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_udiv, pi, res, "/");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_urem(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_urem, bzla_is_inv_urem_const, true);
#endif
  uint32_t bw, cnt;
  int32_t cmp, pos_x;
  BzlaBitVector *res, *ones, *tmp, *tmp2, *one, *n, *mul, *n_hi, *sub;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_urem);

  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);

  ones = bzla_bv_ones(mm, bw); /* 2^bw - 1 */
  one  = bzla_bv_one(mm, bw);

  res = 0;

  /* -----------------------------------------------------------------------
   * s % x = t
   *
   * -> if t = 1...1 -> s = 1...1 and x = 0...0, else conflict
   * -> if s = t, choose either x = 0 or some x > t randomly
   * -> if t > 0 and t = s - 1, conflict
   * -> if s > t, x = ((s - t) / n) > t, else conflict
   * -> if s < t, conflict
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
    if (!bzla_bv_compare(t, ones))
    {
      /* CONFLICT: t = ~0 but s != ~0 */
      assert(!bzla_bv_compare(s, ones));

      /* s % x = ~0 -> s = ~0, x = 0 */
      res = bzla_bv_zero(mm, bw);
    }
    else
    {
      cmp = bzla_bv_compare(s, t);

      if (cmp == 0)
      {
        /* s = t, choose either x = 0 or random x > t
         * ------------------------------------------------------------------ */

        if (bzla_rng_pick_with_prob(&bzla->rng, 250))
        {
          /* choose x = 0 with prob = 0.25 */
          res = bzla_bv_zero(mm, bw);
        }
        else
        {
          /* t < res <= 2^bw - 1 */
          tmp = bzla_bv_add(mm, t, one);
          res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
          bzla_bv_free(mm, tmp);
        }
      }
      else
      {
        /* s > t, x = (s - t) / n
         * ------------------------------------------------------------------ */

        assert(cmp > 0); /* CONFLICT: s < t */
#ifndef NDEBUG
        if (!bzla_bv_is_zero(t))
        {
          tmp = bzla_bv_dec(mm, s);
          /* CONFLICT: t = s - 1 -> s % x = s - 1 -> not possible if t > 0 */
          assert(bzla_bv_compare(t, tmp));
          bzla_bv_free(mm, tmp);
        }
#endif
        sub = bzla_bv_sub(mm, s, t);
        assert(bzla_bv_compare(sub, t) > 0); /* CONFLICT: s - t <= t */

        /**
         * choose either n = 1 or 1 <= n < (s - t) / t
         * with prob = 0.5
         */
        if (bzla_rng_pick_with_prob(&bzla->rng, 500))
        {
          res = bzla_bv_copy(mm, sub);
        }
        else
        {
          /**
           * 1 <= n < (s - t) / t (non-truncating)
           * (note: div truncates towards 0!)
           */

          if (bzla_bv_is_zero(t))
          {
            /* t = 0 -> 1 <= n <= s */
            n_hi = bzla_bv_copy(mm, s);
          }
          else
          {
            /**
             * x > t
             * -> (s - t) / n > t
             * -> (s - t) / t > n
             */
            bzla_bv_udiv_urem(mm, sub, t, &tmp2, &tmp);
            if (bzla_bv_is_zero(tmp))
            {
              /**
               * (s - t) / t is not truncated (remainder is 0) and is therefore
               * the EXclusive upper bound, the inclusive upper bound is:
               *   n_hi = (s - t) / t - 1
               */
              n_hi = bzla_bv_sub(mm, tmp2, one);
              bzla_bv_free(mm, tmp2);
            }
            else
            {
              /**
               * (s - t) / t is truncated (remainder is not 0) and is therefore
               * the INclusive upper bound:
               *   n_hi = (s - t) / t
               */
              n_hi = tmp2;
            }
            bzla_bv_free(mm, tmp);
          }

          if (bzla_bv_is_zero(n_hi))
          {
            assert(false);
            res = bzla_bv_udiv(mm, sub, one);
          }
          else
          {
            /**
             * choose 1 <= n <= n_hi randomly
             * s.t (s - t) % n = 0
             */
            n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, n_hi);
            tmp = bzla_bv_urem(mm, sub, n);
            for (cnt = 0; cnt < bw && !bzla_bv_is_zero(tmp); cnt++)
            {
              bzla_bv_free(mm, n);
              bzla_bv_free(mm, tmp);
              n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, n_hi);
              tmp = bzla_bv_urem(mm, sub, n);
            }

            if (bzla_bv_is_zero(tmp))
            {
              /* res = (s - t) / n */
              res = bzla_bv_udiv(mm, sub, n);
            }
            else
            {
              /* fallback: n = 1 */
              res = bzla_bv_copy(mm, sub);
            }

            bzla_bv_free(mm, n);
            bzla_bv_free(mm, tmp);
          }
          bzla_bv_free(mm, n_hi);
        }
        bzla_bv_free(mm, sub);
      }
    }
  }
  /* ------------------------------------------------------------------------
   * x % s = t
   *
   * -> if s = 0, x = t
   * -> if t = 1...1 and s != 0, conflict
   * -> if s <= t, conflict
   * -> if t > 0 and s = 1, conflict
   * -> else choose either
   *      - x = t, or
   *      - x = s * n + b, with n s.t. (s * n + b) does not overflow
   * ------------------------------------------------------------------------ */
  else
  {
    /* CONFLICT: t > 0 and s = 1 */
    assert(bzla_bv_is_zero(t) || !bzla_bv_is_one(s));

    if (bzla_bv_is_zero(s))
    {
      /* s = 0 -> x = t */
      res = bzla_bv_copy(mm, t);
    }
    else if (!bzla_bv_compare(t, ones))
    {
      assert(bzla_bv_is_zero(s)); /* CONFLICT: s != 0 */
      /* t = ~0 -> s = 0, x = ~0 */
      res = bzla_bv_copy(mm, t);
    }
    else
    {
      assert(bzla_bv_compare(s, t) > 0); /* CONFLICT: s <= t */

      if (bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
      BVUREM_EQ_0:
        /**
         * choose simplest solution (0 <= res < s -> res = t)
         * with prob 0.5
         */
        res = bzla_bv_copy(mm, t);
      }
      else
      {
        /**
         * x = s * n + t,
         * with n s.t. (s * n + t) does not overflow
         */
        tmp2 = bzla_bv_sub(mm, ones, s);

        /* overflow for n = 1 -> only simplest solution possible */
        if (bzla_bv_compare(tmp2, t) < 0)
        {
          bzla_bv_free(mm, tmp2);
          goto BVUREM_EQ_0;
        }
        else
        {
          bzla_bv_free(mm, tmp2);

          tmp = bzla_bv_copy(mm, ones);
          n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);

          while (bzla_bv_is_umulo(mm, s, n))
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_sub(mm, n, one);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
          }

          mul  = bzla_bv_mul(mm, s, n);
          tmp2 = bzla_bv_sub(mm, ones, mul);

          /* choose n s.t. addition in s * n + t does not overflow */
          while (bzla_bv_compare(tmp2, t) < 0)
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_dec(mm, n);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
            bzla_bv_free(mm, mul);
            bzla_bv_free(mm, tmp2);
            mul  = bzla_bv_mul(mm, s, n);
            tmp2 = bzla_bv_sub(mm, ones, mul);
          }

          res = bzla_bv_add(mm, mul, t);
          assert(bzla_bv_compare(res, mul) >= 0);
          assert(bzla_bv_compare(res, t) >= 0);

          bzla_bv_free(mm, tmp);
          bzla_bv_free(mm, tmp2);
          bzla_bv_free(mm, mul);
          bzla_bv_free(mm, n);
        }
      }
    }
  }

  bzla_bv_free(mm, one);
  bzla_bv_free(mm, ones);

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_urem, pi, res, "%");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_concat(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_concat, bzla_is_inv_concat_const, false);
  BzlaBitVector *tmp;
#endif
  int32_t pos_x;
  uint32_t bw_t, bw_s;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_concat);

  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  bw_t  = bzla_bv_get_width(t);
  bw_s  = bzla_bv_get_width(s);
  res   = 0;

  /* ------------------------------------------------------------------------
   * s o x = t
   *
   * -> slice x out of the lower bits of t
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
#ifndef NDEBUG
    tmp = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bw_s);
    assert(!bzla_bv_compare(tmp, s)); /* CONFLICT: s bits do not match t */
#endif
    res = bzla_bv_slice(mm, t, bw_t - bw_s - 1, 0);
  }
  /* ------------------------------------------------------------------------
   * x o s = t
   *
   * -> slice x out of the upper bits of t
   * ------------------------------------------------------------------------ */
  else
  {
#ifndef NDEBUG
    tmp = bzla_bv_slice(mm, t, bw_s - 1, 0);
    assert(!bzla_bv_compare(tmp, s)); /* CONFLICT: s bits do not match t */
#endif
    res = bzla_bv_slice(mm, t, bw_t - 1, bw_s);
  }
#ifndef NDEBUG
  bzla_bv_free(mm, tmp);
  check_result_binary_dbg(bzla, bzla_bv_concat, pi, res, "o");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_slice(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_slice, bzla_is_inv_slice_const, false);
#endif

  uint32_t i, upper, lower, rlower, rupper, rboth, bw_x;
  BzlaBitVector *res;
  const BzlaBitVector *t, *x;
  BzlaMemMgr *mm;
  bool bkeep, bflip;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_slice);

  /* invertibility condition: true */

  mm = bzla->mm;
  x  = pi->bv[0];
  t  = pi->target_value;

  bflip = bzla_rng_pick_with_prob(
      &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP));

  bkeep = bflip ? true
                : bzla_rng_pick_with_prob(
                    &bzla->rng,
                    bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_SLICE_KEEP_DC));

  upper = bzla_node_bv_slice_get_upper(pi->exp);
  lower = bzla_node_bv_slice_get_lower(pi->exp);

  res = bzla_bv_zero(mm, bzla_node_bv_get_width(bzla, pi->exp->e[0]));

  /* keep previous value for don't care bits or set randomly with prob
   * BZLA_OPT_PROP_PROB_SLICE_KEEP_DC */
  for (i = 0; i < lower; i++)
    bzla_bv_set_bit(
        res,
        i,
        bkeep ? bzla_bv_get_bit(x, i) : bzla_rng_pick_rand(&bzla->rng, 0, 1));

  /* set sliced bits to propagated value */
  for (i = lower; i <= upper; i++)
    bzla_bv_set_bit(res, i, bzla_bv_get_bit(t, i - lower));

  /* keep previous value for don't care bits or set randomly with prob
   * BZLA_OPT_PROP_PROB_SLICE_KEEP_DC */
  bw_x = bzla_bv_get_width(res);
  for (i = upper + 1; i < bw_x; i++)
    bzla_bv_set_bit(
        res,
        i,
        bkeep ? bzla_bv_get_bit(x, i) : bzla_rng_pick_rand(&bzla->rng, 0, 1));

  if (bflip)
  {
    rboth  = 0;
    rupper = bw_x - 1;
    rlower = 0;

    if (lower)
    {
      rboth += 1;
      rlower = bzla_rng_pick_rand(&bzla->rng, 0, lower - 1);
    }

    if (upper + 1 < bw_x)
    {
      rboth += 2;
      rupper = bzla_rng_pick_rand(&bzla->rng, upper + 1, bw_x - 1);
    }

    switch (rboth)
    {
      case 3:
        assert(rupper >= upper + 1 && rupper < bw_x);
        assert(rlower < lower);
        bzla_bv_flip_bit(
            res, bzla_rng_pick_with_prob(&bzla->rng, 500) ? rupper : rlower);
        break;
      case 2:
        assert(rupper >= upper + 1 && rupper < bw_x);
        bzla_bv_flip_bit(res, rupper);
        break;
      case 1:
        assert(rlower < lower);
        bzla_bv_flip_bit(res, rlower);
        break;
    }
  }

#ifndef NDEBUG
  BzlaBitVector *tmpdbg = bzla_bv_slice(mm, res, upper, lower);
  assert(!bzla_bv_compare(tmpdbg, t));
  bzla_bv_free(mm, tmpdbg);

  char *str_t   = bzla_bv_to_char(mm, t);
  char *str_res = bzla_bv_to_char(mm, res);
  BZLALOG(3,
          "prop (xxxxx): %s: %s := %s[%d:%d]",
          bzla_util_node2string(pi->exp),
          str_t,
          str_res,
          lower,
          upper);
  bzla_mem_freestr(mm, str_t);
  bzla_mem_freestr(mm, str_res);
#endif
  return res;
}

BzlaBitVector *
bzla_proputils_inv_sign_extend(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(
      bzla, pi, bzla_is_inv_sign_extend, bzla_is_inv_sign_extend_const, false);
#endif
  assert(pi->res_x);
  return bzla_bv_copy(bzla->mm, pi->res_x->lo);
}

BzlaBitVector *
bzla_proputils_cons_sign_extend(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  return 0;
}

BzlaBitVector *
bzla_proputils_inv_sign_extend_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(pi->res_x);
  return bzla_bv_copy(bzla->mm, pi->res_x->lo);
}

/* -------------------------------------------------------------------------- */
/* INV: cond                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_cond(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi->exp);
  assert(bzla_node_is_regular(pi->exp));
  assert(pi->pos_x || !bzla_bv_compare(pi->bv[1], pi->target_value)
         || !bzla_bv_compare(pi->bv[2], pi->target_value));
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 2);
  assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));

  bool cmp0, cmp1;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_cond);

  mm = bzla->mm;
  t  = pi->target_value;

  if (pi->pos_x == 0)
  {
    cmp0 = bzla_bv_compare(pi->bv[1], t) == 0;
    cmp1 = bzla_bv_compare(pi->bv[2], t) == 0;
    if (cmp0 && cmp1)
    {
      res = bzla_rng_flip_coin(&bzla->rng) ? bzla_bv_one(mm, 1)
                                           : bzla_bv_zero(mm, 1);
    }
    else if (cmp0)
    {
      res = bzla_bv_one(mm, 1);
    }
    else
    {
      assert(cmp1);
      res = bzla_bv_zero(mm, 1);
    }
  }
  else if ((pi->pos_x == 1 && bzla_bv_is_zero(pi->bv[0]))
           || (pi->pos_x == 2 && bzla_bv_is_one(pi->bv[0])))
  {
    /* return current assignment for disabled branch */
    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
  }
  else
  {
    res = bzla_bv_copy(mm, t);
  }
#if 0
  BzlaBitVector *res, *s1, *s2;
  BzlaMemMgr *mm = bzla->mm;

  (void) domains;
  (void) d_res_x;

  s1 = (BzlaBitVector *) bzla_model_get_bv (bzla, cond->e[1]);
  s2 = (BzlaBitVector *) bzla_model_get_bv (bzla, cond->e[2]);
#ifndef NDEBUG
  char *str_t  = bzla_bv_to_char (bzla->mm, t);
  char *str_s0 = bzla_bv_to_char (mm, s);
  char *str_s1 = bzla_bv_to_char (mm, s1);
  char *str_s2 = bzla_bv_to_char (mm, s2);
#endif

  record_inv_stats (bzla, &BZLA_PROP_SOLVER (bzla)->stats.inv_cond);

  /* either assume that cond is fixed and propagate s
   * to enabled path, or flip condition */

  if (idx_x == 0)
  {
    /* flip condition */
    res = bzla_bv_not (mm, s);
  }
  else
  {
    /* else continue propagating current target value down */
    res = bzla_bv_copy (mm, t);
    if (bzla_node_is_bv_const (cond->e[idx_x]))
    {
      bool is_recoverable = !bzla_bv_compare (t, idx_x == 1 ? s2 : s1);
#ifndef NDEBUG
      if (idx_x == 2)
      {
        BZLALOG (2,
                 "%s CONFLICT (@%d): %s := %s ? %s : x",
                 is_recoverable ? "recoverable" : "non-recoverable",
                 bzla_node_get_id (cond),
                 str_t,
                 str_s0,
                 str_s1);
      }
      else
      {
        BZLALOG (2,
                 "%s CONFLICT (@%d): %s := %s ? x : %s",
                 is_recoverable ? "recoverable" : "non-recoverable",
                 bzla_node_get_id (cond),
                 str_t,
                 str_s0,
                 str_s2);
      }
      BZLALOG (2, "");
#endif
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        if (is_recoverable)
          BZLA_PROP_SOLVER (bzla)->stats.rec_conf += 1;
        else
          BZLA_PROP_SOLVER (bzla)->stats.non_rec_conf += 1;
      }
      else
      {
        if (is_recoverable)
          BZLA_SLS_SOLVER (bzla)->stats.move_prop_rec_conf += 1;
        else
          BZLA_SLS_SOLVER (bzla)->stats.move_prop_non_rec_conf += 1;
      }
    }
  }
#endif

#ifndef NDEBUG
  char *str_res = bzla_bv_to_char(mm, res);
  char *str_t   = bzla_bv_to_char(bzla->mm, t);
  char *str_s0  = bzla_bv_to_char(mm, pi->bv[0]);
  char *str_s1  = bzla_bv_to_char(mm, pi->bv[1]);
  char *str_s2  = bzla_bv_to_char(mm, pi->bv[2]);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s ? %s : %s",
          pi->pos_x,
          bzla_util_node2string(pi->exp),
          str_t,
          pi->pos_x == 0 ? str_res : str_s0,
          pi->pos_x == 1 ? str_res : str_s1,
          pi->pos_x == 2 ? str_res : str_s2);
  bzla_mem_freestr(mm, str_t);
  bzla_mem_freestr(mm, str_res);
  bzla_mem_freestr(mm, str_s0);
  bzla_mem_freestr(mm, str_s1);
  bzla_mem_freestr(mm, str_s2);
#endif
  return res;
}

/* ========================================================================== */
/* Inverse value computation with respect to const bits                       */
/* ========================================================================== */

#define BZLA_PROPUTILS_GEN_MAX_RAND 10

/* -------------------------------------------------------------------------- */
/* INV: add                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_add_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_add, bzla_is_inv_add_const, true);
#endif
  BzlaMemMgr *mm;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;
  s  = pi->bv[1 - pi->pos_x];
  t  = pi->target_value;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    BzlaBitVector *tmp = bzla_bv_add(mm, s, x->lo);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_add);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    res = bzla_proputils_inv_add(bzla, pi);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_add, pi, res, "+");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_and_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_and, bzla_is_inv_and_const, true);
#endif
  BzlaMemMgr *mm;
  BzlaBitVector *tmp, *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;
  s  = pi->bv[1 - pi->pos_x];
  t  = pi->target_value;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = bzla_bv_and(mm, s, x->lo);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_and);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    res = bzla_proputils_inv_and(bzla, pi);
    set_const_bits(mm, x, &res);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_and, pi, res, "&");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_eq_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_eq, bzla_is_inv_eq_const, false);
#endif
  BzlaMemMgr *mm;
  BzlaBitVector *tmp, *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaBvDomainGenerator gen;

  mm = bzla->mm;
  s  = pi->bv[1 - pi->pos_x];
  t  = pi->target_value;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = bzla_bv_eq(mm, s, x->lo);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_eq);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (bzla_bv_is_zero(t))
  {
    bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
    do
    {
      res = bzla_bvdomain_gen_random(&gen);
    } while (bzla_bv_compare(res, s) == 0);
    res = bzla_bv_copy(mm, res);
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    assert(bzla_bvdomain_check_fixed_bits(mm, x, s));
    res = bzla_bv_copy(mm, s);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_eq, pi, res, "=");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_ult_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_ult, bzla_is_inv_ult_const, false);
#endif
  bool isult;
  int32_t pos_x;
  uint32_t bw;
  BzlaBitVector *res, *zero, *one, *ones, *tmp;
  BzlaMemMgr *mm;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaBvDomainGenerator gen;

  mm = bzla->mm;

  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);

  bw    = bzla_bv_get_width(s);
  zero  = bzla_bv_zero(mm, bw);
  one   = bzla_bv_one(mm, bw);
  ones  = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(t);

  res = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = pos_x ? bzla_bv_ult(mm, s, x->lo) : bzla_bv_ult(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    if (pos_x)
    {
      /* s < x = t ---------------------------------------------------------- */
      if (!isult)
      {
        /* s >= x */
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, zero, s);
      }
      else
      {
        /* s < x */
        tmp = bzla_bv_add(mm, s, one);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, ones);
        bzla_bv_free(mm, tmp);
      }
    }
    else
    {
      /* x < s = t ---------------------------------------------------------- */
      if (!isult)
      {
        /* x >= s */
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, s, ones);
      }
      else
      {
        /* x < s */
        tmp = bzla_bv_sub(mm, s, one);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, zero, tmp);
        bzla_bv_free(mm, tmp);
      }
    }
    assert(bzla_bvdomain_gen_has_next(&gen));
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_ult, pi, res, "<");
#endif
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, one);
  bzla_bv_free(mm, ones);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: sll                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sll_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(pi->pos_x || pi->res_x == 0);
  assert(!pi->pos_x || pi->res_x);
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_sll, bzla_is_inv_sll_const, true);
#endif
  int32_t pos_x;
  uint32_t cnt;
  BzlaBitVector *tmp, *res, *bv;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  res   = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = pos_x ? bzla_bv_sll(mm, s, x->lo) : bzla_bv_sll(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sll);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pos_x)
  {
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sll);

    assert(pi->res_x);
    assert(bzla_bvdomain_is_fixed(mm, pi->res_x));
    bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, pi->res_x->lo, 0);
    assert(bzla_bvdomain_gen_has_next(&gen));
    for (cnt = 0, res = 0; cnt < BZLA_PROPUTILS_GEN_MAX_RAND; cnt++)
    {
      bv  = bzla_bvdomain_gen_random(&gen);
      tmp = bzla_bv_sll(mm, s, bv);
      if (bzla_bv_compare(tmp, t) == 0)
      {
        res = bzla_bv_copy(mm, bv);
        bzla_bv_free(mm, tmp);
        break;
      }
      bzla_bv_free(mm, tmp);
    }
    if (!res) res = bzla_bv_copy(mm, pi->res_x->lo);
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    assert(pi->res_x == 0);
    res = bzla_proputils_inv_sll(bzla, pi);
    set_const_bits(mm, x, &res);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_sll, pi, res, "<<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_srl_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(pi->pos_x || pi->res_x == 0);
  assert(!pi->pos_x || pi->res_x);
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_srl, bzla_is_inv_srl_const, true);
#endif
  int32_t pos_x;
  uint32_t cnt;
  BzlaBitVector *tmp, *res, *bv;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  res   = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = pos_x ? bzla_bv_srl(mm, s, x->lo) : bzla_bv_srl(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pos_x)
  {
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);

    assert(pi->res_x);
    assert(bzla_bvdomain_is_fixed(mm, pi->res_x));
    bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, pi->res_x->lo, 0);
    assert(bzla_bvdomain_gen_has_next(&gen));
    for (cnt = 0, res = 0; cnt < BZLA_PROPUTILS_GEN_MAX_RAND; cnt++)
    {
      bv  = bzla_bvdomain_gen_random(&gen);
      tmp = bzla_bv_srl(mm, s, bv);
      if (bzla_bv_compare(tmp, t) == 0)
      {
        res = bzla_bv_copy(mm, bv);
        bzla_bv_free(mm, tmp);
        break;
      }
      bzla_bv_free(mm, tmp);
    }
    if (!res) res = bzla_bv_copy(mm, pi->res_x->lo);
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    assert(pi->res_x == 0);
    res = bzla_proputils_inv_srl(bzla, pi);
    set_const_bits(mm, x, &res);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_srl, pi, res, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_mul_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_mul, bzla_is_inv_mul_const, true);
#endif
  BzlaBitVector *tmp, *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  s  = pi->bv[1 - pi->pos_x];
  t  = pi->target_value;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = bzla_bv_mul(mm, s, x->lo);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pi->res_x)
  {
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

    if (bzla_bvdomain_is_fixed(mm, pi->res_x))
    {
#ifndef NDEBUG
      tmp = bzla_bv_mul(mm, s, pi->res_x->lo);
      assert(bzla_bv_compare(tmp, t) == 0);
      bzla_bv_free(mm, tmp);
#endif
      res = bzla_bv_copy(mm, pi->res_x->lo);
    }
    else
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(t));
      set_const_bits(mm, pi->res_x, &res);
    }
  }
  else
  {
    if (bzla_bv_is_zero(s))
    {
      record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

      res = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(t));
      set_const_bits(mm, x, &res);
    }
    else
    {
      assert(!bzla_bvdomain_has_fixed_bits(mm, x));
      res = bzla_proputils_inv_mul(bzla, pi);
    }
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_mul, pi, res, "*");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_udiv_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_udiv, bzla_is_inv_udiv_const, true);
#endif
  int32_t pos_x;
  uint32_t bw;
  BzlaBitVector *tmp, *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaMemMgr *mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_udiv);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  if (!bzla_bvdomain_has_fixed_bits(mm, x))
  {
    res = bzla_proputils_inv_udiv(bzla, pi);
  }
  else if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = pos_x ? bzla_bv_udiv(mm, s, x->lo) : bzla_bv_udiv(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    BzlaBvDomainGenerator gen;

    if (pi->res_x)
    {
      assert(pi->res_x);
      bzla_bvdomain_gen_init_range(
          mm, &bzla->rng, &gen, x, pi->res_x->lo, pi->res_x->hi);
    }
    else if (bzla_bv_is_zero(s))
    {
      bw = bzla_bv_get_width(s);
      if (pos_x)
      {
        if (bzla_bv_is_ones(t))
        {
          /* x = 0 */
          tmp = bzla_bv_zero(mm, bw);
          bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, tmp);
          bzla_bv_free(mm, tmp);
        }
        else
        {
          /* x > 0 */
          tmp = bzla_bv_one(mm, bw);
          bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, 0);
          bzla_bv_free(mm, tmp);
        }
      }
      else
      {
        /* x random */
        bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
      }
    }
    else
    {
      assert(bzla_bv_is_zero(t));
      if (pos_x)
      {
        /* x > s */
        tmp = bzla_bv_inc(mm, s);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, 0);
        bzla_bv_free(mm, tmp);
      }
      else
      {
        /* x < s */
        tmp = bzla_bv_dec(mm, s);
        bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, 0, tmp);
        bzla_bv_free(mm, tmp);
      }
    }

    assert(bzla_bvdomain_gen_has_next(&gen));
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_udiv, pi, res, "/");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_urem_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_urem, bzla_is_inv_urem_const, true);
#endif
  int32_t pos_x;
  uint32_t bw, cnt;
  BzlaBitVector *tmp, *res, *ones, *one, *bv, *simple;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaMemMgr *mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_urem);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  bw = bzla_bv_get_width(s);
  assert(bzla_bv_get_width(t) == bw);
  assert(bzla_bvdomain_get_width(x) == bw);

  if (!bzla_bvdomain_has_fixed_bits(mm, x))
  {
    res = bzla_proputils_inv_urem(bzla, pi);
  }
  else if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = pos_x ? bzla_bv_urem(mm, s, x->lo) : bzla_bv_urem(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pos_x)
  {
    if (pi->res_x)
    {
      assert(pi->res_x);
      res = bzla_bv_copy(mm, pi->res_x->lo);
#ifndef NDEBUG
      BzlaBitVector *tmp = bzla_bv_urem(mm, s, res);
      assert(bzla_bv_compare(tmp, t) == 0);
      bzla_bv_free(mm, tmp);
#endif
    }
    else
    {
      one = bzla_bv_one(mm, bw);
      if (bzla_bv_is_ones(t))
      {
        /* s % x = t = ones: s = ones, x = 0 */
        res = bzla_bv_zero(mm, bw);
      }
      else if (bzla_bv_compare(s, t) == 0)
      {
        /* s = t and t != ones: x = 0 or random x > t */
        if (bzla_bv_compare(x->hi, t) <= 0
            || (bzla_bv_is_zero(x->lo) && bzla_rng_flip_coin(&bzla->rng)))
        {
          res = bzla_bv_zero(mm, bw);
        }
        else
        {
          BzlaBvDomainGenerator gen;
          res = 0;
          tmp = bzla_bv_inc(mm, t);
          bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, tmp, 0);
          bzla_bv_free(mm, tmp);
          assert(bzla_bvdomain_gen_has_next(&gen));
          while (bzla_bvdomain_gen_has_next(&gen))
          {
            bv  = bzla_bvdomain_gen_random(&gen);
            tmp = bzla_bv_urem(mm, s, bv);
            if (bzla_bv_compare(tmp, t) == 0)
            {
              res = bzla_bv_copy(mm, bv);
              bzla_bv_free(mm, tmp);
              break;
            }
            bzla_bv_free(mm, tmp);
          }
          assert(res);
          bzla_bvdomain_gen_delete(&gen);
        }
      }
      else
      {
        if (bzla_bv_is_zero(t) && bzla_bvdomain_check_fixed_bits(mm, x, one)
            && bzla_rng_flip_coin(&bzla->rng))
        {
          /* special case: s % x = 0: one is a simple solution */
          res = bzla_bv_copy(mm, one);
        }
        else
        {
          simple = bzla_bv_sub(mm, s, t); /* simplest solution: s - t */
          if (bzla_bvdomain_check_fixed_bits(mm, x, simple)
              && bzla_rng_flip_coin(&bzla->rng))
          {
            res = simple;
          }
          else
          {
            /* try to find some other factor within 10k iterations, else fall
             * back to using the simple solution */
            res = bzla_bvdomain_get_factor(mm, simple, x, t, 10000, &bzla->rng);
            assert(!res || bzla_bvdomain_check_fixed_bits(mm, x, res));
            if (res)
            {
              bzla_bv_free(mm, simple);
            }
            else
            {
              res = 0;
              if (bzla_bvdomain_check_fixed_bits(mm, x, simple))
              {
                res = simple;
              }
              assert(res || bzla_bvdomain_check_fixed_bits(mm, x, one));
              if (bzla_bv_is_zero(t)
                  && bzla_bvdomain_check_fixed_bits(mm, x, one)
                  && (!res || bzla_rng_flip_coin(&bzla->rng)))
              {
                res = bzla_bv_copy(mm, one);
                bzla_bv_free(mm, simple);
              }
            }
          }
        }
      }
      bzla_bv_free(mm, one);
    }
  }
  else
  {
    ones = bzla_bv_ones(mm, bw);
    if (bzla_bv_is_zero(s) || bzla_bv_compare(t, ones) == 0
        || (bzla_bvdomain_check_fixed_bits(mm, x, t)
            && bzla_rng_flip_coin(&bzla->rng)))
    {
      /* x % 0 = t: x = t
       * t = ones : s = 0, x = ones */
      assert(bzla_bvdomain_check_fixed_bits(mm, x, t));
      res = bzla_bv_copy(mm, t);
    }
    else
    {
      /* Pick x within range determined in is_inv, given as pi->res_x->lo for
       * the
       * lower bound and pi->res_x->hi for the upper bound (both inclusive). */
      BzlaBvDomainGenerator gen;
      if (pi->res_x)
      {
        assert(bzla_bv_compare(pi->res_x->lo, pi->res_x->hi) <= 0);
        res = bzla_bv_copy(mm, pi->res_x->lo);
        bzla_bvdomain_gen_init_range(
            mm, &bzla->rng, &gen, x, pi->res_x->lo, pi->res_x->hi);
      }
      else
      {
        res = bzla_bv_copy(mm, t);
        bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
      }
      assert(bzla_bvdomain_gen_has_next(&gen));
      for (cnt = 0; cnt < BZLA_PROPUTILS_GEN_MAX_RAND; cnt++)
      {
        bv  = bzla_bvdomain_gen_random(&gen);
        tmp = bzla_bv_urem(mm, bv, s);
        if (bzla_bv_compare(tmp, t) == 0)
        {
          bzla_bv_free(mm, res);
          res = bzla_bv_copy(mm, bv);
          bzla_bv_free(mm, tmp);
          break;
        }
        bzla_bv_free(mm, tmp);
      }
      bzla_bvdomain_gen_delete(&gen);
    }
    bzla_bv_free(mm, ones);
  }
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_urem, pi, res, "%");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_concat_const(Bzla *bzla, BzlaPropInfo *pi)
{
  return bzla_proputils_inv_concat(bzla, pi);
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_slice_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi->exp);
  assert(bzla_node_is_regular(pi->exp));
  assert(pi->target_value);
  assert(pi->pos_x == 0);
  assert(!bzla_node_is_bv_const(pi->exp->e[0]));
  assert(bzla_is_inv_slice(bzla, pi));
  assert(pi->bvd[0]);

  BzlaBitVector *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;

  t = pi->target_value;
  x = pi->bvd[0];
  assert(bzla_is_inv_slice_const(bzla, pi));

  res = bzla_proputils_inv_slice(bzla, pi);
  set_const_bits(bzla->mm, x, &res);
#ifndef NDEBUG
  uint32_t upper        = bzla_node_bv_slice_get_upper(pi->exp);
  uint32_t lower        = bzla_node_bv_slice_get_lower(pi->exp);
  BzlaMemMgr *mm        = bzla->mm;
  BzlaBitVector *tmpdbg = bzla_bv_slice(mm, res, upper, lower);
  assert(!bzla_bv_compare(tmpdbg, t));
  bzla_bv_free(mm, tmpdbg);
  char *str_t   = bzla_bv_to_char(mm, t);
  char *str_res = bzla_bv_to_char(mm, res);
  BZLALOG(3,
          "prop (xxxxx): %s: %s := %s[%d:%d]",
          bzla_util_node2string(pi->exp),
          str_t,
          str_res,
          lower,
          upper);
  bzla_mem_freestr(mm, str_t);
  bzla_mem_freestr(mm, str_res);
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: cond                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_cond_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi->exp);
  assert(bzla_node_is_regular(pi->exp));
  assert(pi->target_value);
  assert(pi->bv[0]);
  assert(pi->bv[1]);
  assert(pi->bv[2]);
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 2);
  assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));
  assert(pi->bvd[pi->pos_x]);

  int32_t pos_x;
  BzlaMemMgr *mm;
  BzlaBitVector *tmp, *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_cond);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  assert(bzla_is_inv_cond_const(bzla, pi));

  if ((pi->pos_x == 1 && bzla_bv_is_zero(pi->bv[0]))
      || (pi->pos_x == 2 && bzla_bv_is_one(pi->bv[0])))
  {
    /* return current assignment for disabled branch */
    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
  }
  else if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    if (pos_x == 0)
    {
      tmp = bzla_bv_ite(mm, x->lo, pi->bv[1], pi->bv[2]);
    }
    else if (pos_x == 1)
    {
      tmp = bzla_bv_ite(mm, pi->bv[0], x->lo, pi->bv[2]);
    }
    else
    {
      tmp = bzla_bv_ite(mm, pi->bv[0], pi->bv[1], x->lo);
    }
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pi->res_x)
  {
    assert(pos_x || pi->res_x);
    /* all non-random cases are determined in is_inv */
    assert(bzla_bvdomain_is_fixed(mm, pi->res_x));
    res = bzla_bv_copy(mm, pi->res_x->lo);
  }
  else
  {
    /* x random */
    BzlaBvDomainGenerator gen;
    bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
    assert(bzla_bvdomain_gen_has_next(&gen));
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
#ifndef NDEBUG
  char *str_res = bzla_bv_to_char(mm, res);
  char *str_t   = bzla_bv_to_char(bzla->mm, t);
  char *str_s0  = bzla_bv_to_char(mm, pi->bv[0]);
  char *str_s1  = bzla_bv_to_char(mm, pi->bv[1]);
  char *str_s2  = bzla_bv_to_char(mm, pi->bv[2]);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s ? %s : %s",
          pos_x,
          bzla_util_node2string(pi->exp),
          str_t,
          pos_x == 0 ? str_res : str_s0,
          pos_x == 1 ? str_res : str_s1,
          pos_x == 2 ? str_res : str_s2);
  bzla_mem_freestr(mm, str_t);
  bzla_mem_freestr(mm, str_res);
  bzla_mem_freestr(mm, str_s0);
  bzla_mem_freestr(mm, str_s1);
  bzla_mem_freestr(mm, str_s2);
#endif
  return res;
}

/* ========================================================================== */
/* Lookup tables.                                                             */
/* ========================================================================== */

static BzlaPropSelectPath kind_to_select_path[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = select_path_add,
    [BZLA_BV_AND_NODE]    = select_path_and,
    [BZLA_BV_CONCAT_NODE] = select_path_concat,
    [BZLA_BV_EQ_NODE]     = select_path_eq,
    [BZLA_BV_MUL_NODE]    = select_path_mul,
    [BZLA_BV_ULT_NODE]    = select_path_ult,
    [BZLA_BV_SLICE_NODE]  = select_path_slice,
    [BZLA_BV_SLL_NODE]    = select_path_sll,
    [BZLA_BV_SRL_NODE]    = select_path_srl,
    [BZLA_BV_UDIV_NODE]   = select_path_udiv,
    [BZLA_BV_UREM_NODE]   = select_path_urem,
    [BZLA_COND_NODE]      = select_path_cond,
};

static BzlaPropComputeValueFun kind_to_cons[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_proputils_cons_add,
    [BZLA_BV_AND_NODE]    = bzla_proputils_cons_and,
    [BZLA_BV_CONCAT_NODE] = bzla_proputils_cons_concat,
    [BZLA_BV_EQ_NODE]     = bzla_proputils_cons_eq,
    [BZLA_BV_MUL_NODE]    = bzla_proputils_cons_mul,
    [BZLA_BV_ULT_NODE]    = bzla_proputils_cons_ult,
    [BZLA_BV_SLICE_NODE]  = bzla_proputils_cons_slice,
    [BZLA_BV_SLL_NODE]    = bzla_proputils_cons_sll,
    [BZLA_BV_SRL_NODE]    = bzla_proputils_cons_srl,
    [BZLA_BV_UDIV_NODE]   = bzla_proputils_cons_udiv,
    [BZLA_BV_UREM_NODE]   = bzla_proputils_cons_urem,
    [BZLA_COND_NODE]      = bzla_proputils_cons_cond,
};

static BzlaPropComputeValueFun kind_to_cons_const[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_proputils_cons_add_const,
    [BZLA_BV_AND_NODE]    = bzla_proputils_cons_and_const,
    [BZLA_BV_CONCAT_NODE] = bzla_proputils_cons_concat_const,
    [BZLA_BV_EQ_NODE]     = bzla_proputils_cons_eq_const,
    [BZLA_BV_MUL_NODE]    = bzla_proputils_cons_mul_const,
    [BZLA_BV_ULT_NODE]    = bzla_proputils_cons_ult_const,
    [BZLA_BV_SLICE_NODE]  = bzla_proputils_cons_slice_const,
    [BZLA_BV_SLL_NODE]    = bzla_proputils_cons_sll_const,
    [BZLA_BV_SRL_NODE]    = bzla_proputils_cons_srl_const,
    [BZLA_BV_UDIV_NODE]   = bzla_proputils_cons_udiv_const,
    [BZLA_BV_UREM_NODE]   = bzla_proputils_cons_urem_const,
    [BZLA_COND_NODE]      = bzla_proputils_cons_cond_const,
};

static BzlaPropComputeValueFun kind_to_inv[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_proputils_inv_add,
    [BZLA_BV_AND_NODE]    = bzla_proputils_inv_and,
    [BZLA_BV_CONCAT_NODE] = bzla_proputils_inv_concat,
    [BZLA_BV_EQ_NODE]     = bzla_proputils_inv_eq,
    [BZLA_BV_MUL_NODE]    = bzla_proputils_inv_mul,
    [BZLA_BV_ULT_NODE]    = bzla_proputils_inv_ult,
    [BZLA_BV_SLICE_NODE]  = bzla_proputils_inv_slice,
    [BZLA_BV_SLL_NODE]    = bzla_proputils_inv_sll,
    [BZLA_BV_SRL_NODE]    = bzla_proputils_inv_srl,
    [BZLA_BV_UDIV_NODE]   = bzla_proputils_inv_udiv,
    [BZLA_BV_UREM_NODE]   = bzla_proputils_inv_urem,
    [BZLA_COND_NODE]      = bzla_proputils_inv_cond,
};

static BzlaPropComputeValueFun kind_to_inv_const[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_proputils_inv_add_const,
    [BZLA_BV_AND_NODE]    = bzla_proputils_inv_and_const,
    [BZLA_BV_CONCAT_NODE] = bzla_proputils_inv_concat_const,
    [BZLA_BV_EQ_NODE]     = bzla_proputils_inv_eq_const,
    [BZLA_BV_MUL_NODE]    = bzla_proputils_inv_mul_const,
    [BZLA_BV_ULT_NODE]    = bzla_proputils_inv_ult_const,
    [BZLA_BV_SLICE_NODE]  = bzla_proputils_inv_slice_const,
    [BZLA_BV_SLL_NODE]    = bzla_proputils_inv_sll_const,
    [BZLA_BV_SRL_NODE]    = bzla_proputils_inv_srl_const,
    [BZLA_BV_UDIV_NODE]   = bzla_proputils_inv_udiv_const,
    [BZLA_BV_UREM_NODE]   = bzla_proputils_inv_urem_const,
    [BZLA_COND_NODE]      = bzla_proputils_inv_cond_const,
};

static BzlaPropIsInvFun kind_to_is_inv[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = 0,  // always invertible
    [BZLA_BV_AND_NODE]    = bzla_is_inv_and,
    [BZLA_BV_CONCAT_NODE] = bzla_is_inv_concat,
    [BZLA_BV_EQ_NODE]     = 0,  // always invertible
    [BZLA_BV_MUL_NODE]    = bzla_is_inv_mul,
    [BZLA_BV_ULT_NODE]    = bzla_is_inv_ult,
    [BZLA_BV_SLICE_NODE]  = bzla_is_inv_slice,
    [BZLA_BV_SLL_NODE]    = bzla_is_inv_sll,
    [BZLA_BV_SRL_NODE]    = bzla_is_inv_srl,
    [BZLA_BV_UDIV_NODE]   = bzla_is_inv_udiv,
    [BZLA_BV_UREM_NODE]   = bzla_is_inv_urem,
    [BZLA_COND_NODE]      = bzla_is_inv_cond,
};

static BzlaPropIsInvFun kind_to_is_inv_const[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_is_inv_add_const,
    [BZLA_BV_AND_NODE]    = bzla_is_inv_and_const,
    [BZLA_BV_CONCAT_NODE] = bzla_is_inv_concat_const,
    [BZLA_BV_EQ_NODE]     = bzla_is_inv_eq_const,
    [BZLA_BV_MUL_NODE]    = bzla_is_inv_mul_const,
    [BZLA_BV_ULT_NODE]    = bzla_is_inv_ult_const,
    [BZLA_BV_SLICE_NODE]  = bzla_is_inv_slice_const,
    [BZLA_BV_SLL_NODE]    = bzla_is_inv_sll_const,
    [BZLA_BV_SRL_NODE]    = bzla_is_inv_srl_const,
    [BZLA_BV_UDIV_NODE]   = bzla_is_inv_udiv_const,
    [BZLA_BV_UREM_NODE]   = bzla_is_inv_urem_const,
    [BZLA_COND_NODE]      = bzla_is_inv_cond_const,
};

/* ========================================================================== */
/* Propagation move                                                           */
/* ========================================================================== */

/**
 * Record the conflict and determine if it is recoverable.
 *
 * A conflict is always recoverable if given child 'e' is non-const.
 * If we enforce to always move, even on non-recoverable conflicts (i.e.,
 * option BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT is false), we still interpret the
 * conflict as recoverable.
 */
static bool
record_conflict(Bzla *bzla,
                BzlaNode *exp,
                BzlaBitVector *t,
                BzlaBitVector *s[3],
                uint32_t idx_x,
                bool is_recoverable)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(t);
  (void) s;

  BzlaMemMgr *mm;
  uint32_t idx_s = 0;

  mm = bzla->mm;

  if (bzla_node_is_cond(exp))
  {
    is_recoverable = idx_x != 0 || !bzla_node_is_bv_const(exp->e[1])
                     || !bzla_node_is_bv_const(exp->e[2]);
  }
  else
  {
    if (exp->arity > 1)
    {
      idx_s = idx_x ? 0 : 1;
    }
    is_recoverable = !bzla_node_is_bv_const(exp->e[idx_s]);
  }
#ifndef NDEBUG
  char *str_s0, *str_s1;
  char *str_t = bzla_bv_to_char(mm, t);
  char *str_o = 0;
  if (bzla_node_is_cond(exp))
  {
    assert(s[1]);
    BZLALOG(2, "");
    if (idx_x == 0)
    {
      str_s0 = bzla_bv_to_char(mm, s[1]);
      str_s1 = bzla_bv_to_char(mm, s[2]);
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := x ? %s : %s",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0,
              str_s1);
    }
    else if (idx_x == 1)
    {
      str_s0 = bzla_bv_to_char(mm, s[0]);
      str_s1 = bzla_bv_to_char(mm, s[2]);
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := %s ? x : %s",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0,
              str_s1);
    }
    else
    {
      str_s0 = bzla_bv_to_char(mm, s[0]);
      str_s1 = bzla_bv_to_char(mm, s[1]);
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := %s ? %s : x",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0,
              str_s1);
    }
    bzla_mem_freestr(mm, str_s0);
    bzla_mem_freestr(mm, str_s1);
  }
  else if (bzla_node_is_bv_slice(exp))
  {
    BZLALOG(2,
            "%srecoverable CONFLICT (@%d): %s := x[%u:%u]",
            is_recoverable ? "" : "non-",
            bzla_node_get_id(exp),
            str_t,
            bzla_node_bv_slice_get_upper(exp),
            bzla_node_bv_slice_get_lower(exp));
  }
  else
  {
    idx_s  = idx_x ? 0 : 1;
    str_s0 = bzla_bv_to_char(mm, s[idx_s]);
    switch (exp->kind)
    {
      case BZLA_BV_AND_NODE: str_o = "&"; break;
      case BZLA_BV_ULT_NODE: str_o = "<"; break;
      case BZLA_BV_SLL_NODE: str_o = "<<"; break;
      case BZLA_BV_SRL_NODE: str_o = ">>"; break;
      case BZLA_BV_MUL_NODE: str_o = "*"; break;
      case BZLA_BV_UDIV_NODE: str_o = "/"; break;
      case BZLA_BV_UREM_NODE: str_o = "%"; break;
      case BZLA_BV_ADD_NODE: str_o = "+"; break;
      case BZLA_BV_EQ_NODE: str_o = "="; break;
      default: assert(exp->kind == BZLA_BV_CONCAT_NODE); str_o = "o";
    }
    BZLALOG(2, "");
    if (idx_x)
    {
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := %s %s x",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0,
              str_o);
    }
    else
    {
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := x %s %s",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_o,
              str_s0);
    }
    bzla_mem_freestr(mm, str_s0);
  }
  bzla_mem_freestr(mm, str_t);
#endif
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
    BzlaPropSolver *slv    = BZLA_PROP_SOLVER(bzla);
    uint32_t prop_entailed = bzla_opt_get(bzla, BZLA_OPT_PROP_ENTAILED);
    if (is_recoverable)
    {
      slv->stats.rec_conf += 1;
      /* recoverable conflict, push entailed propagation */
      if (prop_entailed != BZLA_PROP_ENTAILED_OFF)
      {
        BzlaPropEntailInfo prop = {exp, bzla_bv_copy(mm, t), 0};
        assert(exp->arity == 2 || exp->arity == 3);
        if (exp->arity == 2)
        {
          prop.idx_x = idx_x ? 0 : 1;
        }
        else
        {
          if (idx_x == 0)
          {
            prop.idx_x = bzla_rng_flip_coin(&bzla->rng) ? 1 : 2;
          }
          else if (idx_x == 1)
          {
            prop.idx_x = bzla_rng_flip_coin(&bzla->rng) ? 0 : 2;
          }
          else
          {
            prop.idx_x = bzla_rng_flip_coin(&bzla->rng) ? 0 : 1;
          }
        }
        if (BZLA_EMPTY_STACK(slv->toprop)
            || prop_entailed == BZLA_PROP_ENTAILED_ALL)
        {
          BZLA_PUSH_STACK(slv->toprop, prop);
        }
        else if (prop_entailed == BZLA_PROP_ENTAILED_LAST)
        {
          assert(BZLA_COUNT_STACK(slv->toprop) == 1);
          BZLA_POKE_STACK(slv->toprop, 0, prop);
        }
        else
        {
          bzla_bv_free(bzla->mm, prop.bvexp);
        }
        assert(prop_entailed == BZLA_PROP_ENTAILED_ALL
               || BZLA_COUNT_STACK(slv->toprop) == 1);
      }
      /* fix counter since we always increase the counter, even in the conflict
       * case (except for slice and cond, where inv = cons)*/
      if (!bzla_node_is_bv_slice(exp) && !bzla_node_is_bv_cond(exp))
        slv->stats.props_inv -= 1;
    }
    else
    {
      slv->stats.non_rec_conf += 1;
      if (prop_entailed)
      {
        /* non-recoverable conflict, entailed propagations are thus invalid */
        bzla_proputils_reset_prop_info_stack(mm, &slv->toprop);
      }
    }
  }
  else
  {
    if (is_recoverable)
      BZLA_SLS_SOLVER(bzla)->stats.move_prop_rec_conf += 1;
    else
      BZLA_SLS_SOLVER(bzla)->stats.move_prop_non_rec_conf += 1;
  }

  return is_recoverable
         || !bzla_opt_get(bzla, BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT);
}

/* -------------------------------------------------------------------------- */

static bool
is_sign_extend(Bzla *bzla, BzlaNode *n)
{
  assert(bzla_node_is_regular(n));

  uint32_t msb;
  BzlaNode *ite, *t;

  if (!bzla_node_is_bv_concat(n))
  {
    return false;
  }

  ite = n->e[0];
  t   = n->e[1];
  msb = bzla_node_bv_get_width(bzla, t) - 1;

  if (bzla_node_is_inverted(ite) || !bzla_node_is_cond(ite)
      || !bzla_node_is_bv_slice(ite->e[0]) || bzla_node_is_inverted(ite->e[0])
      || ite->e[0]->e[0] != t || bzla_node_bv_slice_get_upper(ite->e[0]) != msb
      || bzla_node_bv_slice_get_lower(ite->e[0]) != msb
      || !bzla_node_is_bv_const_ones(bzla, ite->e[1])
      || !bzla_node_is_bv_const_zero(bzla, ite->e[2]))
  {
    return false;
  }

  return true;
}

uint64_t
bzla_proputils_select_move_prop(Bzla *bzla,
                                BzlaNode *root,
                                BzlaBitVector *bvroot,
                                int32_t pos_x,
                                BzlaNode **input,
                                BzlaBitVector **assignment)
{
  assert(bzla);
  assert(root);
  assert(bvroot);

  bool is_inv, pick_inv, has_fixed_bits;
  int32_t i, nconst;
  uint64_t nprops;
  BzlaNode *cur, *real_cur;
  BzlaIntHashTable *domains;
  BzlaHashTableData *d;
  BzlaBitVector *bv_s[3] = {0, 0, 0}, *bv_t, *bv_s_new, *tmp;
  BzlaMemMgr *mm;
  uint32_t opt_prop_prob_use_inv_value;
  uint32_t opt_prop_const_bits;
  bool opt_skip_no_progress;
  bool is_sext;
  BzlaPropInfo pi;

  BzlaPropSelectPath select_path;
  BzlaPropIsInvFun is_inv_fun;

#ifndef NBZLALOG
  char *a;
  uint32_t nrecconf_prev, nnonrecconf_prev, nrecconf, nnonrecconf;
  uint32_t ncons = 0;
#endif

  mm = bzla->mm;

  *input      = 0;
  *assignment = 0;
  nprops      = 0;
  domains     = 0;

  opt_prop_prob_use_inv_value =
      bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE);
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS);
  opt_skip_no_progress =
      bzla_opt_get(bzla, BZLA_OPT_PROP_SKIP_NO_PROGRESS) != 0;

#ifndef NBZLALOG
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
    nrecconf_prev    = BZLA_PROP_SOLVER(bzla)->stats.rec_conf;
    nnonrecconf_prev = BZLA_PROP_SOLVER(bzla)->stats.non_rec_conf;
  }
  else
  {
    assert(bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
    nrecconf_prev    = BZLA_SLS_SOLVER(bzla)->stats.move_prop_rec_conf;
    nnonrecconf_prev = BZLA_SLS_SOLVER(bzla)->stats.move_prop_non_rec_conf;
  }
#endif

  domains = BZLA_PROP_SOLVER(bzla)->domains;
  assert(domains);

  tmp = (BzlaBitVector *) bzla_model_get_bv(bzla, root);
  if (!bzla_bv_compare(bvroot, tmp))
  {
    if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      BZLA_PROP_SOLVER(bzla)->stats.fixed_conf++;
    goto DONE;
  }

  cur  = root;
  bv_t = bzla_bv_copy(bzla->mm, bvroot);

  for (;;)
  {
    real_cur = bzla_node_real_addr(cur);

#ifndef NDEBUG
    if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND && opt_prop_const_bits)
    {
      BzlaPropSolver *slv = BZLA_PROP_SOLVER(bzla);
      assert(slv->domains);
      assert(bzla_hashint_map_contains(slv->domains, real_cur->id));
      BzlaBvDomain *d =
          bzla_hashint_map_get(slv->domains, real_cur->id)->as_ptr;
      assert(bzla_bv_get_width(d->hi)
             == bzla_node_bv_get_width(bzla, real_cur));
      assert(bzla_bv_get_width(d->lo)
             == bzla_node_bv_get_width(bzla, real_cur));
      if (opt_prop_const_bits
          && !bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_DOMAINS))
      {
        assert(real_cur->av);
        uint32_t bw = real_cur->av->width;
        for (uint32_t j = 0; j < bw; j++)
        {
          uint32_t k = bw - 1 - j;
          if (bzla_aig_is_true(real_cur->av->aigs[j]))
            assert(bzla_bvdomain_is_fixed_bit_true(d, k));
          else if (bzla_aig_is_false(real_cur->av->aigs[j]))
            assert(bzla_bvdomain_is_fixed_bit_false(d, k));
          else
            assert(!bzla_bvdomain_is_fixed_bit(d, k));
        }
      }
    }
#endif

    if (bzla_node_is_bv_var(cur))
    {
      *input      = real_cur;
      *assignment = bzla_node_is_inverted(cur) ? bzla_bv_not(bzla->mm, bv_t)
                                               : bzla_bv_copy(bzla->mm, bv_t);
      break;
    }
    else if (bzla_node_is_bv_const(cur))
    {
      break;
    }
    else
    {
      assert(!bzla_node_is_bv_const(cur));

      if (bzla_node_is_inverted(cur))
      {
        tmp  = bv_t;
        bv_t = bzla_bv_not(bzla->mm, tmp);
        bzla_bv_free(bzla->mm, tmp);
      }

      /* Reset propagation info struct. */
      memset(&pi, 0, sizeof(BzlaPropInfo));

      /* check if all paths are const, if yes -> conflict */
      for (i = 0, nconst = 0; i < real_cur->arity; i++)
      {
        bv_s[i]  = (BzlaBitVector *) bzla_model_get_bv(bzla, real_cur->e[i]);
        pi.bv[i] = bv_s[i];
        if (bzla_node_is_bv_const(real_cur->e[i])) nconst += 1;
      }
      if (nconst > real_cur->arity - 1) break;
      /* additionally, for ite, if condition and enabled branch are const
       * -> conflict */
      if (bzla_node_is_cond(real_cur) && bzla_node_is_bv_const(real_cur->e[0])
          && (bzla_node_is_bv_const(
              real_cur == bzla->true_exp ? real_cur->e[1] : real_cur->e[2])))
      {
        break;
      }

#ifndef NBZLALOG
      a = bzla_bv_to_char(bzla->mm, bv_t);
      BZLALOG(2, "");
      BZLALOG(2, "propagate: %s", a);
      bzla_mem_freestr(bzla->mm, a);
#endif

      is_sext = is_sign_extend(bzla, real_cur);

      pi.exp          = real_cur;
      pi.res_x        = 0;
      pi.target_value = bv_t;

      /* select path */
      if (is_sext)
      {
        pi.pos_x = 1;
        pos_x    = 1;
      }
      else
      {
        select_path = kind_to_select_path[real_cur->kind];
        if (pos_x == -1) pos_x = select_path(bzla, &pi);
      }
      assert(pi.pos_x == pos_x);

      assert(pos_x >= 0);
      assert(pos_x < real_cur->arity);

#ifndef NDEBUG
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        BzlaPropEntailInfo prop = {
            real_cur, bzla_bv_copy(bzla->mm, bv_t), pos_x};
        BZLA_PUSH_STACK(BZLA_PROP_SOLVER(bzla)->prop_path, prop);
      }
#endif

      /* Initialize domains. */
      has_fixed_bits = false;
      if (opt_prop_const_bits)
      {
        assert(domains);
        d = bzla_hashint_map_get(domains, bzla_node_get_id(real_cur->e[pos_x]));
        assert(d);
        assert(d->as_ptr);

        has_fixed_bits = bzla_bvdomain_has_fixed_bits(mm, d->as_ptr);

        for (i = 0; i < real_cur->arity; ++i)
        {
          d = bzla_hashint_map_get(domains, bzla_node_get_id(real_cur->e[i]));
          assert(d);
          assert(d->as_ptr);
          pi.bvd[i] = d->as_ptr;
        }
      }

      /* 1) check invertibility
       *    -> if not invertible, fall back to consistent value computation
       * 2) if not invertible, enforce consistent value computation
       * 3) if consistent value computation is selected or enforced,
       *    compute consistent value
       * 4) else compute inverse value
       */

      BzlaPropComputeValueFun inv_value_fun, cons_value_fun, compute_value_fun;

      if (has_fixed_bits)
      {
        if (is_sext)
        {
          is_inv_fun     = bzla_is_inv_sign_extend_const;
          cons_value_fun = bzla_proputils_cons_sign_extend;
          inv_value_fun  = bzla_proputils_inv_sign_extend_const;
        }
        else
        {
          is_inv_fun     = kind_to_is_inv_const[real_cur->kind];
          cons_value_fun = kind_to_cons_const[real_cur->kind];
          inv_value_fun  = kind_to_inv_const[real_cur->kind];
        }
      }
      else
      {
        if (is_sext)
        {
          is_inv_fun     = bzla_is_inv_sign_extend;
          cons_value_fun = bzla_proputils_cons_sign_extend;
          inv_value_fun  = bzla_proputils_inv_sign_extend;
        }
        else
        {
          is_inv_fun     = kind_to_is_inv[real_cur->kind];
          cons_value_fun = kind_to_cons[real_cur->kind];
          inv_value_fun  = kind_to_inv[real_cur->kind];
        }
      }

      /* Determine if there exists an inverse value. */
      is_inv = true;
      if (is_inv_fun)
      {
        assert(!opt_prop_const_bits || pi.bvd[pi.pos_x]);
        is_inv = is_inv_fun(bzla, &pi);
      }

      if (!is_inv)
      {
        /* not invertible counts as conflict */
        if (!record_conflict(bzla, real_cur, bv_t, bv_s, pos_x, true))
        {
          /* non-recoverable conflict */
          if (pi.res_x)
          {
            bzla_bvdomain_free(mm, pi.res_x);
            pi.res_x = 0;
          }
          break;
        }
      }

      /* we either select a consistent or inverse value
       * as path assignment, depending on the given probability p
       * -> if pick_inv then inverse else consistent */
      pick_inv =
          bzla_rng_pick_with_prob(&bzla->rng, opt_prop_prob_use_inv_value);
#ifndef NBZLALOG
      if (!pick_inv) ncons += 1;
#endif

      /* compute new assignment */
      compute_value_fun = pick_inv && is_inv ? inv_value_fun : cons_value_fun;
      bv_s_new          = compute_value_fun(bzla, &pi);

      if (pi.res_x)
      {
        bzla_bvdomain_free(mm, pi.res_x);
        pi.res_x = 0;
      }

      if (!bv_s_new)
      {
        (void) record_conflict(bzla, real_cur, bv_t, bv_s, pos_x, false);
        break;
      }
#ifndef NBZLALOG
      a = bzla_bv_to_char(bzla->mm, bv_s_new);
      BZLALOG(2, "");
      BZLALOG(
          2, "%s value: %s", pick_inv && is_inv ? "inverse" : "consistent", a);
      bzla_mem_freestr(bzla->mm, a);
#endif

      if (opt_skip_no_progress && !bzla_bv_compare(bv_s_new, bv_s[pos_x]))
      {
        if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
        {
          BZLA_PROP_SOLVER(bzla)->stats.moves_skipped++;
        }
        bzla_bv_free(bzla->mm, bv_s_new);
        break;
      }

      /* propagate down */
      bzla_bv_free(bzla->mm, bv_t);
      bv_t = bv_s_new;
      cur  = real_cur->e[pos_x];
      assert(bzla_hashint_map_contains(domains, bzla_node_get_id(cur)));
      assert(bzla_hashint_map_get(domains, bzla_node_get_id(cur))),
          assert(bzla_bvdomain_check_fixed_bits(
              bzla->mm,
              bzla_hashint_map_get(domains, bzla_node_get_id(cur))->as_ptr,
              bv_t));

      nprops += 1;
      pos_x = -1;
    }
  }

  bzla_bv_free(bzla->mm, bv_t);

DONE:
#ifndef NBZLALOG
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
    nrecconf    = BZLA_PROP_SOLVER(bzla)->stats.rec_conf;
    nnonrecconf = BZLA_PROP_SOLVER(bzla)->stats.non_rec_conf;
  }
  else
  {
    assert(bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
    nrecconf    = BZLA_SLS_SOLVER(bzla)->stats.move_prop_rec_conf;
    nnonrecconf = BZLA_SLS_SOLVER(bzla)->stats.move_prop_non_rec_conf;
  }
  nrecconf -= nrecconf_prev;
  nnonrecconf -= nnonrecconf_prev;
  ncons += nrecconf;
  BZLALOG(1, "");
  BZLALOG(1, "propagation path:");
  BZLALOG(1, "    length: %u", nprops);
  BZLALOG(1, "        inverse value props: %u", nprops - ncons);
  BZLALOG(1, "        consistent value props: %u", ncons);
  BZLALOG(1, "    conflicts: %u", nrecconf + nnonrecconf);
  BZLALOG(1, "        recoverable conflicts: %u", nrecconf);
  BZLALOG(1, "        non-recoverable conflicts: %u", nnonrecconf);
#endif
  return nprops;
}

/* ========================================================================== */

void
bzla_proputils_clone_prop_info_stack(BzlaMemMgr *mm,
                                     BzlaPropEntailInfoStack *stack,
                                     BzlaPropEntailInfoStack *res,
                                     BzlaNodeMap *exp_map)
{
  assert(mm);
  assert(stack);
  assert(res);
  assert(exp_map);

  uint32_t i;
  int32_t cloned_idx_x;
  BzlaNode *cloned_exp;
  BzlaBitVector *cloned_bvexp;

  BZLA_INIT_STACK(mm, *res);
  assert(BZLA_SIZE_STACK(*stack) || !BZLA_COUNT_STACK(*stack));
  if (BZLA_SIZE_STACK(*stack))
  {
    BZLA_NEWN(mm, res->start, BZLA_SIZE_STACK(*stack));
    res->top = res->start;
    res->end = res->start + BZLA_SIZE_STACK(*stack);

    for (i = 0; i < BZLA_COUNT_STACK(*stack); i++)
    {
      assert(BZLA_PEEK_STACK(*stack, i).exp);
      cloned_exp = bzla_nodemap_mapped(exp_map, BZLA_PEEK_STACK(*stack, i).exp);
      assert(cloned_exp);
      assert(BZLA_PEEK_STACK(*stack, i).bvexp);
      cloned_bvexp = bzla_bv_copy(mm, BZLA_PEEK_STACK(*stack, i).bvexp);
      cloned_idx_x = BZLA_PEEK_STACK(*stack, i).idx_x;
      assert(cloned_idx_x == 0 || cloned_idx_x == 1);
      BzlaPropEntailInfo cloned_prop = {cloned_exp, cloned_bvexp, cloned_idx_x};
      BZLA_PUSH_STACK(*res, cloned_prop);
    }
  }
  assert(BZLA_COUNT_STACK(*stack) == BZLA_COUNT_STACK(*res));
  assert(BZLA_SIZE_STACK(*stack) == BZLA_SIZE_STACK(*res));
}

void
bzla_proputils_reset_prop_info_stack(BzlaMemMgr *mm,
                                     BzlaPropEntailInfoStack *stack)
{
  assert(mm);
  assert(stack);

  while (!BZLA_EMPTY_STACK(*stack))
  {
    BzlaPropEntailInfo prop = BZLA_POP_STACK(*stack);
    bzla_bv_free(mm, prop.bvexp);
  }
  BZLA_RESET_STACK(*stack);
}

/* ========================================================================== */

void
bzla_propinfo_set_result(Bzla *bzla, BzlaPropInfo *pi, BzlaBvDomain *res)
{
  assert(bzla);
  assert(pi);
  if (pi->res_x)
  {
    bzla_bvdomain_free(bzla->mm, pi->res_x);
  }
  pi->res_x = res;
}
