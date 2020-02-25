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
#include "utils/bzlautil.h"

/* ========================================================================== */

typedef int32_t (*BzlaPropSelectPath)(Bzla *,
                                      BzlaNode *,
                                      BzlaBitVector *,
                                      BzlaBitVector **);

/* ========================================================================== */

/**
 * Create a bit-vector with all bits that are const bits in domain d_res_x
 * set to their const value, and all other bits set to their value in res_x.
 */
static BzlaBitVector *
set_const_bits(BzlaMemMgr *mm, BzlaBvDomain *d_res_x, BzlaBitVector *res_x)
{
  assert(d_res_x);
  assert(res_x);
  BzlaBitVector *tmp = bzla_bv_and(mm, d_res_x->hi, res_x);
  BzlaBitVector *res = bzla_bv_or(mm, d_res_x->lo, tmp);
  bzla_bv_free(mm, tmp);
  return res;
}

/* ========================================================================== */
/* Path selection (for down-propagation)                                      */
/* ========================================================================== */

#ifndef NBZLALOG
static void
select_path_log(Bzla *bzla, BzlaNode *exp, BzlaBitVector *s[], uint32_t idx_x)
{
  exp = bzla_node_real_addr(exp);
  char *a;
  BzlaMemMgr *mm = bzla->mm;

  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(exp));

  for (size_t i = 0; i < exp->arity; i++)
  {
    a = bzla_bv_to_char(mm, s[i]);
    BZLALOG(
        2, "       e[%zu]: %s (%s)", i, bzla_util_node2string(exp->e[i]), a);
    bzla_mem_freestr(mm, a);
  }

  BZLALOG(2, "    * chose: %u", idx_x);
  if (BZLA_PROP_SOLVER(bzla)->domains)
  {
    BzlaHashTableData *d = bzla_hashint_map_get(
        BZLA_PROP_SOLVER(bzla)->domains, bzla_node_get_id(exp->e[idx_x]));
    if (d)
    {
      BZLALOG(2, "    * domain: %s", bzla_bvdomain_to_str(d->as_ptr));
    }
  }
}
#endif

static int32_t
select_path_non_const(BzlaNode *exp)
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
select_path_random(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  int32_t idx_x = (int32_t) bzla_rng_pick_rand(&bzla->rng, 0, exp->arity - 1);
  assert(!bzla_node_is_bv_const(exp->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_add(Bzla *bzla, BzlaNode *add, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(t);
  assert(s);

  (void) t;
  (void) s;

  int32_t idx_x;

  idx_x = select_path_non_const(add);
  if (idx_x == -1) idx_x = select_path_random(bzla, add);
  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, add, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(add->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_and(Bzla *bzla, BzlaNode *and, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(t);
  assert(s);

  uint32_t opt;
  int32_t i, idx_x;
  BzlaBitVector *tmp;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  idx_x = select_path_non_const(and);

  if (idx_x == -1)
  {
    opt = bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL);

    if (opt == BZLA_PROP_PATH_SEL_RANDOM)
    {
      idx_x = select_path_random(bzla, and);
    }
    else if (bzla_node_bv_get_width(bzla, and) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < and->arity; i++)
        if (bzla_bv_is_zero(s[i])) idx_x = idx_x == -1 ? i : -1;
      if (idx_x == -1) idx_x = select_path_random(bzla, and);
    }
    else if (opt == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* 1) all bits set in t must be set in both inputs, but
       * 2) all bits NOT set in t can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < and->arity; i++)
      {
        tmp = bzla_bv_and(mm, t, s[i]);
        if (bzla_bv_compare(tmp, t)) idx_x = idx_x == -1 ? i : -1;
        bzla_bv_free(mm, tmp);
      }
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, and);
  }

  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, and, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(and->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_eq(Bzla *bzla, BzlaNode *eq, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(t);
  assert(s);

  (void) t;
  (void) s;

  int32_t idx_x;
  idx_x = select_path_non_const(eq);
  if (idx_x == -1) idx_x = select_path_random(bzla, eq);
  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, eq, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(eq->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_ult(Bzla *bzla, BzlaNode *ult, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(t);
  assert(s);

  int32_t idx_x;
  BzlaBitVector *ones;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  idx_x = select_path_non_const(ult);

  if (idx_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      if (bzla_bv_is_one(t))
      {
        /* 1...1 < s[1] */
        if (!bzla_bv_compare(s[0], ones)) idx_x = 0;
        /* s[0] < 0 */
        if (bzla_bv_is_zero(s[1])) idx_x = idx_x == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, ones);
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, ult);
  }

  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, ult, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(ult->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_sll(Bzla *bzla, BzlaNode *sll, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(t);
  assert(s);

  int32_t idx_x;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp;
  BzlaMemMgr *mm;

  idx_x = select_path_non_const(sll);

  mm = bzla->mm;
  bw = bzla_bv_get_width(t);
  assert(bzla_bv_get_width(s[0]) == bw);
  assert(bzla_bv_get_width(s[1]) == bw);

  if (idx_x == -1)
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
          idx_x = 1;
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
        idx_x = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of LSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(t, i))
          {
            idx_x = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(s[0], i) != bzla_bv_get_bit(t, j + i))
          {
            idx_x = idx_x == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, sll);
  }
DONE:
  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, sll, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(sll->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_srl(Bzla *bzla, BzlaNode *srl, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(t);
  assert(s);

  int32_t idx_x;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp;
  BzlaMemMgr *mm;

  idx_x = select_path_non_const(srl);

  mm = bzla->mm;
  bw = bzla_bv_get_width(t);
  assert(bzla_bv_get_width(s[0]) == bw);
  assert(bzla_bv_get_width(s[1]) == bw);

  if (idx_x == -1)
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
          idx_x = 1;
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
        idx_x = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of MSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(t, bw - 1 - i))
          {
            idx_x = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(s[0], bw - 1 - i)
              != bzla_bv_get_bit(t, bw - 1 - (j + i)))
          {
            idx_x = idx_x == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, srl);
  }
DONE:
  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, srl, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(srl->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_mul(Bzla *bzla, BzlaNode *mul, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(t);
  assert(s);

  uint32_t ctz_bvmul;
  int32_t idx_x, lsb_s0, lsb_s1;
  bool iszero_s0, iszero_s1;

  idx_x = select_path_non_const(mul);

  if (idx_x == -1)
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
        if (iszero_s0) idx_x = 0;
        if (iszero_s1) idx_x = idx_x == -1 ? 1 : -1;
      }
      /* t is odd but either s[0] or s[1] are even */
      else if (bzla_bv_get_bit(t, 0) && (!lsb_s0 || !lsb_s1))
      {
        if (!lsb_s0) idx_x = 0;
        if (!lsb_s1) idx_x = idx_x == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in t < number of 0-LSBs in s[0|1] */
      else
      {
        ctz_bvmul = bzla_bv_get_num_trailing_zeros(t);
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(s[0])) idx_x = 0;
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(s[1]))
          idx_x = idx_x == -1 ? 1 : -1;
      }
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, mul);
  }
  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, mul, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(mul->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_udiv(Bzla *bzla,
                 BzlaNode *udiv,
                 BzlaBitVector *t,
                 BzlaBitVector **s)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(t);
  assert(s);

  int32_t idx_x, cmp_udiv_max;
  BzlaBitVector *ones, *up, *lo, *tmp;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  idx_x = select_path_non_const(udiv);

  if (idx_x == -1)
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
        idx_x = 1;
      else
      {
        /* 1...1 / x = 0 -> choose x */
        if (bzla_bv_is_zero(t) && !bzla_bv_compare(s[0], ones)) idx_x = 0;
        /* s[0] < t -> choose x */
        else if (bzla_bv_compare(s[0], t) < 0)
          idx_x = 0;
        else
        {
          up  = bzla_bv_udiv(mm, s[0], t);
          lo  = bzla_bv_inc(mm, t);
          tmp = bzla_bv_udiv(mm, s[0], lo);
          bzla_bv_free(mm, lo);
          lo = bzla_bv_inc(mm, tmp);

          if (bzla_bv_compare(lo, up) > 0) idx_x = 0;
          bzla_bv_free(mm, up);
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, tmp);
        }

        /* x / 0 != 1...1 -> choose x */
        if (bzla_bv_is_zero(s[1]) || bzla_bv_is_umulo(mm, s[1], t))
          idx_x = idx_x == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, ones);
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, udiv);
  }

  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, udiv, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(udiv->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_urem(Bzla *bzla,
                 BzlaNode *urem,
                 BzlaBitVector *t,
                 BzlaBitVector **s)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(t);
  assert(s);

  int32_t idx_x;
  BzlaBitVector *ones, *sub, *tmp;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  idx_x = select_path_non_const(urem);

  if (idx_x == -1)
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
        if (!bzla_bv_is_zero(s[1])) idx_x = 1;
        if (bzla_bv_compare(s[0], ones)) idx_x = idx_x == -1 ? 0 : -1;
      }
      /* t > 0 and s[1] = 1 */
      else if (!bzla_bv_is_zero(t) && bzla_bv_is_one(s[1]))
      {
        idx_x = 1;
      }
      /* 0 < s[1] <= t */
      else if (!bzla_bv_is_zero(s[1]) && bzla_bv_compare(s[1], t) <= 0)
      {
        idx_x = idx_x == -1 ? 1 : -1;
      }
      /* s[0] < t or
       * s[0] > t and s[0] - t <= t or
       *                 and s[0] - 1 = t */
      else if (bzla_bv_compare(s[0], t) < 0
               || (bzla_bv_compare(s[0], t) > 0
                   && (bzla_bv_compare(sub, t) <= 0
                       || !bzla_bv_compare(tmp, t))))
      {
        idx_x = 0;
      }

      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, ones);
      bzla_bv_free(mm, sub);
    }

    if (idx_x == -1) idx_x = select_path_random(bzla, urem);
  }

  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, urem, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(urem->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_concat(Bzla *bzla,
                   BzlaNode *concat,
                   BzlaBitVector *t,
                   BzlaBitVector **s)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(t);
  assert(s);

  int32_t idx_x;
  uint32_t bw_t;
  BzlaBitVector *tmp;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  idx_x = select_path_non_const(concat);

  if (idx_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* s[0] o s[1] = t
       * -> s[0] resp. s[1] must match with t */
      bw_t = bzla_bv_get_width(t);
      tmp  = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bzla_bv_get_width(s[0]));
      if (bzla_bv_compare(tmp, s[0])) idx_x = 0;
      bzla_bv_free(mm, tmp);
      tmp = bzla_bv_slice(mm, t, bzla_bv_get_width(s[1]) - 1, 0);
      if (bzla_bv_compare(tmp, s[1])) idx_x = idx_x == -1 ? 1 : -1;
      bzla_bv_free(mm, tmp);
    }

    if (idx_x == -1) idx_x = select_path_random(bzla, concat);
  }

  assert(idx_x >= 0);
#ifndef NBZLALOG
  select_path_log(bzla, concat, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(concat->e[idx_x]));
  return idx_x;
}

static int32_t
select_path_slice(Bzla *bzla,
                  BzlaNode *slice,
                  BzlaBitVector *t,
                  BzlaBitVector **s)
{
  assert(bzla);
  assert(slice);
  assert(bzla_node_is_regular(slice));
  assert(t);
  assert(s);

  assert(!bzla_node_is_bv_const(slice->e[0]));

  (void) bzla;
  (void) slice;
  (void) t;
  (void) s;
#ifndef NBZLALOG
  select_path_log(bzla, slice, s, 0);
#endif

  return 0;
}

static int32_t
select_path_cond(Bzla *bzla,
                 BzlaNode *cond,
                 BzlaBitVector *t,
                 BzlaBitVector **s)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(t);
  assert(s);

  bool is_const_e1, is_const_e2;
  int32_t idx_x, *delta;
  uint32_t *prob, *nflips_cond;
  BzlaBitVector *s0;

  (void) t;

  s0 = *s;
  assert(s0);

  if (bzla_node_is_bv_const(cond->e[0]))
  {
    /* pick enabled branch */
    assert((cond->e[0] == bzla->true_exp && !bzla_node_is_bv_const(cond->e[1]))
           || (cond->e[0] != bzla->true_exp
               && !bzla_node_is_bv_const(cond->e[2])));
    idx_x = cond->e[0] == bzla->true_exp ? 1 : 2;
  }
  else
  {
    is_const_e1 = bzla_node_is_bv_const(cond->e[1]);
    is_const_e2 = bzla_node_is_bv_const(cond->e[2]);
    if (is_const_e1 && is_const_e2)
    {
      idx_x = 0;
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
        idx_x = 0;
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
        idx_x = is_const_e1 ? 2 : 1;
      }
    }
    else
    {
      /* enabled branch is not const, condition not const */
      if (bzla_rng_pick_with_prob(
              &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND)))
      {
        idx_x = 0;
      }
      else
      {
        idx_x = bzla_bv_is_true(s0) ? 1 : 2;
      }
    }
  }

#ifndef NBZLALOG
  select_path_log(bzla, cond, s, idx_x);
#endif
  assert(!bzla_node_is_bv_const(cond->e[idx_x]));
  return idx_x;
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
check_cons_dbg(Bzla *bzla,
               BzlaNode *node,
               BzlaBitVector *t,
               BzlaBitVector *s,
               int32_t idx_x,
               BzlaIntHashTable *domains,
               bool same_bw)
{
  assert(bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(t);
  assert(s);
  assert(domains);
  assert(!same_bw || bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(node->e[idx_x]));
}
#endif

BzlaBitVector *
bzla_proputils_cons_add(Bzla *bzla,
                        BzlaNode *add,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, add, t, s, idx_x, domains, true);
#endif
  (void) add;
  (void) s;
  (void) idx_x;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_add);
  return bzla_bv_new_random(bzla->mm, &bzla->rng, bzla_bv_get_width(t));
}

BzlaBitVector *
bzla_proputils_cons_and(Bzla *bzla,
                        BzlaNode *and,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, and, t, s, idx_x, domains, true);
#endif
  uint32_t i, bw;
  BzlaBitVector *res;
  BzlaUIntStack dcbits;
  bool b;

  (void) s;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_and);

  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(bzla->mm, dcbits);

  res = bzla_bv_copy(bzla->mm, bzla_model_get_bv(bzla, and->e[idx_x]));

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
bzla_proputils_cons_eq(Bzla *bzla,
                       BzlaNode *eq,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, eq, t, s, idx_x, domains, false);
#endif
  (void) t;
  (void) domains;
  (void) d_res_x;

  BzlaBitVector *res;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_eq);

  if (bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_EQ_FLIP)))
  {
    res = bzla_bv_copy(bzla->mm, bzla_model_get_bv(bzla, eq->e[idx_x]));
    bzla_bv_flip_bit(
        res, bzla_rng_pick_rand(&bzla->rng, 0, bzla_bv_get_width(res) - 1));
  }
  else
  {
    res = bzla_bv_new_random(bzla->mm, &bzla->rng, bzla_bv_get_width(s));
  }
  return res;
}

static BzlaBitVector *
cons_ult_aux(Bzla *bzla,
             BzlaNode *ult,
             BzlaBitVector *t,
             BzlaBitVector *s,
             int32_t idx_x,
             BzlaIntHashTable *domains,
             BzlaBvDomain *d_res_x,
             bool with_const_bits)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, ult, t, s, idx_x, domains, false);
#endif
  bool isult;
  uint32_t bw;
  BzlaBitVector *ones, *zero, *tmp, *res;
  BzlaMemMgr *mm;
  BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;

  (void) ult;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_ult);

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(s);
  isult = !bzla_bv_is_zero(t);

  x = with_const_bits
          ? bzla_hashint_map_get(domains, bzla_node_get_id(ult->e[idx_x]))
                ->as_ptr
          : 0;

  if (idx_x && isult)
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
  else if (!idx_x && isult)
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
        zero = bzla_bv_new(mm, bw);
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
      }
    }
    else
    {
      zero = bzla_bv_new(mm, bw);
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
    tmp = bzla_bv_new_random(mm, &bzla->rng, bw);
    if (x)
    {
      res = set_const_bits(mm, x, tmp);
      bzla_bv_free(mm, tmp);
    }
    else
    {
      res = tmp;
    }
  }

  return res;
}

BzlaBitVector *
bzla_proputils_cons_ult(Bzla *bzla,
                        BzlaNode *ult,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
  return cons_ult_aux(bzla, ult, t, s, idx_x, domains, d_res_x, false);
}

static BzlaBitVector *
cons_sll_aux(Bzla *bzla,
             BzlaNode *sll,
             BzlaBitVector *t,
             BzlaBitVector *s,
             int32_t idx_x,
             BzlaIntHashTable *domains,
             BzlaBvDomain *d_res_x,
             bool with_const_bits)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, sll, t, s, idx_x, domains, true);
#endif
  uint32_t bw, ctz_t, shift, max;
  BzlaBitVector *res, *bv_shift, *left, *right, *zero, *tmp;
  BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  (void) sll;
  (void) s;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_sll);

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  x = with_const_bits
          ? bzla_hashint_map_get(domains, bzla_node_get_id(sll->e[idx_x]))
                ->as_ptr
          : 0;

  if (bw >= 64 && ctz_t == bw)
  {
    shift    = bw;
    bv_shift = bzla_bv_new_random(mm, &bzla->rng, bw);
    if (x && idx_x)
    {
      set_const_bits(mm, x, bv_shift);
    }
  }
  else
  {
    max = ctz_t < bw ? ctz_t : ((1u << bw) - 1);
    if (x && idx_x)
    {
      tmp  = bzla_bv_uint64_to_bv(mm, max, bw);
      zero = bzla_bv_new(mm, bw);
      bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, zero, tmp);
      if (!bzla_bvdomain_gen_has_next(&gen))
      {
        /* non-recoverable conflict */
        bzla_bv_free(mm, zero);
        bzla_bv_free(mm, tmp);
        bzla_bvdomain_gen_delete(&gen);
        return NULL;
      }
      bv_shift = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bv_free(mm, zero);
      bzla_bv_free(mm, tmp);
      bzla_bvdomain_gen_delete(&gen);
    }
    else
    {
      shift    = bzla_rng_pick_rand(&bzla->rng, 0, max);
      bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);
    }
  }

  if (idx_x)
  {
    res = bv_shift;
  }
  else
  {
    if (shift == bw)
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
      if (x)
      {
        set_const_bits(mm, x, bv_shift);
      }
    }
    else
    {
      if (shift)
      {
        if (x)
        {
          if (bzla_bvdomain_is_fixed(mm, x))
          {
            left = bzla_bv_slice(mm, x->lo, bw - 1, bw - shift);
          }
          else
          {
            bzla_bvdomain_gen_init(mm, &bzla->rng, &gen, x);
            left = bzla_bv_slice(
                mm, bzla_bvdomain_gen_random(&gen), bw - 1, bw - shift);
            bzla_bvdomain_gen_delete(&gen);
          }
        }
        else
        {
          left = bzla_bv_new_random(mm, &bzla->rng, shift);
        }
        right = bzla_bv_slice(mm, t, bw - 1 - shift, 0);
        res   = bzla_bv_concat(mm, left, right);
        bzla_bv_free(mm, left);
        bzla_bv_free(mm, right);
      }
      else
      {
        res = bzla_bv_copy(mm, t);
      }
      if (x && !bzla_bvdomain_check_fixed_bits(mm, x, res))
      {
        /* non-recoverable conflict */
        bzla_bv_free(mm, bv_shift);
        bzla_bv_free(mm, res);
        return NULL;
      }
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_sll(Bzla *bzla,
                        BzlaNode *sll,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
  return cons_sll_aux(bzla, sll, t, s, idx_x, domains, d_res_x, false);
}

BzlaBitVector *
bzla_proputils_cons_srl(Bzla *bzla,
                        BzlaNode *srl,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, srl, t, s, idx_x, domains, true);
#endif
  uint32_t clz_t, bw;
  uint64_t shift;
  BzlaBitVector *res, *bv_shift, *left, *right;
  BzlaMemMgr *mm;

  (void) srl;
  (void) s;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_srl);

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  if (bw >= 64 && clz_t == bw)
  {
    shift    = bw;
    bv_shift = bzla_bv_new_random(mm, &bzla->rng, bw);
  }
  else
  {
    shift = bzla_rng_pick_rand(
        &bzla->rng, 0, clz_t < bw ? clz_t : ((1u << bw) - 1));
    bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);
  }

  if (idx_x)
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
bzla_proputils_cons_mul(Bzla *bzla,
                        BzlaNode *mul,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, mul, t, s, idx_x, domains, true);
#endif
  uint32_t r, bw, ctz_res, ctz_bvmul;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  (void) mul;
  (void) s;
  (void) idx_x;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_mul);

  mm  = bzla->mm;
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
      ctz_bvmul = bzla_bv_get_num_trailing_zeros(t);
      /* choose res as 2^n with ctz(t) >= ctz(res) with prob 0.1 */
      if (bzla_rng_pick_with_prob(&bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        res = bzla_bv_new(mm, bw);
        bzla_bv_set_bit(
            res, bzla_rng_pick_rand(&bzla->rng, 0, ctz_bvmul - 1), 1);
      }
      /* choose res as t / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (bzla_rng_pick_with_prob(&bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        if ((r = bzla_rng_pick_rand(&bzla->rng, 0, ctz_bvmul)))
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
        if (ctz_res > ctz_bvmul)
          bzla_bv_set_bit(
              res, bzla_rng_pick_rand(&bzla->rng, 0, ctz_bvmul - 1), 1);
      }
    }
  }

  return res;
}

BzlaBitVector *
bzla_proputils_cons_udiv(Bzla *bzla,
                         BzlaNode *udiv,
                         BzlaBitVector *t,
                         BzlaBitVector *s,
                         int32_t idx_x,
                         BzlaIntHashTable *domains,
                         BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, udiv, t, s, idx_x, domains, true);
#endif
  uint32_t bw;
  BzlaBitVector *res, *tmp, *tmp_s, *zero, *one, *ones;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  bw   = bzla_bv_get_width(t);
  zero = bzla_bv_new(mm, bw);
  one  = bzla_bv_one(mm, bw);
  ones = bzla_bv_ones(mm, bw);

  (void) udiv;
  (void) s;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_udiv);

  if (idx_x)
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
    /* -> t = 0 then res < 1...1
     * -> t = 1...1 then choose random res
     * -> else choose tmp_s s.t. res = tmp_s * t does not overflow */
    if (bzla_bv_is_zero(t))
    {
      tmp = bzla_bv_dec(mm, ones);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
    else if (!bzla_bv_compare(t, ones))
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      tmp_s = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, ones);
      while (bzla_bv_is_umulo(mm, tmp_s, t))
      {
        tmp = bzla_bv_sub(mm, tmp_s, one);
        bzla_bv_free(mm, tmp_s);
        tmp_s = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
        bzla_bv_free(mm, tmp);
      }
      res = bzla_bv_mul(mm, tmp_s, t);
      bzla_bv_free(mm, tmp_s);
    }
  }

  bzla_bv_free(mm, one);
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, ones);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_urem(Bzla *bzla,
                         BzlaNode *urem,
                         BzlaBitVector *t,
                         BzlaBitVector *s,
                         int32_t idx_x,
                         BzlaIntHashTable *domains,
                         BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, urem, t, s, idx_x, domains, true);
#endif
  uint32_t bw;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;

  (void) urem;
  (void) s;
  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_urem);

  mm   = bzla->mm;
  bw   = bzla_bv_get_width(t);
  ones = bzla_bv_ones(mm, bw);

  if (idx_x)
  {
    /* t = 1...1  ->  res = 0 */
    if (!bzla_bv_compare(t, ones))
    {
      res = bzla_bv_new(mm, bw);
    }
    /* else res > t */
    else
    {
      tmp = bzla_bv_inc(mm, t);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    /* t = 1...1  ->  res = 1...1 */
    if (!bzla_bv_compare(t, ones))
    {
      res = bzla_bv_copy(mm, ones);
    }
    /* else res >= t */
    else
    {
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, t, ones);
    }
  }

  bzla_bv_free(mm, ones);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_concat(Bzla *bzla,
                           BzlaNode *concat,
                           BzlaBitVector *t,
                           BzlaBitVector *s,
                           int32_t idx_x,
                           BzlaIntHashTable *domains,
                           BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, concat, t, s, idx_x, domains, false);
#endif
  int32_t idx_s, bw_t, bw_s;
  uint32_t r;
  BzlaBitVector *res;
  const BzlaBitVector *bvcur;

  (void) domains;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_concat);

  idx_s = idx_x ? 0 : 1;
  bw_t  = bzla_bv_get_width(t);
  bw_s  = bzla_bv_get_width(s);

  /* If one operand is const, with BZLA_OPT_CONC_FLIP_PROB
   * either slice bits out of current assignment and flip max. one bit
   * randomly, or slice bits out of given assignment 's'.  */

  if (bzla_node_is_bv_const(concat->e[idx_s])
      && bzla_rng_pick_with_prob(
          &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_CONC_FLIP)))
  {
    bvcur = bzla_model_get_bv(bzla, concat);
    res   = idx_x ? bzla_bv_slice(bzla->mm, bvcur, bw_t - bw_s - 1, 0)
                : bzla_bv_slice(bzla->mm, bvcur, bw_t - 1, bw_s);
    r = bzla_rng_pick_rand(&bzla->rng, 0, bzla_bv_get_width(res));
    if (r) bzla_bv_flip_bit(res, r - 1);
  }
  else
  {
    res = idx_x ? bzla_bv_slice(bzla->mm, t, bw_t - bw_s - 1, 0)
                : bzla_bv_slice(bzla->mm, t, bw_t - 1, bw_s);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_slice(Bzla *bzla,
                          BzlaNode *slice,
                          BzlaBitVector *t,
                          BzlaBitVector *s,
                          int32_t idx_x,
                          BzlaIntHashTable *domains,
                          BzlaBvDomain *d_res_x)
{
  return bzla_proputils_inv_slice(bzla, slice, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_cond(Bzla *bzla,
                         BzlaNode *cond,
                         BzlaBitVector *t,
                         BzlaBitVector *s,
                         int32_t idx_x,
                         BzlaIntHashTable *domains,
                         BzlaBvDomain *d_res_x)
{
  return bzla_proputils_inv_cond(bzla, cond, t, s, idx_x, domains, d_res_x);
}

/* ========================================================================== */
/* Consistent value computation with respect to const bits                    */
/* ========================================================================== */

BzlaBitVector *
bzla_proputils_cons_add_const(Bzla *bzla,
                              BzlaNode *add,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, add, t, s, idx_x, domains, true);
#endif
  (void) d_res_x;

  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_add);

  mm = bzla->mm;
  x  = bzla_hashint_map_get(domains, bzla_node_get_id(add->e[idx_x]))->as_ptr;
  if (bzla_bvdomain_is_fixed(mm, x)) return bzla_bv_copy(mm, x->lo);
  tmp = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(t));
  res = set_const_bits(mm, x, tmp);
  bzla_bv_free(mm, tmp);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_and_const(Bzla *bzla,
                              BzlaNode *and,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, and, t, s, idx_x, domains, true);
#endif
  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;
  (void) d_res_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_and);

  mm = bzla->mm;
  x  = bzla_hashint_map_get(domains, bzla_node_get_id(and->e[idx_x]))->as_ptr;
  if (bzla_bvdomain_is_fixed(mm, x)) return bzla_bv_copy(mm, x->lo);

  for (uint32_t i = 0, bw = bzla_bv_get_width(t); i < bw; i++)
  {
    if (bzla_bv_get_bit(t, i) && bzla_bvdomain_is_fixed_bit_false(x, i))
    {
      /* non-recoverable conflict */
      return NULL;
    }
  }
  tmp = bzla_proputils_cons_and(bzla, and, t, s, idx_x, domains, d_res_x);
  res = set_const_bits(mm, x, tmp);
  bzla_bv_free(mm, tmp);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_eq_const(Bzla *bzla,
                             BzlaNode *eq,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, eq, t, s, idx_x, domains, false);
#endif
  BzlaBvDomain *x;
  (void) d_res_x;

  x = bzla_hashint_map_get(domains, bzla_node_get_id(eq->e[idx_x]))->as_ptr;
  if (bzla_bvdomain_is_fixed(bzla->mm, x))
  {
    record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_eq);
    return bzla_bv_copy(bzla->mm, x->lo);
  }
  return bzla_proputils_cons_eq(bzla, eq, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_ult_const(Bzla *bzla,
                              BzlaNode *ult,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
  return cons_ult_aux(bzla, ult, t, s, idx_x, domains, d_res_x, true);
}

BzlaBitVector *
bzla_proputils_cons_sll_const(Bzla *bzla,
                              BzlaNode *sll,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
  return cons_sll_aux(bzla, sll, t, s, idx_x, domains, d_res_x, true);
}

BzlaBitVector *
bzla_proputils_cons_srl_const(Bzla *bzla,
                              BzlaNode *srl,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_srl(bzla, srl, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_mul_const(Bzla *bzla,
                              BzlaNode *mul,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_mul(bzla, mul, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_udiv_const(Bzla *bzla,
                               BzlaNode *udiv,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains,
                               BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_udiv(bzla, udiv, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_urem_const(Bzla *bzla,
                               BzlaNode *urem,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains,
                               BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_urem(bzla, urem, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_concat_const(Bzla *bzla,
                                 BzlaNode *concat,
                                 BzlaBitVector *t,
                                 BzlaBitVector *s,
                                 int32_t idx_x,
                                 BzlaIntHashTable *domains,
                                 BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_concat(
      bzla, concat, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_slice_const(Bzla *bzla,
                                BzlaNode *slice,
                                BzlaBitVector *t,
                                BzlaBitVector *s,
                                int32_t idx_x,
                                BzlaIntHashTable *domains,
                                BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_slice(bzla, slice, t, s, idx_x, domains, d_res_x);
}

BzlaBitVector *
bzla_proputils_cons_cond_const(Bzla *bzla,
                               BzlaNode *cond,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains,
                               BzlaBvDomain *d_res_x)
{
  // TODO
  return bzla_proputils_cons_cond(bzla, cond, t, s, idx_x, domains, d_res_x);
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
              BzlaNode *node,
              BzlaBitVector *t,
              BzlaBitVector *s,
              int32_t idx_x,
              BzlaIntHashTable *domains,
              BzlaPropIsInv is_inv_fun,
              BzlaPropIsInv is_inv_fun_const,
              bool same_bw,
              BzlaBvDomain *d_res_x)
{
  assert(bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(t);
  assert(s);
  assert(domains);
  assert(!same_bw || bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(node->e[idx_x]));
  assert(is_inv_fun(bzla, 0, t, s, idx_x, 0));
  (void) d_res_x;
  assert(
      !bzla_hashint_map_contains(domains, node->id)
      || bzla_hashint_map_contains(domains, bzla_node_get_id(node->e[idx_x])));
  BzlaHashTableData *x =
      bzla_hashint_map_get(domains, bzla_node_get_id(node->e[idx_x]));
  assert(!x || !bzla_bvdomain_has_fixed_bits(bzla->mm, x->as_ptr)
         || is_inv_fun_const(bzla, x->as_ptr, t, s, idx_x, 0));
}

static void
check_result_binary_dbg(Bzla *bzla,
                        BzlaBitVector *(*fun)(BzlaMemMgr *,
                                              const BzlaBitVector *,
                                              const BzlaBitVector *),
                        BzlaNode *exp,
                        BzlaBitVector *s,
                        BzlaBitVector *t,
                        BzlaBitVector *res,
                        int32_t idx_x,
                        char *op)
{
  assert(bzla);
  assert(fun);
  assert(exp);
  assert(s);
  assert(t);
  assert(res);
  assert(op);

  (void) exp;
  (void) op;

  BzlaBitVector *tmp;
  char *str_s, *str_t, *str_res;

  tmp = idx_x ? fun(bzla->mm, s, res) : fun(bzla->mm, res, s);

  assert(!bzla_bv_compare(tmp, t));
  str_t   = bzla_bv_to_char(bzla->mm, t);
  str_s   = bzla_bv_to_char(bzla->mm, s);
  str_res = bzla_bv_to_char(bzla->mm, res);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s %s %s",
          idx_x,
          bzla_util_node2string(exp),
          str_t,
          idx_x ? str_s : str_res,
          op,
          idx_x ? str_res : str_s);
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
bzla_proputils_inv_add(Bzla *bzla,
                       BzlaNode *add,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                add,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_add,
                bzla_is_inv_add_const,
                true,
                d_res_x);
#endif
  BzlaBitVector *res;

  (void) add;
  (void) idx_x;
  (void) domains;
  (void) d_res_x;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_add);

  /* invertibility condition: true, res = t - s */
  res = bzla_bv_sub(bzla->mm, t, s);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_add, add, s, t, res, idx_x, "+");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_and(Bzla *bzla,
                       BzlaNode *and,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                and,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_and,
                bzla_is_inv_and_const,
                true,
                d_res_x);
#endif
  uint32_t i, bw;
  int32_t bit_and, bit_e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  BzlaUIntStack dcbits;
  bool b;

  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_and);

  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(mm, dcbits);

  res = bzla_bv_copy(mm, bzla_model_get_bv(bzla, and->e[idx_x]));
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
  check_result_binary_dbg(bzla, bzla_bv_and, and, s, t, res, idx_x, "AND");
#endif

  BZLA_RELEASE_STACK(dcbits);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_eq(Bzla *bzla,
                      BzlaNode *eq,
                      BzlaBitVector *t,
                      BzlaBitVector *s,
                      int32_t idx_x,
                      BzlaIntHashTable *domains,
                      BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                eq,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_eq,
                bzla_is_inv_eq_const,
                false,
                d_res_x);
#endif
  BzlaBitVector *res;
  BzlaMemMgr *mm;

  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

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
        res = bzla_bv_copy(bzla->mm, bzla_model_get_bv(bzla, eq->e[idx_x]));
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
  check_result_binary_dbg(bzla, bzla_bv_eq, eq, s, t, res, idx_x, "=");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_ult(Bzla *bzla,
                       BzlaNode *ult,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                ult,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_ult,
                bzla_is_inv_ult_const,
                false,
                d_res_x);
#endif
  bool isult;
  uint32_t bw;
  BzlaBitVector *res, *zero, *one, *ones, *tmp;
  BzlaMemMgr *mm;

  (void) ult;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);

  bw    = bzla_bv_get_width(s);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  ones  = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(t);

  res = 0;

  if (idx_x)
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
  check_result_binary_dbg(bzla, bzla_bv_ult, ult, s, t, res, idx_x, "<");
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
bzla_proputils_inv_sll(Bzla *bzla,
                       BzlaNode *sll,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                sll,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_sll,
                bzla_is_inv_sll_const,
                true,
                d_res_x);
#endif
  uint32_t bw, i, ctz_s, ctz_t, shift;
  BzlaBitVector *res, *tmp, *ones;
  BzlaMemMgr *mm;

  (void) sll;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sll);

  res   = 0;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  /* ------------------------------------------------------------------------
   * s << x = t
   *
   * -> identify possible shift value via zero LSB in t
   *    (considering zero LSB in s)
   * ------------------------------------------------------------------------ */
  if (idx_x)
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
  check_result_binary_dbg(bzla, bzla_bv_sll, sll, s, t, res, idx_x, "<<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_srl(Bzla *bzla,
                       BzlaNode *srl,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                srl,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_srl,
                bzla_is_inv_srl_const,
                true,
                d_res_x);
#endif
  uint32_t bw, i, clz_s, clz_t, shift;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;

  (void) srl;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);

  res   = 0;
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  /* ------------------------------------------------------------------------
   * s >> x = t
   *
   * -> identify possible shift value via zero MSBs in t
   *    (considering zero MSBs in s)
   * ------------------------------------------------------------------------ */
  if (idx_x)
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
  check_result_binary_dbg(bzla, bzla_bv_srl, srl, s, t, res, idx_x, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_mul(Bzla *bzla,
                       BzlaNode *mul,
                       BzlaBitVector *t,
                       BzlaBitVector *s,
                       int32_t idx_x,
                       BzlaIntHashTable *domains,
                       BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                mul,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_mul,
                bzla_is_inv_mul_const,
                true,
                d_res_x);
#endif
  int32_t lsb_s, ispow2_s;
  uint32_t i, j, bw;
  BzlaBitVector *res, *inv, *tmp, *tmp2;
  BzlaMemMgr *mm;

  (void) mul;
  (void) idx_x;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

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
  check_result_binary_dbg(bzla, bzla_bv_mul, mul, s, t, res, idx_x, "*");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_udiv(Bzla *bzla,
                        BzlaNode *udiv,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                udiv,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_udiv,
                bzla_is_inv_udiv_const,
                true,
                d_res_x);
#endif
  uint32_t bw;
  BzlaBitVector *res, *lo, *up, *one, *ones, *tmp;
  BzlaMemMgr *mm;
  BzlaRNG *rng;

  (void) udiv;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_udiv);

  rng = &bzla->rng;
  bw  = bzla_bv_get_width(s);

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
  if (idx_x)
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
        res = bzla_bv_new(mm, bw);
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
  check_result_binary_dbg(bzla, bzla_bv_udiv, udiv, s, t, res, idx_x, "/");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_urem(Bzla *bzla,
                        BzlaNode *urem,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                urem,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_urem,
                bzla_is_inv_urem_const,
                true,
                d_res_x);
#endif
  uint32_t bw, cnt;
  int32_t cmp;
  BzlaBitVector *res, *ones, *tmp, *tmp2, *one, *n, *mul, *n_hi, *sub;
  BzlaMemMgr *mm;

  (void) urem;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_urem);

  bw = bzla_bv_get_width(t);

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
  if (idx_x)
  {
    if (!bzla_bv_compare(t, ones))
    {
      /* CONFLICT: t = ~0 but s != ~0 */
      assert(!bzla_bv_compare(s, ones));

      /* s % x = ~0 -> s = ~0, x = 0 */
      res = bzla_bv_new(mm, bw);
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
          res = bzla_bv_new(mm, bw);
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
  check_result_binary_dbg(bzla, bzla_bv_urem, urem, s, t, res, idx_x, "%");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_concat(Bzla *bzla,
                          BzlaNode *concat,
                          BzlaBitVector *t,
                          BzlaBitVector *s,
                          int32_t idx_x,
                          BzlaIntHashTable *domains,
                          BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                concat,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_concat,
                bzla_is_inv_concat_const,
                false,
                d_res_x);
#endif
  uint32_t bw_t, bw_s;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  (void) concat;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_concat);

  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);
  res  = 0;

  /* ------------------------------------------------------------------------
   * s o x = t
   *
   * -> slice x out of the lower bits of t
   * ------------------------------------------------------------------------ */
  if (idx_x)
  {
    tmp = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bw_s);
    assert(!bzla_bv_compare(tmp, s)); /* CONFLICT: s bits do not match t */
    res = bzla_bv_slice(mm, t, bw_t - bw_s - 1, 0);
  }
  /* ------------------------------------------------------------------------
   * x o s = t
   *
   * -> slice x out of the upper bits of t
   * ------------------------------------------------------------------------ */
  else
  {
    tmp = bzla_bv_slice(mm, t, bw_s - 1, 0);
    assert(!bzla_bv_compare(tmp, s)); /* CONFLICT: s bits do not match t */
    res = bzla_bv_slice(mm, t, bw_t - 1, bw_s);
  }
  bzla_bv_free(mm, tmp);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_concat, concat, s, t, res, idx_x, "o");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_slice(Bzla *bzla,
                         BzlaNode *slice,
                         BzlaBitVector *t,
                         BzlaBitVector *s,
                         int32_t idx_x,
                         BzlaIntHashTable *domains,
                         BzlaBvDomain *d_res_x)
{
  assert(bzla);
  assert(slice);
  assert(bzla_node_is_regular(slice));
  assert(t);
  assert(!bzla_node_is_bv_const(slice->e[0]));

  uint32_t i, upper, lower, rlower, rupper, rboth, bw_x;
  BzlaNode *e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  bool bkeep, bflip;

  (void) domains;
  (void) idx_x;
  (void) d_res_x;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_slice);

  /* invertibility condition: true */

  mm = bzla->mm;
  e  = slice->e[0];
  assert(e);

  bflip = bzla_rng_pick_with_prob(
      &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP));

  bkeep = bflip ? true
                : bzla_rng_pick_with_prob(
                    &bzla->rng,
                    bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_SLICE_KEEP_DC));

  upper = bzla_node_bv_slice_get_upper(slice);
  lower = bzla_node_bv_slice_get_lower(slice);

  res = bzla_bv_new(mm, bzla_node_bv_get_width(bzla, e));

  /* keep previous value for don't care bits or set randomly with prob
   * BZLA_OPT_PROP_PROB_SLICE_KEEP_DC */
  for (i = 0; i < lower; i++)
    bzla_bv_set_bit(
        res,
        i,
        bkeep ? bzla_bv_get_bit(s, i) : bzla_rng_pick_rand(&bzla->rng, 0, 1));

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
        bkeep ? bzla_bv_get_bit(s, i) : bzla_rng_pick_rand(&bzla->rng, 0, 1));

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
          bzla_util_node2string(slice),
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
bzla_proputils_inv_cond(Bzla *bzla,
                        BzlaNode *cond,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains,
                        BzlaBvDomain *d_res_x)
{
  assert(bzla);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(t);
  assert(!bzla_bv_compare(s, bzla_model_get_bv(bzla, cond->e[0])));
  assert(idx_x || !bzla_node_is_bv_const(cond->e[idx_x]));

  BzlaBitVector *res, *s1, *s2;
  BzlaMemMgr *mm = bzla->mm;

  (void) domains;
  (void) d_res_x;

  s1 = (BzlaBitVector *) bzla_model_get_bv(bzla, cond->e[1]);
  s2 = (BzlaBitVector *) bzla_model_get_bv(bzla, cond->e[2]);
#ifndef NDEBUG
  char *str_t  = bzla_bv_to_char(bzla->mm, t);
  char *str_s0 = bzla_bv_to_char(mm, s);
  char *str_s1 = bzla_bv_to_char(mm, s1);
  char *str_s2 = bzla_bv_to_char(mm, s2);
#endif

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_cond);

  /* either assume that cond is fixed and propagate s
   * to enabled path, or flip condition */

  if (idx_x == 0)
  {
    /* flip condition */
    res = bzla_bv_not(mm, s);
  }
  else
  {
    /* else continue propagating current target value down */
    res = bzla_bv_copy(mm, t);
    if (bzla_node_is_bv_const(cond->e[idx_x]))
    {
      bool is_recoverable = !bzla_bv_compare(t, idx_x == 1 ? s2 : s1);
#ifndef NDEBUG
      if (idx_x == 2)
      {
        BZLALOG(2,
                "%s CONFLICT (@%d): %s := %s ? %s : x",
                is_recoverable ? "recoverable" : "non-recoverable",
                bzla_node_get_id(cond),
                str_t,
                str_s0,
                str_s1);
      }
      else
      {
        BZLALOG(2,
                "%s CONFLICT (@%d): %s := %s ? x : %s",
                is_recoverable ? "recoverable" : "non-recoverable",
                bzla_node_get_id(cond),
                str_t,
                str_s0,
                str_s2);
      }
      BZLALOG(2, "");
#endif
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        if (is_recoverable)
          BZLA_PROP_SOLVER(bzla)->stats.rec_conf += 1;
        else
          BZLA_PROP_SOLVER(bzla)->stats.non_rec_conf += 1;
      }
      else
      {
        if (is_recoverable)
          BZLA_SLS_SOLVER(bzla)->stats.move_prop_rec_conf += 1;
        else
          BZLA_SLS_SOLVER(bzla)->stats.move_prop_non_rec_conf += 1;
      }
    }
  }

#ifndef NDEBUG
  char *str_res = bzla_bv_to_char(mm, res);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s ? %s : %s",
          idx_x,
          bzla_util_node2string(cond),
          str_t,
          idx_x == 0 ? str_res : str_s0,
          idx_x == 1 ? str_res : str_s1,
          idx_x == 2 ? str_res : str_s2);
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
bzla_proputils_inv_add_const(Bzla *bzla,
                             BzlaNode *add,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
  assert(domains);
#ifndef NDEBUG
  check_inv_dbg(bzla,
                add,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_add,
                bzla_is_inv_add_const,
                true,
                d_res_x);
#endif
  BzlaBitVector *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  x  = bzla_hashint_map_get(domains, bzla_node_get_id(add->e[idx_x]))->as_ptr;

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
    res = bzla_proputils_inv_add(bzla, add, t, s, idx_x, domains, 0);
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_and_const(Bzla *bzla,
                             BzlaNode *and,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
  assert(domains);
  assert(bzla_node_is_regular(and));
  assert(
      !bzla_hashint_map_contains(domains, and->id)
      || bzla_hashint_map_contains(domains, bzla_node_get_id(and->e[idx_x])));
  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  check_inv_dbg(bzla,
                and,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_and,
                bzla_is_inv_and_const,
                true,
                d_res_x);
#endif
  mm = bzla->mm;
  x  = bzla_hashint_map_get(domains, bzla_node_get_id(and->e[idx_x]))->as_ptr;
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
    tmp = bzla_proputils_inv_and(bzla, and, t, s, idx_x, domains, 0);
    res = set_const_bits(mm, x, tmp);
    bzla_bv_free(mm, tmp);
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_eq_const(Bzla *bzla,
                            BzlaNode *eq,
                            BzlaBitVector *t,
                            BzlaBitVector *s,
                            int32_t idx_x,
                            BzlaIntHashTable *domains,
                            BzlaBvDomain *d_res_x)
{
  assert(domains);
  assert(bzla_node_is_regular(eq));
  assert(!bzla_hashint_map_contains(domains, eq->id)
         || bzla_hashint_map_contains(domains, bzla_node_get_id(eq->e[idx_x])));
  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  check_inv_dbg(bzla,
                eq,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_eq,
                bzla_is_inv_eq_const,
                false,
                d_res_x);
#endif
  mm = bzla->mm;
  x  = bzla_hashint_map_get(domains, bzla_node_get_id(eq->e[idx_x]))->as_ptr;

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
  else
  {
    tmp = bzla_proputils_inv_eq(bzla, eq, t, s, idx_x, domains, 0);
    res = set_const_bits(mm, x, tmp);
    bzla_bv_free(mm, tmp);
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_ult_const(Bzla *bzla,
                             BzlaNode *ult,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
  assert(domains);
  assert(bzla_node_is_regular(ult));
  assert(
      !bzla_hashint_map_contains(domains, ult->id)
      || bzla_hashint_map_contains(domains, bzla_node_get_id(ult->e[idx_x])));
#ifndef NDEBUG
  check_inv_dbg(bzla,
                ult,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_ult,
                bzla_is_inv_ult_const,
                false,
                d_res_x);
#endif
  bool isult;
  uint32_t bw;
  BzlaBitVector *res, *zero, *one, *ones, *tmp;
  BzlaMemMgr *mm;
  BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;

  (void) ult;
  (void) domains;
  (void) d_res_x;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);

  bw    = bzla_bv_get_width(s);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  ones  = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(t);

  x = bzla_hashint_map_get(domains, bzla_node_get_id(ult->e[idx_x]))->as_ptr;

  res = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = idx_x ? bzla_bv_ult(mm, s, x->lo) : bzla_bv_ult(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    if (idx_x)
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
  check_result_binary_dbg(bzla, bzla_bv_ult, ult, s, t, res, idx_x, "<");
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
bzla_proputils_inv_sll_const(Bzla *bzla,
                             BzlaNode *sll,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
  assert(idx_x || d_res_x == 0);
  assert(!idx_x || d_res_x);
#ifndef NDEBUG
  check_inv_dbg(bzla,
                sll,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_sll,
                bzla_is_inv_sll_const,
                true,
                d_res_x);
#endif
  uint32_t cnt;
  BzlaBitVector *tmp, *res, *bv;
  BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  res = 0;

  x = bzla_hashint_map_get(domains, bzla_node_get_id(sll->e[idx_x]))->as_ptr;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = idx_x ? bzla_bv_sll(mm, s, x->lo) : bzla_bv_sll(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sll);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (idx_x)
  {
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sll);

    assert(d_res_x);
    assert(bzla_bvdomain_is_fixed(mm, d_res_x));
    bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, d_res_x->lo, 0);
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
    if (!res) res = bzla_bv_copy(mm, d_res_x->lo);
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    assert(d_res_x == 0);
    tmp = bzla_proputils_inv_sll(bzla, sll, t, s, idx_x, domains, 0);
    res = set_const_bits(mm, x, tmp);
    bzla_bv_free(mm, tmp);
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_srl_const(Bzla *bzla,
                             BzlaNode *srl,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
  assert(idx_x || d_res_x == 0);
  assert(!idx_x || d_res_x);
#ifndef NDEBUG
  check_inv_dbg(bzla,
                srl,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_srl,
                bzla_is_inv_srl_const,
                true,
                d_res_x);
#endif
  uint32_t cnt;
  BzlaBitVector *tmp, *res, *bv;
  BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  res = 0;

  x = bzla_hashint_map_get(domains, bzla_node_get_id(srl->e[idx_x]))->as_ptr;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = idx_x ? bzla_bv_srl(mm, s, x->lo) : bzla_bv_srl(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (idx_x)
  {
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);

    assert(d_res_x);
    assert(bzla_bvdomain_is_fixed(mm, d_res_x));
    bzla_bvdomain_gen_init_range(mm, &bzla->rng, &gen, x, d_res_x->lo, 0);
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
    if (!res) res = bzla_bv_copy(mm, d_res_x->lo);
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    assert(d_res_x == 0);
    tmp = bzla_proputils_inv_srl(bzla, srl, t, s, idx_x, domains, 0);
    res = set_const_bits(mm, x, tmp);
    bzla_bv_free(mm, tmp);
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_mul_const(Bzla *bzla,
                             BzlaNode *mul,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains,
                             BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                mul,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_mul,
                bzla_is_inv_mul_const,
                true,
                d_res_x);
#endif
  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  x = bzla_hashint_map_get(domains, bzla_node_get_id(mul->e[idx_x]))->as_ptr;

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
  else if (d_res_x)
  {
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

    if (bzla_bvdomain_is_fixed(mm, d_res_x))
    {
#ifndef NDEBUG
      tmp = bzla_bv_mul(mm, s, d_res_x->lo);
      assert(bzla_bv_compare(tmp, t) == 0);
      bzla_bv_free(mm, tmp);
#endif
      res = bzla_bv_copy(mm, d_res_x->lo);
    }
    else
    {
      tmp = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(t));
      res = set_const_bits(mm, d_res_x, tmp);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    if (bzla_bv_is_zero(s))
    {
      record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

      tmp = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(t));
      res = set_const_bits(mm, x, tmp);
      bzla_bv_free(mm, tmp);
    }
    else
    {
      assert(!bzla_bvdomain_has_fixed_bits(mm, x));
      res = bzla_proputils_inv_mul(bzla, mul, t, s, idx_x, domains, 0);
    }
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_udiv_const(Bzla *bzla,
                              BzlaNode *udiv,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                udiv,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_udiv,
                bzla_is_inv_udiv_const,
                true,
                d_res_x);
#endif
  uint32_t bw;
  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_udiv);

  mm = bzla->mm;

  x = bzla_hashint_map_get(domains, bzla_node_get_id(udiv->e[idx_x]))->as_ptr;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = idx_x ? bzla_bv_udiv(mm, s, x->lo) : bzla_bv_udiv(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    BzlaBvDomainGenerator gen;

    if (d_res_x)
    {
      assert(d_res_x);
      bzla_bvdomain_gen_init_range(
          mm, &bzla->rng, &gen, x, d_res_x->lo, d_res_x->hi);
    }
    else if (bzla_bv_is_zero(s))
    {
      bw = bzla_bv_get_width(s);
      if (idx_x)
      {
        if (bzla_bv_is_ones(t))
        {
          /* x = 0 */
          tmp = bzla_bv_new(mm, bw);
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
      if (idx_x)
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
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_urem_const(Bzla *bzla,
                              BzlaNode *urem,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
#ifndef NDEBUG
  check_inv_dbg(bzla,
                urem,
                t,
                s,
                idx_x,
                domains,
                bzla_is_inv_urem,
                bzla_is_inv_urem_const,
                true,
                d_res_x);
#endif
  uint32_t bw, cnt;
  BzlaBitVector *tmp, *res, *ones, *bv;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_urem);

  mm = bzla->mm;

  x = bzla_hashint_map_get(domains, bzla_node_get_id(urem->e[idx_x]))->as_ptr;

  bw = bzla_bv_get_width(s);
  assert(bzla_bv_get_width(t) == bw);
  assert(bzla_bvdomain_get_width(x) == bw);

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    tmp = idx_x ? bzla_bv_urem(mm, s, x->lo) : bzla_bv_urem(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (idx_x)
  {
    ones = bzla_bv_ones(mm, bw);
    if (bzla_bv_compare(t, ones) == 0)
    {
      /* s % x = t = ones: s = ones, x = 0 */
      res = bzla_bv_new(mm, bw);
    }
    else if (bzla_bv_compare(s, t) == 0)
    {
      /* s = t and t != ones: x = 0 or random x > t */
      if (bzla_bv_compare(x->hi, t) <= 0
          || (bzla_bv_is_zero(x->lo) && bzla_rng_flip_coin(&bzla->rng)))
      {
        res = bzla_bv_new(mm, bw);
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
      /* Pick x within range determined in is_inv, given as d_res_x->lo for the
       * lower bound and d_res_x->hi for the upper bound (both inclusive). */
      assert(d_res_x);
      assert(bzla_bv_compare(d_res_x->lo, d_res_x->hi) <= 0);
      BzlaBvDomainGenerator gen;
      res = 0;
      bzla_bvdomain_gen_init_range(
          mm, &bzla->rng, &gen, x, d_res_x->lo, d_res_x->hi);
      assert(bzla_bvdomain_gen_has_next(&gen));
      for (cnt = 0, res = 0; cnt < BZLA_PROPUTILS_GEN_MAX_RAND; cnt++)
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
      if (!res) res = bzla_bv_copy(mm, d_res_x->lo);
      bzla_bvdomain_gen_delete(&gen);
    }
    bzla_bv_free(mm, ones);
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
      /* Pick x within range determined in is_inv, given as d_res_x->lo for the
       * lower bound and d_res_x->hi for the upper bound (both inclusive). */
      BzlaBvDomainGenerator gen;
      if (d_res_x)
      {
        assert(bzla_bv_compare(d_res_x->lo, d_res_x->hi) <= 0);
        res = bzla_bv_copy(mm, d_res_x->lo);
        bzla_bvdomain_gen_init_range(
            mm, &bzla->rng, &gen, x, d_res_x->lo, d_res_x->hi);
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
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_concat_const(Bzla *bzla,
                                BzlaNode *concat,
                                BzlaBitVector *t,
                                BzlaBitVector *s,
                                int32_t idx_x,
                                BzlaIntHashTable *domains,
                                BzlaBvDomain *d_res_x)
{
  return bzla_proputils_inv_concat(bzla, concat, t, s, idx_x, domains, d_res_x);
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_slice_const(Bzla *bzla,
                               BzlaNode *slice,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains,
                               BzlaBvDomain *d_res_x)
{
  return bzla_proputils_inv_slice(bzla, slice, t, s, idx_x, domains, d_res_x);
}

/* -------------------------------------------------------------------------- */
/* INV: cond                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_cond_const(Bzla *bzla,
                              BzlaNode *cond,
                              BzlaBitVector *t,
                              BzlaBitVector *s0,
                              BzlaBitVector *s1,
                              int32_t idx_x,
                              BzlaIntHashTable *domains,
                              BzlaBvDomain *d_res_x)
{
  assert(bzla);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(t);
  assert(s0);
  assert(s1);
  assert(domains);
  assert(!idx_x || bzla_bv_get_width(s0) == 1);
  assert(idx_x || bzla_bv_get_width(s0) == bzla_bv_get_width(s1));
  assert(idx_x || bzla_bv_get_width(s0) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 2);
  assert(!bzla_node_is_bv_const(cond->e[idx_x]));

  BzlaBitVector *tmp, *res;
  BzlaBvDomain *x;
  BzlaMemMgr *mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_cond);

  mm = bzla->mm;

  assert(
      !bzla_hashint_map_contains(domains, cond->id)
      || bzla_hashint_map_contains(domains, bzla_node_get_id(cond->e[idx_x])));
  x = bzla_hashint_map_get(domains, bzla_node_get_id(cond->e[idx_x]))->as_ptr;
  assert(bzla_is_inv_cond_const(bzla, x, t, s0, s1, idx_x, 0));

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    if (idx_x == 0)
    {
      tmp = bzla_bv_ite(mm, x->lo, s0, s1);
    }
    else if (idx_x == 1)
    {
      tmp = bzla_bv_ite(mm, s0, x->lo, s1);
    }
    else
    {
      tmp = bzla_bv_ite(mm, s0, s1, x->lo);
    }
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (d_res_x)
  {
    assert(idx_x || d_res_x);
    /* all non-random cases are determined in is_inv */
    assert(bzla_bvdomain_is_fixed(mm, d_res_x));
    res = bzla_bv_copy(mm, d_res_x->lo);
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

static BzlaPropComputeValue kind_to_cons[BZLA_NUM_OPS_NODE] = {
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

static BzlaPropComputeValue kind_to_cons_const[BZLA_NUM_OPS_NODE] = {
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

static BzlaPropComputeValue kind_to_inv[BZLA_NUM_OPS_NODE] = {
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

static BzlaPropComputeValue kind_to_inv_const[BZLA_NUM_OPS_NODE] = {
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
    [BZLA_COND_NODE]      = 0,  // special handling
};

static BzlaPropIsInv kind_to_is_inv[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = 0,  // always invertible
    [BZLA_BV_AND_NODE]    = bzla_is_inv_and,
    [BZLA_BV_CONCAT_NODE] = bzla_is_inv_concat,
    [BZLA_BV_EQ_NODE]     = 0,  // always invertible
    [BZLA_BV_MUL_NODE]    = bzla_is_inv_mul,
    [BZLA_BV_ULT_NODE]    = bzla_is_inv_ult,
    [BZLA_BV_SLICE_NODE]  = 0,  // always invertible
    [BZLA_BV_SLL_NODE]    = bzla_is_inv_sll,
    [BZLA_BV_SRL_NODE]    = bzla_is_inv_srl,
    [BZLA_BV_UDIV_NODE]   = bzla_is_inv_udiv,
    [BZLA_BV_UREM_NODE]   = bzla_is_inv_urem,
    [BZLA_COND_NODE]      = 0,  // special handling
};

static BzlaPropIsInv kind_to_is_inv_const[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_is_inv_add_const,
    [BZLA_BV_AND_NODE]    = bzla_is_inv_and_const,
    [BZLA_BV_CONCAT_NODE] = bzla_is_inv_concat_const,
    [BZLA_BV_EQ_NODE]     = bzla_is_inv_eq_const,
    [BZLA_BV_MUL_NODE]    = bzla_is_inv_mul_const,
    [BZLA_BV_ULT_NODE]    = bzla_is_inv_ult_const,
    [BZLA_BV_SLICE_NODE]  = 0,  // special handling
    [BZLA_BV_SLL_NODE]    = bzla_is_inv_sll_const,
    [BZLA_BV_SRL_NODE]    = bzla_is_inv_srl_const,
    [BZLA_BV_UDIV_NODE]   = bzla_is_inv_udiv_const,
    [BZLA_BV_UREM_NODE]   = bzla_is_inv_urem_const,
    [BZLA_COND_NODE]      = 0,  // special handling
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
        BzlaPropInfo prop = {exp, bzla_bv_copy(mm, t), 0};
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

uint64_t
bzla_proputils_select_move_prop(Bzla *bzla,
                                BzlaNode *root,
                                BzlaBitVector *bvroot,
                                int32_t idx_x,
                                BzlaNode **input,
                                BzlaBitVector **assignment)
{
  assert(bzla);
  assert(root);
  assert(bvroot);

  bool is_inv, pick_inv, has_fixed_bits;
  int32_t i, idx_s, idx_s0, idx_s1, nconst;
  uint64_t nprops;
  BzlaNode *cur, *real_cur;
  BzlaIntHashTable *domains;
  BzlaHashTableData *d;
  BzlaBitVector *bv_s[3] = {0, 0, 0}, *bv_t, *bv_s_new, *tmp;
  BzlaBvDomain *d_res_x;
  BzlaMemMgr *mm;
  uint32_t opt_prop_prob_use_inv_value;
  uint32_t opt_prop_const_bits;

  BzlaPropSelectPath select_path;
  BzlaPropIsInv is_inv_fun;

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
  d_res_x     = 0;

  opt_prop_prob_use_inv_value =
      bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE);
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS);

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
      if (opt_prop_const_bits)
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

      /* check if all paths are const, if yes -> conflict */
      for (i = 0, nconst = 0; i < real_cur->arity; i++)
      {
        bv_s[i] = (BzlaBitVector *) bzla_model_get_bv(bzla, real_cur->e[i]);
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

      /* we either select a consistent or inverse value
       * as path assignment, depending on the given probability p
       * -> if pick_inv then inverse else consistent */
      pick_inv =
          bzla_rng_pick_with_prob(&bzla->rng, opt_prop_prob_use_inv_value);
#ifndef NBZLALOG
      if (!pick_inv) ncons += 1;
#endif

      /* select path */
      select_path = kind_to_select_path[real_cur->kind];
      if (idx_x == -1) idx_x = select_path(bzla, real_cur, bv_t, bv_s);
      assert(idx_x >= 0 && idx_x < real_cur->arity);
#ifndef NDEBUG
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        BzlaPropInfo prop = {real_cur, bzla_bv_copy(bzla->mm, bv_t), idx_x};
        BZLA_PUSH_STACK(BZLA_PROP_SOLVER(bzla)->prop_path, prop);
      }
#endif

      d              = 0;
      has_fixed_bits = false;
      if (opt_prop_const_bits)
      {
        assert(domains);
        d = bzla_hashint_map_get(domains, bzla_node_get_id(real_cur->e[idx_x]));
        assert(d);
        has_fixed_bits = bzla_bvdomain_has_fixed_bits(mm, d->as_ptr);
        assert(d->as_ptr);
      }

      /* 1) check invertibility
       *    -> if not invertible, fall back to consistent value computation
       * 2) if not invertible, enforce consistent value computation
       * 3) if consistent value computation is selected or enforced,
       *    compute consistent value
       * 4) else compute inverse value
       */

      is_inv   = true;
      bv_s_new = 0;
      if (bzla_node_is_cond(real_cur))
      {
        if (has_fixed_bits)
        {
          assert(d);
          assert(d->as_ptr);
          if (idx_x == 0)
          {
            is_inv = bzla_is_inv_cond_const(
                bzla, d->as_ptr, bv_t, bv_s[1], bv_s[2], idx_x, &d_res_x);
          }
          else if (idx_x == 1)
          {
            is_inv = bzla_is_inv_cond_const(
                bzla, d->as_ptr, bv_t, bv_s[0], bv_s[2], idx_x, &d_res_x);
          }
          else
          {
            is_inv = bzla_is_inv_cond_const(
                bzla, d->as_ptr, bv_t, bv_s[0], bv_s[1], idx_x, &d_res_x);
          }

          /* not invertible counts as conflict */
          if (idx_x == 0)
          {
            idx_s0 = 1;
            idx_s1 = 2;
          }
          else if (idx_x == 1)
          {
            idx_s0 = 0;
            idx_s1 = 2;
          }
          else
          {
            idx_s0 = 0;
            idx_s1 = 1;
          }

          if (!is_inv)
          {
            if (!record_conflict(bzla, real_cur, bv_t, bv_s, idx_x, true))
            {
              /* non-recoverable conflict */
              if (d_res_x)
              {
                bzla_bvdomain_free(mm, d_res_x);
                d_res_x = 0;
              }
              break;
            }
          }

          /* compute new assignment */
          if (pick_inv && is_inv)
          {
            bv_s_new = bzla_proputils_inv_cond_const(bzla,
                                                     real_cur,
                                                     bv_t,
                                                     bv_s[idx_s0],
                                                     bv_s[idx_s1],
                                                     idx_x,
                                                     domains,
                                                     d_res_x);
          }
          else
          {
            /* inv_cond and cons_cond expect bv_s[0] as argument */
            bv_s_new = bzla_proputils_cons_cond(
                bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x);
          }
        }
        else
        {
          /* Note: We don't determine invertibility in the non-const case.
           *       Maybe we should in the future? TODO */

          /* compute new assignment */

          /* Note: inv_cond and cons_cond expect bv_s[0] as argument */
          if (pick_inv && is_inv)
          {
            bv_s_new = bzla_proputils_inv_cond(
                bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x);
          }
          else
          {
            bv_s_new = bzla_proputils_cons_cond(
                bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x);
          }
        }
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        if (has_fixed_bits)
        {
          assert(d);
          assert(d->as_ptr);
          is_inv =
              bzla_is_inv_slice_const(bzla,
                                      d->as_ptr,
                                      bv_t,
                                      bzla_node_bv_slice_get_upper(real_cur),
                                      bzla_node_bv_slice_get_lower(real_cur));

          if (!is_inv)
          {
            /* not invertible counts as conflict */
            if (!record_conflict(bzla, real_cur, bv_t, bv_s, idx_x, true))
            {
              /* non-recoverable conflict */
              break;
            }
          }
          bv_s_new =
              pick_inv && is_inv
                  ? bzla_proputils_inv_slice_const(
                      bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x)
                  : bzla_proputils_cons_slice(
                      bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x);
        }
        else
        {
          bv_s_new =
              pick_inv && is_inv
                  ? bzla_proputils_inv_slice(
                      bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x)
                  : bzla_proputils_cons_slice(
                      bzla, real_cur, bv_t, bv_s[0], idx_x, domains, d_res_x);
        }
      }
      else
      {
        BzlaPropComputeValue inv_value_fun, cons_value_fun, compute_value_fun;

        idx_s = idx_x ? 0 : 1;

        is_inv_fun = has_fixed_bits ? kind_to_is_inv_const[real_cur->kind]
                                    : kind_to_is_inv[real_cur->kind];
        if (is_inv_fun)
        {
          assert(!opt_prop_const_bits || d);
          is_inv = is_inv_fun(
              bzla, d ? d->as_ptr : 0, bv_t, bv_s[idx_s], idx_x, &d_res_x);
        }

        if (!is_inv)
        {
          /* not invertible counts as conflict */
          if (!record_conflict(bzla, real_cur, bv_t, bv_s, idx_x, true))
          {
            /* non-recoverable conflict */
            if (d_res_x)
            {
              bzla_bvdomain_free(mm, d_res_x);
              d_res_x = 0;
            }
            break;
          }
        }
        /* compute new assignment */
        cons_value_fun = has_fixed_bits ? kind_to_cons_const[real_cur->kind]
                                        : kind_to_cons[real_cur->kind];
        inv_value_fun = has_fixed_bits ? kind_to_inv_const[real_cur->kind]
                                       : kind_to_inv[real_cur->kind];

        compute_value_fun = pick_inv && is_inv ? inv_value_fun : cons_value_fun;

        bv_s_new = compute_value_fun(
            bzla, real_cur, bv_t, bv_s[idx_s], idx_x, domains, d_res_x);
      }

      if (d_res_x)
      {
        bzla_bvdomain_free(mm, d_res_x);
        d_res_x = 0;
      }
      if (!bv_s_new)
      {
        (void) record_conflict(bzla, real_cur, bv_t, bv_s, idx_x, false);
        break;
      }
#ifndef NBZLALOG
      a = bzla_bv_to_char(bzla->mm, bv_s_new);
      BZLALOG(2, "");
      BZLALOG(
          2, "%s value: %s", pick_inv && is_inv ? "inverse" : "consistent", a);
      bzla_mem_freestr(bzla->mm, a);
#endif
      /* propagate down */
      bzla_bv_free(bzla->mm, bv_t);
      bv_t = bv_s_new;
      cur  = real_cur->e[idx_x];

      nprops += 1;
      idx_x = -1;
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
                                     BzlaPropInfoStack *stack,
                                     BzlaPropInfoStack *res,
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
      BzlaPropInfo cloned_prop = {cloned_exp, cloned_bvexp, cloned_idx_x};
      BZLA_PUSH_STACK(*res, cloned_prop);
    }
  }
  assert(BZLA_COUNT_STACK(*stack) == BZLA_COUNT_STACK(*res));
  assert(BZLA_SIZE_STACK(*stack) == BZLA_SIZE_STACK(*res));
}

void
bzla_proputils_reset_prop_info_stack(BzlaMemMgr *mm, BzlaPropInfoStack *stack)
{
  assert(mm);
  assert(stack);

  while (!BZLA_EMPTY_STACK(*stack))
  {
    BzlaPropInfo prop = BZLA_POP_STACK(*stack);
    bzla_bv_free(mm, prop.bvexp);
  }
  BZLA_RESET_STACK(*stack);
}
