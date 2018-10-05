/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlaproputils.h"

#include "bzlainvutils.h"
#include "bzlaprintmodel.h"
#include "bzlaslsutils.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/* ========================================================================== */
/* Path selection (for down-propagation)                                      */
/* ========================================================================== */

static int32_t
select_path_non_const(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(exp->arity <= 2);
  assert(!bzla_node_is_bv_const(exp->e[0])
         || (exp->arity > 1 && !bzla_node_is_bv_const(exp->e[1])));

  uint32_t i;
  int32_t eidx;

  for (i = 0, eidx = -1; i < exp->arity; i++)
    if (bzla_node_is_bv_const(exp->e[i]))
    {
      eidx = i ? 0 : 1;
      break;
    }
  assert(exp->arity == 1 || !bzla_node_is_bv_const(exp->e[i ? 0 : 1]));
  return eidx;
}

static int32_t
select_path_random(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  return (int32_t) bzla_rng_pick_rand(&bzla->rng, 0, exp->arity - 1);
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

  int32_t eidx;

  eidx = select_path_non_const(add);
  if (eidx == -1) eidx = select_path_random(bzla, add);
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(add));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(add->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(add->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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
  int32_t i, eidx;
  BzlaBitVector *tmp;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  eidx = select_path_non_const(and);

  if (eidx == -1)
  {
    opt = bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL);

    if (opt == BZLA_PROP_PATH_SEL_RANDOM)
    {
      eidx = select_path_random(bzla, and);
    }
    else if (bzla_node_bv_get_width(bzla, and) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < and->arity; i++)
        if (bzla_bv_is_zero(s[i])) eidx = eidx == -1 ? i : -1;
      if (eidx == -1) eidx = select_path_random(bzla, and);
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
        if (bzla_bv_compare(tmp, t)) eidx = eidx == -1 ? i : -1;
        bzla_bv_free(mm, tmp);
      }
    }
    if (eidx == -1) eidx = select_path_random(bzla, and);
  }

  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(and));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(and->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(and->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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

  int32_t eidx;
  eidx = select_path_non_const(eq);
  if (eidx == -1) eidx = select_path_random(bzla, eq);
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(eq));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(eq->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(eq->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_ult(Bzla *bzla, BzlaNode *ult, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(t);
  assert(s);

  int32_t eidx;
  BzlaBitVector *bvmax;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  eidx = select_path_non_const(ult);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      if (bzla_bv_is_one(t))
      {
        /* 1...1 < s[1] */
        if (!bzla_bv_compare(s[0], bvmax)) eidx = 0;
        /* s[0] < 0 */
        if (bzla_bv_is_zero(s[1])) eidx = eidx == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random(bzla, ult);
  }

  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(ult));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(ult->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(ult->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_sll(Bzla *bzla, BzlaNode *sll, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(t);
  assert(s);

  int32_t eidx;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp;
  BzlaMemMgr *mm;

  eidx = select_path_non_const(sll);

  mm = bzla->mm;
  bw = bzla_bv_get_width(t);
  assert(bzla_bv_get_width(s[0]) == bw);
  assert(bzla_bv_get_width(s[1]) == bw);

  if (eidx == -1)
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
          eidx = 1;
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
        eidx = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of LSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(t, i))
          {
            eidx = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(s[0], i) != bzla_bv_get_bit(t, j + i))
          {
            eidx = eidx == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (eidx == -1) eidx = select_path_random(bzla, sll);
  }
DONE:
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(sll));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(sll->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(sll->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_srl(Bzla *bzla, BzlaNode *srl, BzlaBitVector *t, BzlaBitVector **s)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(t);
  assert(s);

  int32_t eidx;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp;
  BzlaMemMgr *mm;

  eidx = select_path_non_const(srl);

  mm = bzla->mm;
  bw = bzla_bv_get_width(t);
  assert(bzla_bv_get_width(s[0]) == bw);
  assert(bzla_bv_get_width(s[1]) == bw);

  if (eidx == -1)
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
          eidx = 1;
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
        eidx = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of MSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(t, bw - 1 - i))
          {
            eidx = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(s[0], bw - 1 - i)
              != bzla_bv_get_bit(t, bw - 1 - (j + i)))
          {
            eidx = eidx == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (eidx == -1) eidx = select_path_random(bzla, srl);
  }
DONE:
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(srl));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(srl->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(srl->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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
  int32_t eidx, lsb_s0, lsb_s1;
  bool iszero_s0, iszero_s1;

  eidx = select_path_non_const(mul);

  if (eidx == -1)
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
        if (iszero_s0) eidx = 0;
        if (iszero_s1) eidx = eidx == -1 ? 1 : -1;
      }
      /* t is odd but either s[0] or s[1] are even */
      else if (bzla_bv_get_bit(t, 0) && (!lsb_s0 || !lsb_s1))
      {
        if (!lsb_s0) eidx = 0;
        if (!lsb_s1) eidx = eidx == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in t < number of 0-LSBs in s[0|1] */
      else
      {
        ctz_bvmul = bzla_bv_get_num_trailing_zeros(t);
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(s[0])) eidx = 0;
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(s[1]))
          eidx = eidx == -1 ? 1 : -1;
      }
    }
    if (eidx == -1) eidx = select_path_random(bzla, mul);
  }
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(mul));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(mul->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(mul->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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

  int32_t eidx, cmp_udiv_max;
  BzlaBitVector *bvmax, *up, *lo, *tmp;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  eidx = select_path_non_const(udiv);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax        = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      cmp_udiv_max = bzla_bv_compare(t, bvmax);

      /* s[0] / s[1] = 1...1 -> choose e[1]
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        eidx = 1;
      else
      {
        /* 1...1 / e[0] = 0 -> choose e[0] */
        if (bzla_bv_is_zero(t) && !bzla_bv_compare(s[0], bvmax)) eidx = 0;
        /* s[0] < t -> choose e[0] */
        else if (bzla_bv_compare(s[0], t) < 0)
          eidx = 0;
        else
        {
          up  = bzla_bv_udiv(mm, s[0], t);
          lo  = bzla_bv_inc(mm, t);
          tmp = bzla_bv_udiv(mm, s[0], lo);
          bzla_bv_free(mm, lo);
          lo = bzla_bv_inc(mm, tmp);

          if (bzla_bv_compare(lo, up) > 0) eidx = 0;
          bzla_bv_free(mm, up);
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, tmp);
        }

        /* e[0] / 0 != 1...1 -> choose e[1] */
        if (bzla_bv_is_zero(s[1]) || bzla_bv_is_umulo(mm, s[1], t))
          eidx = eidx == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random(bzla, udiv);
  }

  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(udiv));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(udiv->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(udiv->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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

  int32_t eidx;
  BzlaBitVector *bvmax, *sub, *tmp;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  eidx = select_path_non_const(urem);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax = bzla_bv_ones(mm, bzla_bv_get_width(s[0]));
      sub   = bzla_bv_sub(mm, s[0], t);
      tmp   = bzla_bv_dec(mm, s[0]);

      /* t = 1...1 -> s[0] = 1...1 and s[1] = 0...0 */
      if (!bzla_bv_compare(t, bvmax))
      {
        if (!bzla_bv_is_zero(s[1])) eidx = 1;
        if (bzla_bv_compare(s[0], bvmax)) eidx = eidx == -1 ? 0 : -1;
      }
      /* t > 0 and s[1] = 1 */
      else if (!bzla_bv_is_zero(t) && bzla_bv_is_one(s[1]))
      {
        eidx = 1;
      }
      /* 0 < s[1] <= t */
      else if (!bzla_bv_is_zero(s[1]) && bzla_bv_compare(s[1], t) <= 0)
      {
        eidx = eidx == -1 ? 1 : -1;
      }
      /* s[0] < t or
       * s[0] > t and s[0] - t <= t or
       *                 and s[0] - 1 = t */
      else if (bzla_bv_compare(s[0], t) < 0
               || (bzla_bv_compare(s[0], t) > 0
                   && (bzla_bv_compare(sub, t) <= 0
                       || !bzla_bv_compare(tmp, t))))
      {
        eidx = 0;
      }

      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, bvmax);
      bzla_bv_free(mm, sub);
    }

    if (eidx == -1) eidx = select_path_random(bzla, urem);
  }

  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(urem));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(urem->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(urem->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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

  int32_t eidx;
  uint32_t bw_concat;
  BzlaBitVector *tmp;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  eidx = select_path_non_const(concat);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* s[0] o s[1] = t
       * -> s[0] resp. s[1] must match with t */
      bw_concat = bzla_bv_get_width(t);
      tmp       = bzla_bv_slice(
          mm, t, bw_concat - 1, bw_concat - bzla_bv_get_width(s[0]));
      if (bzla_bv_compare(tmp, s[0])) eidx = 0;
      bzla_bv_free(mm, tmp);
      tmp = bzla_bv_slice(mm, t, bzla_bv_get_width(s[1]) - 1, 0);
      if (bzla_bv_compare(tmp, s[1])) eidx = eidx == -1 ? 1 : -1;
      bzla_bv_free(mm, tmp);
    }

    if (eidx == -1) eidx = select_path_random(bzla, concat);
  }

  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(concat));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(concat->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(concat->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
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
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(slice));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(slice->e[0]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: 0");
#endif

  return 0;
}

static int32_t
select_path_cond(Bzla *bzla,
                 BzlaNode *cond,
                 BzlaBitVector *bvcond,
                 BzlaBitVector **s)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(bvcond);
  assert(s);

  bool e1const, e2const;
  int32_t eidx;
  uint32_t prob;
  BzlaBitVector *s0;

  (void) bvcond;

  s0 = *s;
  assert(s0);

  if (bzla_node_is_bv_const(cond->e[0]))
    eidx = cond->e[0] == bzla->true_exp ? 1 : 2;
  else
  {
    e1const = bzla_node_is_bv_const(cond->e[1]);
    e2const = bzla_node_is_bv_const(cond->e[2]);

    /* flip condition
     *
     * if either the 'then' or 'else' branch is const
     * with probability BZLA_OPT_PROP_FLIP_COND_CONST_PROB,
     * which is dynamically updated (depending on the number
     * times this case has already bin encountered)
     *
     * else with probability BZLA_OPT_PROP_FLIP_COND_PROB,
     * which is constant and will not be updated */
    if (((e1const && bzla_bv_is_true(s0)) || (e2const && bzla_bv_is_false(s0)))
        && bzla_rng_pick_with_prob(
            &bzla->rng,
            (prob = bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND_CONST))))
    {
      eidx = 0;

      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        BzlaPropSolver *slv;
        slv = BZLA_PROP_SOLVER(bzla);
        if (++slv->nflip_cond_const
            == bzla_opt_get(bzla, BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          slv->nflip_cond_const = 0;
          slv->flip_cond_const_prob_delta =
              prob == 0
                  ? 100
                  : (prob == 1000 ? -100 : slv->flip_cond_const_prob_delta);
          bzla_opt_set(bzla,
                       BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
                       prob + slv->flip_cond_const_prob_delta);
        }
      }
      else
      {
        BzlaSLSSolver *slv;
        slv = BZLA_SLS_SOLVER(bzla);
        if (++slv->prop_nflip_cond_const
            == bzla_opt_get(bzla, BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          slv->prop_nflip_cond_const = 0;
          slv->prop_flip_cond_const_prob_delta =
              prob == 0 ? 100
                        : (prob == 1000 ? -100
                                        : slv->prop_flip_cond_const_prob_delta);
          bzla_opt_set(bzla,
                       BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
                       prob + slv->prop_flip_cond_const_prob_delta);
        }
      }
    }
    else if (bzla_rng_pick_with_prob(
                 &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND)))
    {
      eidx = 0;
    }
    /* assume cond to be fixed and select enabled branch */
    else
    {
      eidx = bzla_bv_is_true(s0) ? 1 : 2;
    }
  }

#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;

  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(cond));
  a = bzla_bv_to_char(mm, s0);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(cond->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bzla_model_get_bv(bzla, cond->e[1]));
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(cond->e[1]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bzla_model_get_bv(bzla, cond->e[2]));
  BZLALOG(2, "       e[2]: %s (%s)", bzla_util_node2string(cond->e[2]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

/* ========================================================================== */
/* Consistent value computation                                               */
/* ========================================================================== */

#ifdef NDEBUG
static BzlaBitVector *inv_slice_bv(
    Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t);
static BzlaBitVector *inv_cond_bv(
    Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t);
#endif

static BzlaBitVector *
cons_add_bv(
    Bzla *bzla, BzlaNode *add, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(add->e[eidx]));

  (void) add;
  (void) s;
  (void) eidx;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_add++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  return bzla_bv_new_random(bzla->mm, &bzla->rng, bzla_bv_get_width(t));
}

static BzlaBitVector *
cons_and_bv(
    Bzla *bzla, BzlaNode *and, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(and->e[eidx]));

  uint32_t i, bw;
  BzlaBitVector *res;
  BzlaUIntStack dcbits;
  bool b;

  (void) s;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_and++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(bzla->mm, dcbits);

  res = bzla_bv_copy(bzla->mm, bzla_model_get_bv(bzla, and->e[eidx]));

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

static BzlaBitVector *
cons_eq_bv(
    Bzla *bzla, BzlaNode *eq, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(eq->e[eidx]));

  (void) t;

  BzlaBitVector *res;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_eq++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  if (bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_EQ_FLIP)))
  {
    res = bzla_bv_copy(bzla->mm, bzla_model_get_bv(bzla, eq->e[eidx]));
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
cons_ult_bv(
    Bzla *bzla, BzlaNode *ult, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BzlaBitVector *bvmax, *zero, *tmp, *res;
  BzlaMemMgr *mm;

  (void) ult;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_ult++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(s);
  isult = !bzla_bv_is_zero(t);
  zero  = bzla_bv_new(mm, bw);
  bvmax = bzla_bv_ones(mm, bw);

  if (eidx && isult)
  {
    /* s < res = 1  ->  res > 0 */
    tmp = bzla_bv_one(mm, bw);
    res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
    bzla_bv_free(mm, tmp);
  }
  else if (!eidx && isult)
  {
    /* res < s = 1  ->  0 <= res < 1...1 */
    tmp = bzla_bv_dec(mm, bvmax);
    res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
    bzla_bv_free(mm, tmp);
  }
  else
  {
    res = bzla_bv_new_random(mm, &bzla->rng, bw);
  }

  bzla_bv_free(mm, bvmax);
  bzla_bv_free(mm, zero);

  return res;
}

static BzlaBitVector *
cons_sll_bv(
    Bzla *bzla, BzlaNode *sll, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(t);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(sll->e[eidx]));

  uint32_t i, bw, ctz_bvsll, shift;
  BzlaBitVector *res, *bv_shift;
  BzlaMemMgr *mm;

  (void) sll;
  (void) s;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_sll++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm = bzla->mm;
  bw = bzla_bv_get_width(t);

  ctz_bvsll = bzla_bv_get_num_trailing_zeros(t);
  shift     = bzla_rng_pick_rand(
      &bzla->rng, 0, ctz_bvsll == bw ? ctz_bvsll - 1 : ctz_bvsll);
  bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);

  if (eidx)
  {
    res = bv_shift;
  }
  else
  {
    res = bzla_bv_srl(mm, t, bv_shift);
    for (i = 0; i < shift; i++)
    {
      bzla_bv_set_bit(res, bw - 1 - i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

static BzlaBitVector *
cons_srl_bv(
    Bzla *bzla, BzlaNode *srl, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(t);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(srl->e[eidx]));

  uint32_t i, shift, bw;
  BzlaBitVector *res, *bv_shift;
  BzlaMemMgr *mm;

  (void) srl;
  (void) s;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_srl++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm = bzla->mm;
  bw = bzla_bv_get_width(t);

  for (i = 0; i < bw; i++)
  {
    if (bzla_bv_get_bit(t, bw - 1 - i)) break;
  }

  shift    = bzla_rng_pick_rand(&bzla->rng, 0, i == bw ? i - 1 : i);
  bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);

  if (eidx)
  {
    res = bv_shift;
  }
  else
  {
    res = bzla_bv_sll(mm, t, bv_shift);
    for (i = 0; i < shift; i++)
    {
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

static BzlaBitVector *
cons_mul_bv(
    Bzla *bzla, BzlaNode *mul, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(mul->e[eidx]));

  uint32_t r, bw, ctz_res, ctz_bvmul;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  (void) mul;
  (void) s;
  (void) eidx;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_mul++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

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

static BzlaBitVector *
cons_udiv_bv(Bzla *bzla,
             BzlaNode *udiv,
             BzlaBitVector *t,
             BzlaBitVector *s,
             int32_t eidx)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(udiv->e[eidx]));

  uint32_t bw;
  BzlaBitVector *res, *tmp, *tmp_s, *zero, *one, *bvmax;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(t);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  bvmax = bzla_bv_ones(mm, bw);

  (void) udiv;
  (void) s;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_udiv++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  if (eidx)
  {
    /* -> t = 1...1 then res = 0 or res = 1
     * -> else choose res s.t. res * t does not overflow */
    if (!bzla_bv_compare(t, bvmax))
      res = bzla_bv_uint64_to_bv(mm, bzla_rng_pick_rand(&bzla->rng, 0, 1), bw);
    else
    {
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, bvmax);
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
      tmp = bzla_bv_dec(mm, bvmax);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
    else if (!bzla_bv_compare(t, bvmax))
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      tmp_s = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, bvmax);
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
  bzla_bv_free(mm, bvmax);
  return res;
}

static BzlaBitVector *
cons_urem_bv(Bzla *bzla,
             BzlaNode *urem,
             BzlaBitVector *t,
             BzlaBitVector *s,
             int32_t eidx)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(urem->e[eidx]));

  uint32_t bw;
  BzlaBitVector *res, *bvmax, *tmp;
  BzlaMemMgr *mm;

  (void) urem;
  (void) s;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_urem++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  mm    = bzla->mm;
  bw    = bzla_bv_get_width(t);
  bvmax = bzla_bv_ones(mm, bw);

  if (eidx)
  {
    /* t = 1...1  ->  res = 0 */
    if (!bzla_bv_compare(t, bvmax))
    {
      res = bzla_bv_new(mm, bw);
    }
    /* else res > t */
    else
    {
      tmp = bzla_bv_inc(mm, t);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    /* t = 1...1  ->  res = 1...1 */
    if (!bzla_bv_compare(t, bvmax))
    {
      res = bzla_bv_copy(mm, bvmax);
    }
    /* else res >= t */
    else
    {
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, t, bvmax);
    }
  }

  bzla_bv_free(mm, bvmax);
  return res;
}

static BzlaBitVector *
cons_concat_bv(Bzla *bzla,
               BzlaNode *concat,
               BzlaBitVector *t,
               BzlaBitVector *s,
               int32_t eidx)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(t);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(concat->e[eidx]));

  int32_t idx, bw_t, bw_s;
  uint32_t r;
  BzlaBitVector *res;
  const BzlaBitVector *bvcur;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_concat++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  idx  = eidx ? 0 : 1;
  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);

  /* If one operand is const, with BZLA_OPT_CONC_FLIP_PROB
   * either slice bits out of current assignment and flip max. one bit
   * randomly, or slice bits out of given assignment 's'.  */

  if (bzla_node_is_bv_const(concat->e[idx])
      && bzla_rng_pick_with_prob(
          &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_CONC_FLIP)))
  {
    bvcur = bzla_model_get_bv(bzla, concat);
    res   = eidx ? bzla_bv_slice(bzla->mm, bvcur, bw_t - bw_s - 1, 0)
               : bzla_bv_slice(bzla->mm, bvcur, bw_t - 1, bw_s);
    r = bzla_rng_pick_rand(&bzla->rng, 0, bzla_bv_get_width(res));
    if (r) bzla_bv_flip_bit(res, r - 1);
  }
  else
  {
    res = eidx ? bzla_bv_slice(bzla->mm, t, bw_t - bw_s - 1, 0)
               : bzla_bv_slice(bzla->mm, t, bw_t - 1, bw_s);
  }
  return res;
}

static BzlaBitVector *
cons_slice_bv(Bzla *bzla,
              BzlaNode *slice,
              BzlaBitVector *t,
              BzlaBitVector *s,
              int32_t eidx)
{
  return inv_slice_bv(bzla, slice, t, s, eidx);
}

static BzlaBitVector *
cons_cond_bv(Bzla *bzla,
             BzlaNode *cond,
             BzlaBitVector *bvcond,
             BzlaBitVector *s,
             int32_t eidx)
{
  return inv_cond_bv(bzla, cond, bvcond, s, eidx);
}

/* ========================================================================== */
/* Inverse value computation                                                  */
/* ========================================================================== */

static BzlaBitVector *
res_rec_conf(Bzla *bzla,
             BzlaNode *exp,
             BzlaNode *e,
             BzlaBitVector *t,
             BzlaBitVector *s,
             int32_t eidx,
             BzlaBitVector *(*fun)(
                 Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t),
             char *op)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(e);
  assert(t);
  assert(s);
  assert(op);
  (void) op;
  (void) e;

  bool is_recoverable;
  uint32_t no_move_on_conflict, prop_entailed;
  BzlaBitVector *res;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  is_recoverable      = bzla_node_is_bv_const(e) ? false : true;
  no_move_on_conflict = bzla_opt_get(bzla, BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT);

  res = no_move_on_conflict && !is_recoverable ? 0 : fun(bzla, exp, t, s, eidx);
  assert(no_move_on_conflict || res);

#ifndef NDEBUG
  char *str_s = bzla_bv_to_char(mm, s);
  char *str_t = bzla_bv_to_char(mm, t);
  BZLALOG(2, "");
  if (eidx)
    BZLALOG(2,
            "%s CONFLICT (@%d): %s := %s %s x",
            is_recoverable ? "recoverable" : "non-recoverable",
            bzla_node_get_id(exp),
            str_t,
            str_s,
            op);
  else
    BZLALOG(2,
            "%s CONFLICT (@%d): %s := x %s %s",
            is_recoverable ? "recoverable" : "non-recoverable",
            bzla_node_get_id(exp),
            str_t,
            op,
            str_s);
  bzla_mem_freestr(mm, str_s);
  bzla_mem_freestr(mm, str_t);
#endif
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
    BzlaPropSolver *slv = BZLA_PROP_SOLVER(bzla);
    if (is_recoverable)
    {
#ifndef NDEBUG
      /* fix counters since we always increase the counter, even in the conflict
       * case  (except for slice and cond where inv = cons) */
      switch (exp->kind)
      {
        case BZLA_BV_ADD_NODE: slv->stats.inv_add -= 1; break;
        case BZLA_BV_AND_NODE: slv->stats.inv_and -= 1; break;
        case BZLA_BV_EQ_NODE: slv->stats.inv_eq -= 1; break;
        case BZLA_BV_ULT_NODE: slv->stats.inv_ult -= 1; break;
        case BZLA_BV_SLL_NODE: slv->stats.inv_sll -= 1; break;
        case BZLA_BV_SRL_NODE: slv->stats.inv_srl -= 1; break;
        case BZLA_BV_MUL_NODE: slv->stats.inv_mul -= 1; break;
        case BZLA_BV_UDIV_NODE: slv->stats.inv_udiv -= 1; break;
        case BZLA_BV_UREM_NODE: slv->stats.inv_urem -= 1; break;
        case BZLA_BV_CONCAT_NODE: slv->stats.inv_concat -= 1; break;
        default:
          assert(bzla_node_is_bv_slice(exp) || bzla_node_is_bv_cond(exp));
          /* do not decrease, we do not call cons function in conflict case */
      }
#endif
      slv->stats.rec_conf += 1;
      /* recoverable conflict, push entailed propagation */
      assert(exp->arity == 2);
      prop_entailed = bzla_opt_get(bzla, BZLA_OPT_PROP_ENTAILED);
      if (prop_entailed != BZLA_PROP_ENTAILED_OFF)
      {
        BzlaPropInfo prop = {exp, bzla_bv_copy(mm, t), eidx ? 0 : 1};
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
      /* non-recoverable conflict, entailed propagations are thus invalid */
      bzla_proputils_reset_prop_info_stack(mm, &slv->toprop);
    }
  }
  else
  {
    if (is_recoverable)
      BZLA_SLS_SOLVER(bzla)->stats.move_prop_rec_conf += 1;
    else
      BZLA_SLS_SOLVER(bzla)->stats.move_prop_non_rec_conf += 1;
  }

  return res;
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static void
check_result_binary_dbg(Bzla *bzla,
                        BzlaBitVector *(*fun)(BzlaMemMgr *,
                                              const BzlaBitVector *,
                                              const BzlaBitVector *),
                        BzlaNode *exp,
                        BzlaBitVector *s,
                        BzlaBitVector *t,
                        BzlaBitVector *res,
                        int32_t eidx,
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

  tmp = eidx ? fun(bzla->mm, s, res) : fun(bzla->mm, res, s);
  assert(!bzla_bv_compare(tmp, t));
  str_t   = bzla_bv_to_char(bzla->mm, t);
  str_s   = bzla_bv_to_char(bzla->mm, s);
  str_res = bzla_bv_to_char(bzla->mm, res);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s %s %s",
          eidx,
          bzla_util_node2string(exp),
          str_t,
          eidx ? str_s : str_res,
          op,
          eidx ? str_res : str_s);
  bzla_bv_free(bzla->mm, tmp);
  bzla_mem_freestr(bzla->mm, str_t);
  bzla_mem_freestr(bzla->mm, str_s);
  bzla_mem_freestr(bzla->mm, str_res);
}
#endif

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_add_bv(
    Bzla *bzla, BzlaNode *add, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(add->e[eidx]));

  BzlaBitVector *res;

  (void) add;
  (void) eidx;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_add++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  /**
   * invertibility condition: true
   *
   * res +   s = t   |->   res = t - s
   * s   + res = t   |
   */

  res = bzla_bv_sub(bzla->mm, t, s);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_add, add, s, t, res, eidx, "+");
#endif
  return res;
}

#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_and_bv(
    Bzla *bzla, BzlaNode *and, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(and->e[eidx]));

  uint32_t i, bw;
  int32_t bit_and, bit_e;
  BzlaNode *e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  BzlaUIntStack dcbits;
  bool b;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_and++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = and->e[eidx ? 0 : 1];
  assert(e);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_and(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, and, e, t, s, eidx, cons_and_bv, "AND");
  }

  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(mm, dcbits);

  res = bzla_bv_copy(mm, bzla_model_get_bv(bzla, and->e[eidx]));
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
  check_result_binary_dbg(bzla, bzla_bv_and, and, s, t, res, eidx, "AND");
#endif

  BZLA_RELEASE_STACK(dcbits);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_eq_bv(
    Bzla *bzla, BzlaNode *eq, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(eq->e[eidx]));

  BzlaBitVector *res;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_eq++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

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
        res = bzla_bv_copy(bzla->mm, bzla_model_get_bv(bzla, eq->e[eidx]));
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
  check_result_binary_dbg(bzla, bzla_bv_eq, eq, s, t, res, eidx, "=");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_ult_bv(
    Bzla *bzla, BzlaNode *ult, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BzlaNode *e;
  BzlaBitVector *res, *zero, *one, *bvmax, *tmp;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_ult++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = ult->e[eidx ? 0 : 1];
  assert(e);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_ult(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, ult, e, t, s, eidx, cons_ult_bv, "<");
  }

  bw    = bzla_bv_get_width(s);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  bvmax = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(t);

  res = 0;

  if (eidx)
  {
    assert(!isult || bzla_bv_compare(s, bvmax)); /* CONFLICT: 1...1 < e[1] */
    if (!isult)
    {
      /* s >= e[1] -------------------------------------------------------- */
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, s);
    }
    else
    {
      /* s < e[1] --------------------------------------------------------- */
      tmp = bzla_bv_add(mm, s, one);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    assert(!isult || !bzla_bv_is_zero(s)); /* CONFLICT: e[0] < 0  */
    if (!isult)
    {
      /* e[0] >= s -------------------------------------------------------- */
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, s, bvmax);
    }
    else
    {
      /* e[0] < s --------------------------------------------------------- */
      tmp = bzla_bv_sub(mm, s, one);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_ult, ult, s, t, res, eidx, "<");
#endif
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, one);
  bzla_bv_free(mm, bvmax);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: sll                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_sll_bv(
    Bzla *bzla, BzlaNode *sll, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(t);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(sll->e[eidx]));

  uint32_t bw, i, ctz_s, ctz_t, shift;
  BzlaNode *e;
  BzlaBitVector *res, *tmp, *bvmax;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_sll++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = sll->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(t);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_sll(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, sll, e, t, s, eidx, cons_sll_bv, "<<");
  }

  res   = 0;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  /* ------------------------------------------------------------------------
   * s << e[1] = t
   *
   * -> identify possible shift value via zero LSB in t
   *    (considering zero LSB in s)
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 << e[1] = 0...0 -> choose res randomly ----------------------- */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /* -> ctz(s) > ctz (t) -> conflict
       * -> shift = ctz(t) - ctz(s)
       *      -> if t = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       * -> else conflict
       * -------------------------------------------------------------------- */
      ctz_s = bzla_bv_get_num_trailing_zeros(s);
      assert(ctz_s <= ctz_t); /* CONFLICT: ctz_s > ctz_t */
      shift = ctz_t - ctz_s;
      if (bzla_bv_is_zero(t))
      {
        /* x...x0 << e[1] = 0...0
         * -> choose random shift <= res < bw
         * ---------------------------------------------------------------- */
        bvmax = bzla_bv_ones(mm, bw);
        tmp   = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        res   = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
        bzla_bv_free(mm, bvmax);
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
   * e[0] << s = t
   *
   * -> e[0] = t >> s
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
  check_result_binary_dbg(bzla, bzla_bv_sll, sll, s, t, res, eidx, "<<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_srl_bv(
    Bzla *bzla, BzlaNode *srl, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(t);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(srl->e[eidx]));

  uint32_t bw, i, clz_s, clz_t, shift;
  BzlaNode *e;
  BzlaBitVector *res, *bvmax, *tmp;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_srl++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = srl->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(t);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_srl(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, srl, e, t, s, eidx, cons_srl_bv, ">>");
  }

  res   = 0;
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  /* ------------------------------------------------------------------------
   * s >> e[1] = t
   *
   * -> identify possible shift value via zero MSBs in t
   *    (considering zero MSBs in s)
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 >> e[1] = 0...0 -> choose random res ------------------------- */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /* clz(s) > clz(t) -> conflict
       *
       * -> shift = clz(t) - clz(s)
       *      -> if t = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       * -> else conflict
       * -------------------------------------------------------------------- */
      clz_s = bzla_bv_get_num_leading_zeros(s);
      assert(clz_s <= clz_t);
      shift = clz_t - clz_s;
      if (bzla_bv_is_zero(t))
      {
        /* x...x0 >> e[1] = 0...0
         * -> choose random shift <= res < bw
         * ---------------------------------------------------------------- */
        bvmax = bzla_bv_ones(mm, bw);
        tmp   = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        res   = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
        bzla_bv_free(mm, bvmax);
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
   * e[0] >> s = t
   *
   * -> e[0] = t << s
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
  check_result_binary_dbg(bzla, bzla_bv_srl, srl, s, t, res, eidx, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_mul_bv(
    Bzla *bzla, BzlaNode *mul, BzlaBitVector *t, BzlaBitVector *s, int32_t eidx)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(mul->e[eidx]));

  int32_t lsb_s, ispow2_s;
  uint32_t i, j, bw;
  BzlaBitVector *res, *inv, *tmp, *tmp2;
  BzlaMemMgr *mm;
  BzlaNode *e;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_mul++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = mul->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(t);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_mul(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, mul, e, t, s, eidx, cons_mul_bv, "*");
  }

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
    /* s = 0 -> if t = 0 choose random value, else conflict ----------------- */
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

        /* res = t >> n with all bits shifted in set randomly
         * (note: bw is not necessarily power of 2 -> do not use srl)
         * ---------------------------------------------------------------- */
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

        /* c' = t >> n (with all bits shifted in set randomly)
         * (note: bw is not necessarily power of 2 -> do not use srl)
         * -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
         * ---------------------------------------------------------------- */
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
  check_result_binary_dbg(bzla, bzla_bv_mul, mul, s, t, res, eidx, "*");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_udiv_bv(Bzla *bzla,
            BzlaNode *udiv,
            BzlaBitVector *t,
            BzlaBitVector *s,
            int32_t eidx)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(udiv->e[eidx]));

  uint32_t bw;
  BzlaNode *e;
  BzlaBitVector *res, *lo, *up, *one, *bvmax, *tmp;
  BzlaMemMgr *mm;
  BzlaRNG *rng;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_udiv++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  rng = &bzla->rng;
  e   = udiv->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(s);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_udiv(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, udiv, e, t, s, eidx, cons_udiv_bv, "/");
  }

  one   = bzla_bv_one(mm, bw);
  bvmax = bzla_bv_ones(mm, bw); /* 2^bw - 1 */

  res = 0;

  /* ------------------------------------------------------------------------
   * s / e[1] = t
   *
   * -> if t = 2^bw - 1: + s = t = 2^bw - 1 -> e[1] = 1 or e[1] = 0
   *                     + s != t -> e[1] = 0
   * -> if t = 0 and 0 < s < 2^bw - 1 choose random e[1] > s
   *             and s = 0            choose random e[1] > 0
   *             else conflict
   * -> if s < t -> conflict
   * -> if t is a divisor of s choose with 0.5 prob out of
   *      + e[1] = t / s
   *      + choose s s.t. s / e[1] = t
   * -> else choose s s.t. s / e[1] = t
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (!bzla_bv_compare(t, bvmax))
    {
      if (!bzla_bv_compare(s, t) && bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
        /* s = t = 2^bw - 1 -> choose either e[1] = 0 or e[1] = 1
         * with prob 0.5
         * ------------------------------------------------------------------ */
        res = bzla_bv_one(mm, bw);
      }
      else
      {
        /* t = 2^bw - 1 and s != t -> e[1] = 0 ------------------------------ */
        res = bzla_bv_new(mm, bw);
      }
    }
    else if (bzla_bv_is_zero(t))
    {
      if (bzla_bv_is_zero(s))
      {
        /* t = 0 and s = 0 -> choose random e[1] > 0 ------------------------ */
        res = bzla_bv_new_random_range(mm, rng, bw, one, bvmax);
      }
      else
      {
        assert(bzla_bv_compare(s, bvmax)); /* CONFLICT: s = ~0  and t = 0 */

        /* t = 0 and 0 < s < 2^bw - 1 -> choose random e[1] > s ------------- */
        tmp = bzla_bv_inc(mm, s);
        res = bzla_bv_new_random_range(mm, rng, bw, tmp, bvmax);
        bzla_bv_free(mm, tmp);
      }
    }
    else
    {
      assert(bzla_bv_compare(s, t) >= 0); /* CONFLICT: s < t */

      /* if t is a divisor of s, choose e[1] = s / t
       * with prob = 0.5 and a s s.t. s / e[1] = t otherwise
       * -------------------------------------------------------------------- */
      tmp = bzla_bv_urem(mm, s, t);
      if (bzla_bv_is_zero(tmp) && bzla_rng_pick_with_prob(rng, 500))
      {
        bzla_bv_free(mm, tmp);
        res = bzla_bv_udiv(mm, s, t);
      }
      else
      {
        /* choose e[1] out of all options that yield s / e[1] = t
         * Note: udiv always truncates the results towards 0.
         * ------------------------------------------------------------------ */

        /* determine upper and lower bounds for e[1]:
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

        /* choose lo <= e[1] <= up ---------------------------------------- */
        res = bzla_bv_new_random_range(mm, rng, bw, lo, up);
        bzla_bv_free(mm, lo);
        bzla_bv_free(mm, up);
      }
    }
  }

  /* ------------------------------------------------------------------------
   * e[0] / s = t
   *
   * -> if t = 2^bw - 1 and s = 1 e[0] = 2^bw-1
   *                    and s = 0, choose random e[0] > 0
   *                    and s > 0 -> conflict
   * -> if s = 0 and t < 2^bw - 1 -> conflict
   * -> if s * t does not overflow, choose with 0.5 prob out of
   *      + e[0] = s * t
   *      + choose s s.t. e[0] / s = t
   * -> else choose s s.t. e[0] / s = t
   * ------------------------------------------------------------------------ */
  else
  {
    if (!bzla_bv_compare(t, bvmax))
    {
      if (!bzla_bv_compare(s, one))
      {
        /* t = 2^bw-1 and s = 1 -> e[0] = 2^bw-1 ---------------------------- */
        res = bzla_bv_copy(mm, bvmax);
      }
      else
      {
        assert(bzla_bv_is_zero(s)); /* CONFLICT: t = ~0 and s != 0 */
        /* t = 2^bw - 1 and s = 0 -> choose random e[0] --------------------- */
        res = bzla_bv_new_random(mm, rng, bw);
      }
    }
    else
    {
      /* if s * t does not overflow, choose e[0] = s * t
       * with prob = 0.5 and a s s.t. e[0] / s = t otherwise */

      assert(!bzla_bv_is_umulo(mm, s, t)); /* CONFLICT: overflow: s * t */
      if (bzla_rng_pick_with_prob(rng, 500))
        res = bzla_bv_mul(mm, s, t);
      else
      {
        /* choose e[0] out of all options that yield
         * e[0] / s = t
         * Note: udiv always truncates the results towards 0.
         * ---------------------------------------------------------------- */

        /* determine upper and lower bounds for e[0]:
         * up = s * (budiv + 1) - 1
         *      if s * (t + 1) does not overflow
         *      else 2^bw - 1
         * lo = s * t */
        lo  = bzla_bv_mul(mm, s, t);
        tmp = bzla_bv_inc(mm, t);
        if (bzla_bv_is_umulo(mm, s, tmp))
        {
          bzla_bv_free(mm, tmp);
          up = bzla_bv_copy(mm, bvmax);
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

  bzla_bv_free(mm, bvmax);
  bzla_bv_free(mm, one);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_udiv, udiv, s, t, res, eidx, "/");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_urem_bv(Bzla *bzla,
            BzlaNode *urem,
            BzlaBitVector *t,
            BzlaBitVector *s,
            int32_t eidx)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(urem->e[eidx]));

  uint32_t bw, cnt;
  int32_t cmp;
  BzlaNode *e;
  BzlaBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_urem++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = urem->e[eidx ? 0 : 1];
  assert(e);

  bw = bzla_bv_get_width(t);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_urem(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, urem, e, t, s, eidx, cons_urem_bv, "%");
  }

  bvmax = bzla_bv_ones(mm, bw); /* 2^bw - 1 */
  one   = bzla_bv_one(mm, bw);

  res = 0;

  /* -----------------------------------------------------------------------
   * s % e[1] = t
   *
   * -> if t = 1...1 -> s = 1...1 and e[1] = 0...0, else conflict
   * -> if s = t, choose either e[1] = 0 or some e[1] > t randomly
   * -> if t > 0 and t = s - 1, conflict
   * -> if s > t, e[1] = ((s - t) / n) > t, else conflict
   * -> if s < t, conflict
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (!bzla_bv_compare(t, bvmax))
    {
      /* CONFLICT: t = ~0 but s != ~0 */
      assert(!bzla_bv_compare(s, bvmax));

      /* s % e[1] = ~0 -> s = ~0, e[1] = 0 -------------------------- */
      res = bzla_bv_new(mm, bw);
    }
    else
    {
      cmp = bzla_bv_compare(s, t);

      if (cmp == 0)
      {
        /* s = t, choose either e[1] = 0 or random e[1] > t ----------------- */

        /* choose e[1] = 0 with prob = 0.25*/
        if (bzla_rng_pick_with_prob(&bzla->rng, 250)) res = bzla_bv_new(mm, bw);
        /* t < res <= 2^bw - 1 */
        else
        {
          tmp = bzla_bv_add(mm, t, one);
          res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
          bzla_bv_free(mm, tmp);
        }
      }
      else
      {
        assert(cmp > 0); /* CONFLICT: s < t */

        /* s > t, e[1] = (s - t) / n ---------------------------------------- */
#ifndef NDEBUG
        if (!bzla_bv_is_zero(t))
        {
          tmp = bzla_bv_dec(mm, s);
          /* CONFLICT: t = s - 1 -> s % e[1] = s - 1 > not possible if t > 0 */
          assert(bzla_bv_compare(t, tmp));
          bzla_bv_free(mm, tmp);
        }
#endif

        sub = bzla_bv_sub(mm, s, t);

        assert(bzla_bv_compare(sub, t) > 0); /* CONFLICT: s - t <= t */

        /* choose either n = 1 or 1 <= n < (s - t) / t
         * with prob = 0.5
         * ---------------------------------------------------------------- */

        if (bzla_rng_pick_with_prob(&bzla->rng, 500))
        {
          res = bzla_bv_copy(mm, sub);
        }
        else
        {
          /* 1 <= n < (s - t) / t (non-truncating)
           * (note: div truncates towards 0!)
           * -------------------------------------------------------------- */

          if (bzla_bv_is_zero(t))
          {
            /* t = 0 -> 1 <= n <= s --------------------------------------- */
            up = bzla_bv_copy(mm, s);
          }
          else
          {
            /* e[1] > t
             * -> (s - t) / n > t
             * -> (s - t) / t > n
             * ------------------------------------------------------------ */
            tmp  = bzla_bv_urem(mm, sub, t);
            tmp2 = bzla_bv_udiv(mm, sub, t);
            if (bzla_bv_is_zero(tmp))
            {
              /* (s - t) / t is not truncated
               * (remainder is 0), therefore the EXclusive
               * upper bound
               * -> up = (s - t) / t - 1
               * ---------------------------------------------------------- */
              up = bzla_bv_sub(mm, tmp2, one);
              bzla_bv_free(mm, tmp2);
            }
            else
            {
              /* (s - t) / t is truncated
               * (remainder is not 0), therefore the INclusive
               * upper bound
               * -> up = (s - t) / t
               * ---------------------------------------------------------- */
              up = tmp2;
            }
            bzla_bv_free(mm, tmp);
          }

          if (bzla_bv_is_zero(up))
            res = bzla_bv_udiv(mm, sub, one);
          else
          {
            /* choose 1 <= n <= up randomly
             * s.t (s - t) % n = 0
             * ------------------------------------------------------------ */
            n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, up);
            tmp = bzla_bv_urem(mm, sub, n);
            for (cnt = 0; cnt < bw && !bzla_bv_is_zero(tmp); cnt++)
            {
              bzla_bv_free(mm, n);
              bzla_bv_free(mm, tmp);
              n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, up);
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
          bzla_bv_free(mm, up);
        }
        bzla_bv_free(mm, sub);
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] % s = t
   *
   * -> if s = 0, e[0] = t
   * -> if t = 1...1 and s != 0, conflict
   * -> if s <= t, conflict
   * -> if t > 0 and s = 1, conflict
   * -> else choose either
   *      - e[0] = t, or
   *      - e[0] = s * n + b, with n s.t. (s * n + b) does not overflow
   * ------------------------------------------------------------------------ */
  else
  {
    /* CONFLICT: t > 0 and s = 1 */
    assert(bzla_bv_is_zero(t) || !bzla_bv_is_one(s));

    if (bzla_bv_is_zero(s))
    {
      /* s = 0 -> e[0] = t -------------------------------------------------- */
      res = bzla_bv_copy(mm, t);
    }
    else if (!bzla_bv_compare(t, bvmax))
    {
      assert(bzla_bv_is_zero(s)); /* CONFLICT: s != 0 */
      /* t = 1...1 -> s = 0, e[0] = 1...1 ----------------------------------- */
      res = bzla_bv_copy(mm, t);
    }
    else
    {
      assert(bzla_bv_compare(s, t) > 0); /* CONFLICT: s <= t */

      if (bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
      BVUREM_EQ_0:
        /* choose simplest solution (0 <= res < s -> res = t)
         * with prob 0.5
         * ------------------------------------------------------------------ */
        res = bzla_bv_copy(mm, t);
      }
      else
      {
        /* e[0] = s * n + t,
         * with n s.t. (s * n + t) does not overflow
         * ------------------------------------------------------------------ */
        tmp2 = bzla_bv_sub(mm, bvmax, s);

        /* overflow for n = 1 -> only simplest solution possible */
        if (bzla_bv_compare(tmp2, t) < 0)
        {
          bzla_bv_free(mm, tmp2);
          goto BVUREM_EQ_0;
        }
        else
        {
          bzla_bv_free(mm, tmp2);

          tmp = bzla_bv_copy(mm, bvmax);
          n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);

          while (bzla_bv_is_umulo(mm, s, n))
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_sub(mm, n, one);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
          }

          mul  = bzla_bv_mul(mm, s, n);
          tmp2 = bzla_bv_sub(mm, bvmax, mul);

          if (bzla_bv_compare(tmp2, t) < 0)
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_sub(mm, n, one);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
            bzla_bv_free(mm, mul);
            mul = bzla_bv_mul(mm, s, n);
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
  bzla_bv_free(mm, bvmax);

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_urem, urem, s, t, res, eidx, "%");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_concat_bv(Bzla *bzla,
              BzlaNode *concat,
              BzlaBitVector *t,
              BzlaBitVector *s,
              int32_t eidx)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(t);
  assert(s);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(concat->e[eidx]));

  uint32_t bw_t, bw_s;
  BzlaNode *e;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_concat++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  e = concat->e[eidx ? 0 : 1];
  assert(e);
  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);

  /* check invertibility, if not invertible: CONFLICT */
  if (!bzla_is_inv_concat(mm, s, t, eidx))
  {
    return res_rec_conf(bzla, concat, e, t, s, eidx, cons_concat_bv, "o");
  }

  res = 0;

  /* ------------------------------------------------------------------------
   * s o e[1] = t
   *
   * -> slice e[1] out of the lower bits of t
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    tmp = bzla_bv_slice(mm, t, bw_t - 1, bw_t - bw_s);
    assert(!bzla_bv_compare(tmp, s)); /* CONFLICT: s bits do not match t */
    res = bzla_bv_slice(mm, t, bw_t - bw_s - 1, 0);
  }
  /* ------------------------------------------------------------------------
   * e[0] o s = t
   *
   * -> slice e[0] out of the upper bits of t
   * ------------------------------------------------------------------------ */
  else
  {
    tmp = bzla_bv_slice(mm, t, bw_s - 1, 0);
    assert(!bzla_bv_compare(tmp, s)); /* CONFLICT: s bits do not match t */
    res = bzla_bv_slice(mm, t, bw_t - 1, bw_s);
  }
  bzla_bv_free(mm, tmp);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_concat, concat, s, t, res, eidx, "o");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_slice_bv(Bzla *bzla,
             BzlaNode *slice,
             BzlaBitVector *t,
             BzlaBitVector *s,
             int32_t eidx)
{
  assert(bzla);
  assert(slice);
  assert(bzla_node_is_regular(slice));
  assert(t);
  assert(!bzla_node_is_bv_const(slice->e[0]));
  (void) eidx;

  uint32_t i, upper, lower, rlower, rupper, rboth, bw_x;
  BzlaNode *e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  bool bkeep, bflip;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_slice++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

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
#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_cond_bv(Bzla *bzla,
            BzlaNode *cond,
            BzlaBitVector *t,
            BzlaBitVector *s,
            int32_t eidx)
{
  assert(bzla);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(t);
  assert(!bzla_bv_compare(s, bzla_model_get_bv(bzla, cond->e[0])));
  assert(eidx || !bzla_node_is_bv_const(cond->e[eidx]));

  BzlaBitVector *res, *s1, *s2;
  BzlaMemMgr *mm = bzla->mm;

  s1 = (BzlaBitVector *) bzla_model_get_bv(bzla, cond->e[1]);
  s2 = (BzlaBitVector *) bzla_model_get_bv(bzla, cond->e[2]);
#ifndef NDEBUG
  char *str_t  = bzla_bv_to_char(bzla->mm, t);
  char *str_s0 = bzla_bv_to_char(mm, s);
  char *str_s1 = bzla_bv_to_char(mm, s1);
  char *str_s2 = bzla_bv_to_char(mm, s2);
#endif

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_cond++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  /* either assume that cond is fixed and propagate snew
   * to enabled path, or flip condition */

  if (eidx == 0)
  {
    /* flip condition */
    res = bzla_bv_not(mm, s);
  }
  else
  {
    /* else continue propagating current target value down */
    res = bzla_bv_copy(mm, t);
    if (bzla_node_is_bv_const(cond->e[eidx]))
    {
      bool is_recoverable = !bzla_bv_compare(t, eidx == 1 ? s2 : s1);
#ifndef NDEBUG
      if (eidx == 2)
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
          eidx,
          bzla_util_node2string(cond),
          str_t,
          eidx == 0 ? str_res : str_s0,
          eidx == 1 ? str_res : str_s1,
          eidx == 2 ? str_res : str_s2);
  bzla_mem_freestr(mm, str_t);
  bzla_mem_freestr(mm, str_res);
  bzla_mem_freestr(mm, str_s0);
  bzla_mem_freestr(mm, str_s1);
  bzla_mem_freestr(mm, str_s2);
#endif
  return res;
}

/* ========================================================================== */
/* Propagation move                                                           */
/* ========================================================================== */

static BzlaNode *
select_move(Bzla *bzla,
            BzlaNode *exp,
            BzlaBitVector *t,
            BzlaBitVector *s[3],
            int32_t eidx,
            BzlaBitVector *(*compute_value)(
                Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t),
            BzlaBitVector **value)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(t);
  assert(s);
  assert(eidx >= 0);
  assert(compute_value);
  assert(value);

  int32_t idx;

  /* special case slice: only one child
   * special case cond: we only need assignment of condition to compute value */
  idx =
      eidx ? 0 : (bzla_node_is_bv_slice(exp) || bzla_node_is_cond(exp) ? 0 : 1);
  *value = compute_value(bzla, exp, t, s[idx], eidx);
  return exp->e[eidx];
}

uint64_t
bzla_proputils_select_move_prop(Bzla *bzla,
                                BzlaNode *root,
                                BzlaBitVector *bvroot,
                                int32_t eidx,
                                BzlaNode **input,
                                BzlaBitVector **assignment)
{
  assert(bzla);
  assert(root);
  assert(bvroot);

  bool b;
  int32_t i, nconst;
  uint64_t nprops;
  BzlaNode *cur, *real_cur;
  BzlaBitVector *bve[3], *bvcur, *bvenew, *tmp;
  int32_t (*select_path)(Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector **);
  BzlaBitVector *(*compute_value)(
      Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t);
#ifndef NBZLALOG
  char *a;
  uint32_t nrecconf_prev, nnonrecconf_prev, nrecconf, nnonrecconf;
  uint32_t ncons = 0;
#endif

  *input      = 0;
  *assignment = 0;
  nprops      = 0;

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

  tmp = (BzlaBitVector *) bzla_model_get_bv(bzla, root);
  if (!bzla_bv_compare(bvroot, tmp))
  {
    if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      BZLA_PROP_SOLVER(bzla)->stats.fixed_conf++;
    goto DONE;
  }

  cur   = root;
  bvcur = bzla_bv_copy(bzla->mm, bvroot);

  for (;;)
  {
    real_cur = bzla_node_real_addr(cur);

    if (bzla_node_is_bv_var(cur))
    {
      *input      = real_cur;
      *assignment = bzla_node_is_inverted(cur) ? bzla_bv_not(bzla->mm, bvcur)
                                               : bzla_bv_copy(bzla->mm, bvcur);
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
        tmp   = bvcur;
        bvcur = bzla_bv_not(bzla->mm, tmp);
        bzla_bv_free(bzla->mm, tmp);
      }

      /* check if all paths are const, if yes -> conflict */
      for (i = 0, nconst = 0; i < real_cur->arity; i++)
      {
        bve[i] = (BzlaBitVector *) bzla_model_get_bv(bzla, real_cur->e[i]);
        if (bzla_node_is_bv_const(real_cur->e[i])) nconst += 1;
      }
      if (nconst > real_cur->arity - 1) break;

#ifndef NBZLALOG
      a = bzla_bv_to_char(bzla->mm, bvcur);
      BZLALOG(2, "");
      BZLALOG(2, "propagate: %s", a);
      bzla_mem_freestr(bzla->mm, a);
#endif

      /* we either select a consistent or inverse value
       * as path assignment, depending on the given probability p
       * -> if b then inverse else consistent */
      b = bzla_rng_pick_with_prob(
          &bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE));
#ifndef NBZLALOG
      if (!b) ncons += 1;
#endif

      /* select path and determine path assignment */
      switch (real_cur->kind)
      {
        case BZLA_BV_ADD_NODE:
          select_path   = select_path_add;
          compute_value = b ? inv_add_bv : cons_add_bv;
          break;
        case BZLA_BV_AND_NODE:
          select_path   = select_path_and;
          compute_value = b ? inv_and_bv : cons_and_bv;
          break;
        case BZLA_BV_EQ_NODE:
          select_path   = select_path_eq;
          compute_value = b ? inv_eq_bv : cons_eq_bv;
          break;
        case BZLA_BV_ULT_NODE:
          select_path   = select_path_ult;
          compute_value = b ? inv_ult_bv : cons_ult_bv;
          break;
        case BZLA_BV_SLL_NODE:
          select_path   = select_path_sll;
          compute_value = b ? inv_sll_bv : cons_sll_bv;
          break;
        case BZLA_BV_SRL_NODE:
          select_path   = select_path_srl;
          compute_value = b ? inv_srl_bv : cons_srl_bv;
          break;
        case BZLA_BV_MUL_NODE:
          select_path   = select_path_mul;
          compute_value = b ? inv_mul_bv : cons_mul_bv;
          break;
        case BZLA_BV_UDIV_NODE:
          select_path   = select_path_udiv;
          compute_value = b ? inv_udiv_bv : cons_udiv_bv;
          break;
        case BZLA_BV_UREM_NODE:
          select_path   = select_path_urem;
          compute_value = b ? inv_urem_bv : cons_urem_bv;
          break;
        case BZLA_BV_CONCAT_NODE:
          select_path   = select_path_concat;
          compute_value = b ? inv_concat_bv : cons_concat_bv;
          break;
        case BZLA_BV_SLICE_NODE:
          select_path   = select_path_slice;
          compute_value = b ? inv_slice_bv : cons_slice_bv;
          break;
        default:
          assert(bzla_node_is_bv_cond(real_cur));
          select_path   = select_path_cond;
          compute_value = b ? inv_cond_bv : cons_cond_bv;
      }

      if (eidx == -1) eidx = select_path(bzla, real_cur, bvcur, bve);

#ifndef NDEBUG
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        BzlaPropInfo prop = {real_cur, bzla_bv_copy(bzla->mm, bvcur), eidx};
        BZLA_PUSH_STACK(BZLA_PROP_SOLVER(bzla)->prop_path, prop);
      }
#endif
      cur =
          select_move(bzla, real_cur, bvcur, bve, eidx, compute_value, &bvenew);
      nprops += 1;

      if (!bvenew) break; /* non-recoverable conflict */

      bzla_bv_free(bzla->mm, bvcur);
      bvcur = bvenew;
      eidx  = -1;
    }
  }

  bzla_bv_free(bzla->mm, bvcur);

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
  int32_t cloned_eidx;
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
      cloned_eidx  = BZLA_PEEK_STACK(*stack, i).eidx;
      assert(cloned_eidx == 0 || cloned_eidx == 1);
      BzlaPropInfo cloned_prop = {cloned_exp, cloned_bvexp, cloned_eidx};
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
