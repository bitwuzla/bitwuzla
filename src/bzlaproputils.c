/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlaproputils.h"

#include "bzlainvutils.h"
#include "bzlanode.h"
#include "bzlaprintmodel.h"
#include "bzlaslsutils.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/* ========================================================================== */

typedef int32_t (*BzlaPropSelectPath)(Bzla *,
                                      BzlaNode *,
                                      BzlaBitVector *,
                                      BzlaBitVector **);

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
  int32_t idx_x;

  for (i = 0, idx_x = -1; i < exp->arity; i++)
    if (bzla_node_is_bv_const(exp->e[i]))
    {
      idx_x = i ? 0 : 1;
      break;
    }
  assert(exp->arity == 1 || !bzla_node_is_bv_const(exp->e[i ? 0 : 1]));
  return idx_x;
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

  int32_t idx_x;

  idx_x = select_path_non_const(add);
  if (idx_x == -1) idx_x = select_path_random(bzla, add);
  assert(idx_x >= 0);
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
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(and));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(and->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(and->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(ult));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(ult->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(ult->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(sll));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(sll->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(sll->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(srl));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(srl->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(srl->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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

      /* s[0] / s[1] = 1...1 -> choose e[1]
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        idx_x = 1;
      else
      {
        /* 1...1 / e[0] = 0 -> choose e[0] */
        if (bzla_bv_is_zero(t) && !bzla_bv_compare(s[0], ones)) idx_x = 0;
        /* s[0] < t -> choose e[0] */
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

        /* e[0] / 0 != 1...1 -> choose e[1] */
        if (bzla_bv_is_zero(s[1]) || bzla_bv_is_umulo(mm, s[1], t))
          idx_x = idx_x == -1 ? 1 : -1;
      }
      bzla_bv_free(mm, ones);
    }
    if (idx_x == -1) idx_x = select_path_random(bzla, udiv);
  }

  assert(idx_x >= 0);
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
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(urem));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(urem->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(urem->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(concat));
  a = bzla_bv_to_char(mm, s[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(concat->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, s[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(concat->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
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
  int32_t idx_x;
  uint32_t prob;
  BzlaBitVector *s0;

  (void) bvcond;

  s0 = *s;
  assert(s0);

  if (bzla_node_is_bv_const(cond->e[0]))
    idx_x = cond->e[0] == bzla->true_exp ? 1 : 2;
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
      idx_x = 0;

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
      idx_x = 0;
    }
    /* assume cond to be fixed and select enabled branch */
    else
    {
      idx_x = bzla_bv_is_true(s0) ? 1 : 2;
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
  BZLALOG(2, "    * chose: %d", idx_x);
#endif
  return idx_x;
}

/* ========================================================================== */
/* Consistent value computation                                               */
/* ========================================================================== */

BzlaBitVector *
bzla_proputils_cons_add(Bzla *bzla,
                        BzlaNode *add,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(add->e[idx_x]));

  (void) add;
  (void) s;
  (void) idx_x;
  (void) domains;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_add++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  return bzla_bv_new_random(bzla->mm, &bzla->rng, bzla_bv_get_width(t));
}

BzlaBitVector *
bzla_proputils_cons_and(Bzla *bzla,
                        BzlaNode *and,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(and->e[idx_x]));

  uint32_t i, bw;
  BzlaBitVector *res;
  BzlaUIntStack dcbits;
  bool b;

  (void) s;
  (void) domains;

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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(eq->e[idx_x]));

  (void) t;
  (void) domains;

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

BzlaBitVector *
bzla_proputils_cons_ult(Bzla *bzla,
                        BzlaNode *ult,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(ult->e[idx_x]));

  bool isult;
  uint32_t bw;
  BzlaBitVector *ones, *zero, *tmp, *res;
  BzlaMemMgr *mm;

  (void) ult;
  (void) domains;

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
  ones  = bzla_bv_ones(mm, bw);

  if (idx_x && isult)
  {
    /* s < res = 1  ->  res > 0 */
    tmp = bzla_bv_one(mm, bw);
    res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
    bzla_bv_free(mm, tmp);
  }
  else if (!idx_x && isult)
  {
    /* res < s = 1  ->  0 <= res < 1...1 */
    tmp = bzla_bv_dec(mm, ones);
    res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
    bzla_bv_free(mm, tmp);
  }
  else
  {
    res = bzla_bv_new_random(mm, &bzla->rng, bw);
  }

  bzla_bv_free(mm, ones);
  bzla_bv_free(mm, zero);

  return res;
}

BzlaBitVector *
bzla_proputils_cons_sll(Bzla *bzla,
                        BzlaNode *sll,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(t);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(sll->e[idx_x]));

  uint32_t i, bw, ctz_bvsll, shift;
  BzlaBitVector *res, *bv_shift;
  BzlaMemMgr *mm;

  (void) sll;
  (void) s;
  (void) domains;

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

  if (idx_x)
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

BzlaBitVector *
bzla_proputils_cons_srl(Bzla *bzla,
                        BzlaNode *srl,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(t);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(srl->e[idx_x]));

  uint32_t i, shift, bw;
  BzlaBitVector *res, *bv_shift;
  BzlaMemMgr *mm;

  (void) srl;
  (void) s;
  (void) domains;

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

  if (idx_x)
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

BzlaBitVector *
bzla_proputils_cons_mul(Bzla *bzla,
                        BzlaNode *mul,
                        BzlaBitVector *t,
                        BzlaBitVector *s,
                        int32_t idx_x,
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(mul->e[idx_x]));

  uint32_t r, bw, ctz_res, ctz_bvmul;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  (void) mul;
  (void) s;
  (void) idx_x;
  (void) domains;

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

BzlaBitVector *
bzla_proputils_cons_udiv(Bzla *bzla,
                         BzlaNode *udiv,
                         BzlaBitVector *t,
                         BzlaBitVector *s,
                         int32_t idx_x,
                         BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(udiv->e[idx_x]));

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

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_udiv++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

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
                         BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(urem->e[idx_x]));

  uint32_t bw;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;

  (void) urem;
  (void) s;
  (void) domains;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_urem++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
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
                           BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(t);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(concat->e[idx_x]));

  int32_t idx_s, bw_t, bw_s;
  uint32_t r;
  BzlaBitVector *res;
  const BzlaBitVector *bvcur;

  (void) domains;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_concat++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

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
                          BzlaIntHashTable *domains)
{
  return bzla_proputils_inv_slice(bzla, slice, t, s, idx_x, domains);
}

BzlaBitVector *
bzla_proputils_cons_cond(Bzla *bzla,
                         BzlaNode *cond,
                         BzlaBitVector *bvcond,
                         BzlaBitVector *s,
                         int32_t idx_x,
                         BzlaIntHashTable *domains)
{
  return bzla_proputils_inv_cond(bzla, cond, bvcond, s, idx_x, domains);
}

/* ========================================================================== */
/* Inverse value computation                                                  */
/* ========================================================================== */

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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(t);
  assert(s);
  assert(domains);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(add->e[idx_x]));
#ifndef NDEBUG
  assert(bzla_is_inv_add(bzla->mm, 0, t, s, idx_x));
  if (domains)
  {
    BzlaHashTableData *x =
        bzla_hashint_map_get(domains, bzla_node_real_addr(add->e[idx_x])->id);
    assert(!x || bzla_is_inv_add_const(bzla->mm, x->as_ptr, t, s, idx_x));
  }
#endif

  BzlaBitVector *res;

  (void) add;
  (void) idx_x;
  (void) domains;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_add++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(and);
  assert(t);
  assert(s);
  assert(domains);
  assert(bzla_node_is_regular(and));
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(and->e[idx_x]));
#ifndef NDEBUG
  assert(bzla_is_inv_and(bzla->mm, 0, t, s, idx_x));
  BzlaHashTableData *x =
      bzla_hashint_map_get(domains, bzla_node_real_addr(and->e[idx_x])->id);
  assert(!x || bzla_is_inv_and_const(bzla->mm, x->as_ptr, t, s, idx_x));
#endif

  uint32_t i, bw;
  int32_t bit_and, bit_e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  BzlaUIntStack dcbits;
  bool b;

  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_and++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

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
                      BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(eq->e[idx_x]));
#ifndef NDEBUG
  assert(bzla_is_inv_eq(bzla->mm, 0, t, s, idx_x));
  BzlaHashTableData *x =
      bzla_hashint_map_get(domains, bzla_node_real_addr(eq->e[idx_x])->id);
  assert(!x || bzla_is_inv_eq_const(bzla->mm, x->as_ptr, t, s, idx_x));
#endif

  BzlaBitVector *res;
  BzlaMemMgr *mm;

  (void) domains;

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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(t);
  assert(bzla_bv_get_width(t) == 1);
  assert(s);
  assert(domains);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(ult->e[idx_x]));
#ifndef NDEBUG
  assert(bzla_is_inv_ult(bzla->mm, 0, t, s, idx_x));
  BzlaHashTableData *x =
      bzla_hashint_map_get(domains, bzla_node_real_addr(ult->e[idx_x])->id);
  assert(!x || bzla_is_inv_ult_const(bzla->mm, x->as_ptr, t, s, idx_x));
#endif

  bool isult;
  uint32_t bw;
  BzlaBitVector *res, *zero, *one, *ones, *tmp;
  BzlaMemMgr *mm;

  (void) ult;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_ult++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  bw    = bzla_bv_get_width(s);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  ones  = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(t);

  res = 0;

  if (idx_x)
  {
    assert(!isult || bzla_bv_compare(s, ones)); /* CONFLICT: 1...1 < e[1] */
    if (!isult)
    {
      /* s >= e[1] */
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, s);
    }
    else
    {
      /* s < e[1] */
      tmp = bzla_bv_add(mm, s, one);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, ones);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    assert(!isult || !bzla_bv_is_zero(s)); /* CONFLICT: e[0] < 0  */
    if (!isult)
    {
      /* e[0] >= s */
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, s, ones);
    }
    else
    {
      /* e[0] < s */
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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(t);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(sll->e[idx_x]));
#ifndef NDEBUG
  assert(bzla_is_inv_sll(bzla->mm, 0, t, s, idx_x));
  BzlaHashTableData *x =
      bzla_hashint_map_get(domains, bzla_node_real_addr(sll->e[idx_x])->id);
  assert(!x || bzla_is_inv_sll_const(bzla->mm, x->as_ptr, t, s, idx_x));
#endif

  uint32_t bw, i, ctz_s, ctz_t, shift;
  BzlaBitVector *res, *tmp, *ones;
  BzlaMemMgr *mm;

  (void) sll;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_sll++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
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
  if (idx_x)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 << e[1] = 0...0 -> choose res randomly */
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
         * x...x0 << e[1] = 0...0
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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(t);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(!bzla_node_is_bv_const(srl->e[idx_x]));
  assert(bzla_is_inv_srl(bzla->mm, 0, t, s, idx_x));

  uint32_t bw, i, clz_s, clz_t, shift;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;

  (void) srl;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_srl++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
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
  if (idx_x)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 >> e[1] = 0...0 -> choose random res */
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
         * x...x0 >> e[1] = 0...0
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
                       BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(mul->e[idx_x]));
  assert(bzla_is_inv_mul(bzla->mm, 0, t, s, idx_x));

  int32_t lsb_s, ispow2_s;
  uint32_t i, j, bw;
  BzlaBitVector *res, *inv, *tmp, *tmp2;
  BzlaMemMgr *mm;

  (void) mul;
  (void) idx_x;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_mul++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

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
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(udiv->e[idx_x]));
  assert(bzla_is_inv_udiv(bzla->mm, 0, t, s, idx_x));

  uint32_t bw;
  BzlaBitVector *res, *lo, *up, *one, *ones, *tmp;
  BzlaMemMgr *mm;
  BzlaRNG *rng;

  (void) udiv;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_udiv++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  rng = &bzla->rng;
  bw  = bzla_bv_get_width(s);

  one  = bzla_bv_one(mm, bw);
  ones = bzla_bv_ones(mm, bw); /* 2^bw - 1 */

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
  if (idx_x)
  {
    if (!bzla_bv_compare(t, ones))
    {
      if (!bzla_bv_compare(s, t) && bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
        /**
         * s = t = 2^bw - 1 -> choose either e[1] = 0 or e[1] = 1
         * with prob 0.5
         */
        res = bzla_bv_one(mm, bw);
      }
      else
      {
        /* t = 2^bw - 1 and s != t -> e[1] = 0 */
        res = bzla_bv_new(mm, bw);
      }
    }
    else if (bzla_bv_is_zero(t))
    {
      if (bzla_bv_is_zero(s))
      {
        /* t = 0 and s = 0 -> choose random e[1] > 0 */
        res = bzla_bv_new_random_range(mm, rng, bw, one, ones);
      }
      else
      {
        assert(bzla_bv_compare(s, ones)); /* CONFLICT: s = ~0  and t = 0 */

        /* t = 0 and 0 < s < 2^bw - 1 -> choose random e[1] > s */
        tmp = bzla_bv_inc(mm, s);
        res = bzla_bv_new_random_range(mm, rng, bw, tmp, ones);
        bzla_bv_free(mm, tmp);
      }
    }
    else
    {
      assert(bzla_bv_compare(s, t) >= 0); /* CONFLICT: s < t */

      /**
       * if t is a divisor of s, choose e[1] = s / t
       * with prob = 0.5 and a s s.t. s / e[1] = t otherwise
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
         * choose e[1] out of all options that yield s / e[1] = t
         * Note: udiv always truncates the results towards 0.
         */

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

        /* choose lo <= e[1] <= up */
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
   *      + choose e[0] s.t. e[0] / s = t
   * -> else choose e[0] s.t. e[0] / s = t
   * ------------------------------------------------------------------------ */
  else
  {
    if (!bzla_bv_compare(t, ones))
    {
      if (!bzla_bv_compare(s, one))
      {
        /* t = 2^bw-1 and s = 1 -> e[0] = 2^bw-1 */
        res = bzla_bv_copy(mm, ones);
      }
      else
      {
        assert(bzla_bv_is_zero(s)); /* CONFLICT: t = ~0 and s != 0 */
        /* t = 2^bw - 1 and s = 0 -> choose random e[0] */
        res = bzla_bv_new_random(mm, rng, bw);
      }
    }
    else
    {
      /* if s * t does not overflow, choose e[0] = s * t
       * with prob = 0.5 and a s s.t. e[0] / s = t otherwise
       * -------------------------------------------------------------------- */

      assert(!bzla_bv_is_umulo(mm, s, t)); /* CONFLICT: overflow: s * t */
      if (bzla_rng_pick_with_prob(rng, 500))
        res = bzla_bv_mul(mm, s, t);
      else
      {
        /**
         * choose e[0] out of all options that yield
         * e[0] / s = t
         * Note: udiv always truncates the results towards 0.
         */

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
                        BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(t);
  assert(s);
  assert(bzla_bv_get_width(s) == bzla_bv_get_width(t));
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(urem->e[idx_x]));
  assert(bzla_is_inv_urem(bzla->mm, 0, t, s, idx_x));

  uint32_t bw, cnt;
  int32_t cmp;
  BzlaBitVector *res, *ones, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BzlaMemMgr *mm;

  (void) urem;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_urem++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  bw = bzla_bv_get_width(t);

  ones = bzla_bv_ones(mm, bw); /* 2^bw - 1 */
  one  = bzla_bv_one(mm, bw);

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
  if (idx_x)
  {
    if (!bzla_bv_compare(t, ones))
    {
      /* CONFLICT: t = ~0 but s != ~0 */
      assert(!bzla_bv_compare(s, ones));

      /* s % e[1] = ~0 -> s = ~0, e[1] = 0 */
      res = bzla_bv_new(mm, bw);
    }
    else
    {
      cmp = bzla_bv_compare(s, t);

      if (cmp == 0)
      {
        /* s = t, choose either e[1] = 0 or random e[1] > t
         * ------------------------------------------------------------------ */

        if (bzla_rng_pick_with_prob(&bzla->rng, 250))
        {
          /* choose e[1] = 0 with prob = 0.25 */
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
        /* s > t, e[1] = (s - t) / n
         * ------------------------------------------------------------------ */

        assert(cmp > 0); /* CONFLICT: s < t */
#ifndef NDEBUG
        if (!bzla_bv_is_zero(t))
        {
          tmp = bzla_bv_dec(mm, s);
          /* CONFLICT: t = s - 1 -> s % e[1] = s - 1 -> not possible if t > 0 */
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
            up = bzla_bv_copy(mm, s);
          }
          else
          {
            /**
             * e[1] > t
             * -> (s - t) / n > t
             * -> (s - t) / t > n
             */
            tmp  = bzla_bv_urem(mm, sub, t);
            tmp2 = bzla_bv_udiv(mm, sub, t);
            if (bzla_bv_is_zero(tmp))
            {
              /**
               * (s - t) / t is not truncated
               * (remainder is 0), therefore the EXclusive
               * upper bound
               * -> up = (s - t) / t - 1
               */
              up = bzla_bv_sub(mm, tmp2, one);
              bzla_bv_free(mm, tmp2);
            }
            else
            {
              /**
               * (s - t) / t is truncated
               * (remainder is not 0), therefore the INclusive
               * upper bound
               * -> up = (s - t) / t
               */
              up = tmp2;
            }
            bzla_bv_free(mm, tmp);
          }

          if (bzla_bv_is_zero(up))
          {
            res = bzla_bv_udiv(mm, sub, one);
          }
          else
          {
            /**
             * choose 1 <= n <= up randomly
             * s.t (s - t) % n = 0
             */
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
      /* s = 0 -> e[0] = t */
      res = bzla_bv_copy(mm, t);
    }
    else if (!bzla_bv_compare(t, ones))
    {
      assert(bzla_bv_is_zero(s)); /* CONFLICT: s != 0 */
      /* t = ~0 -> s = 0, e[0] = ~0 */
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
         * e[0] = s * n + t,
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
                          BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(t);
  assert(s);
  assert(idx_x >= 0 && idx_x <= 1);
  assert(!bzla_node_is_bv_const(concat->e[idx_x]));
#ifndef NDEBUG
  assert(bzla_is_inv_concat(bzla->mm, 0, t, s, idx_x));
  BzlaHashTableData *x =
      bzla_hashint_map_get(domains, bzla_node_real_addr(concat->e[idx_x])->id);
  assert(!x || bzla_is_inv_concat_const(bzla->mm, x->as_ptr, t, s, idx_x));
#endif

  uint32_t bw_t, bw_s;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  (void) concat;
  (void) domains;

  mm = bzla->mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_concat++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  bw_t = bzla_bv_get_width(t);
  bw_s = bzla_bv_get_width(s);
  res  = 0;

  /* ------------------------------------------------------------------------
   * s o e[1] = t
   *
   * -> slice e[1] out of the lower bits of t
   * ------------------------------------------------------------------------ */
  if (idx_x)
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
                         BzlaIntHashTable *domains)
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

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_slice++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

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
                        BzlaIntHashTable *domains)
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
/* Inverse value computation with propagator domains                          */
/* ========================================================================== */

#if 0
static BzlaBitVector *
set_const_bits (BzlaMemMgr *mm, BzlaBvDomain *d_res_x, BzlaBitVector *res_x)
{
  assert (d_res_x);
  assert (res_x);
  BzlaBitVector *tmp = bzla_bv_and (mm, d_res_x->hi, res_x);
  BzlaBitVector *res = bzla_bv_or (mm, d_res_x->lo, tmp);
  bzla_bv_free (mm, tmp);
  return res;
}
#endif

/* -------------------------------------------------------------------------- */
/* INV: add                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_add_bvprop(Bzla *bzla,
                              BzlaNode *add,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(add);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (add));
  assert (bzla_hashint_map_contains (domains, add->id));
  assert (bzla_bv_get_width (s) == bzla_bv_get_width (t));
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (add->e[idx_x]));

  BzlaNode *x;
  BzlaBitVector *res;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  x  = bzla_node_real_addr (add->e[idx_x]);

  d_s = bzla_bvprop_new_fixed (mm, s);
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bzla_bv_get_width (s));
  assert (bzla_bv_get_width (d_x->hi) == bzla_bv_get_width (s));

  is_valid = bzla_bvprop_add (mm, d_x, d_s, d_t, &d_res_x, &d_res_s, &d_res_t);

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_add++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_add_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_add--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_add (bzla, add, t, s, idx_x, domains);
  }

  assert (bzla_bvprop_is_fixed (mm, d_res_x));
  res = bzla_bv_copy (mm, d_res_x->lo);
#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_add, add, s, t, res, idx_x, "&");
#endif
  bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_and_bvprop(Bzla *bzla,
                              BzlaNode *and,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(and);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (and));
  assert (bzla_hashint_map_contains (domains, and->id));
  assert (bzla_bv_get_width (s) == bzla_bv_get_width (t));
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (and->e[idx_x]));

  uint32_t bw;
  BzlaNode *x;
  BzlaBitVector *res, *tmp;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid;
  BzlaMemMgr *mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_and++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  x  = bzla_node_real_addr (and->e[idx_x]);
  bw = bzla_bv_get_width (s);
  assert (bw == bzla_node_bv_get_width (bzla, x));

  d_s = bzla_bvprop_new_fixed (mm, s);
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw);
  assert (bzla_bv_get_width (d_x->hi) == bw);

  is_valid = bzla_bvprop_and (mm, d_x, d_s, d_t, &d_res_x, &d_res_s, &d_res_t);

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_and_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_and--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_and (bzla, and, t, s, idx_x, domains);
  }

  tmp = bzla_bv_new_random (mm, &bzla->rng, bw);
  res = set_const_bits (mm, d_res_x, tmp);
  bzla_bv_free (mm, tmp);
#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_and, and, s, t, res, idx_x, "+");
#endif
  bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_eq_bvprop(Bzla *bzla,
                             BzlaNode *eq,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             int32_t idx_x,
                             BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(eq);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (eq));
  assert (bzla_hashint_map_contains (domains, eq->id));
  assert (bzla_bv_get_width (t) == 1);
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (eq->e[idx_x]));

  uint32_t bw_x;
  BzlaNode *x;
  BzlaBitVector *res, *tmp;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid, is_diseq;
  BzlaMemMgr *mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_eq++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm   = bzla->mm;
  x    = bzla_node_real_addr (eq->e[idx_x]);
  bw_x = bzla_bv_get_width (s);
  assert (bw_x == bzla_node_bv_get_width (bzla, x));

  d_s = bzla_bvprop_new_fixed (mm, s);
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw_x);
  assert (bzla_bv_get_width (d_x->hi) == bw_x);

  is_valid = bzla_bvprop_eq (mm, d_x, d_s, d_t, &d_res_x, &d_res_s, &d_res_t);

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_eq_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_eq--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_eq (bzla, eq, t, s, idx_x, domains);
  }

  if ((is_diseq = bzla_bv_is_zero (t)))
  {
    assert (bzla_bv_compare (d_res_x->lo, s)
            || bzla_bv_compare (d_res_x->hi, s));
    res = 0;
    do
    {
      if (res) bzla_bv_free (mm, res);
      tmp = bzla_bv_new_random (mm, &bzla->rng, bw_x);
      res = set_const_bits (mm, d_res_x, tmp);
      bzla_bv_free (mm, tmp);
    } while (is_diseq && !bzla_bv_compare (res, s));
  }
  else
  {
    assert (bzla_bvprop_is_fixed (mm, d_res_x));
    assert (!bzla_bv_compare (d_res_x->lo, s));
    res = bzla_bv_copy (mm, d_res_x->lo);
  }

#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_eq, eq, s, t, res, idx_x, "=");
#endif
  bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */

bool
bzla_proputils_inv_interval_ult(BzlaMemMgr *mm,
                                BzlaBitVector *t,
                                BzlaBitVector *s,
                                int32_t idx_x,
                                BzlaBvDomain *d_x,
                                BzlaBitVector **min,
                                BzlaBitVector **max)
{
  assert(mm);
  assert(t);
  assert(s);
  assert(d_x);
  assert(min);
  assert(max);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains, will probably not need it in the future
#if 0

  uint32_t bw;

  bw = bzla_bv_get_width (s);

  if (bzla_bv_is_one (t))
  {
    if (idx_x)
    {
      /**
       * s < x
       *
       * min: lo_x if lo_x > s else s + 1
       * max: ~0
       *
       * conflict: hi_x <= s
       */
      assert (!bzla_bv_is_ones (s));
      if (bzla_bv_compare (d_x->hi, s) <= 0) return false;
      *max = bzla_bv_ones (mm, bw);
      *min = bzla_bv_compare (d_x->lo, s) > 0 ? bzla_bv_copy (mm, d_x->lo)
                                              : bzla_bv_inc (mm, s);
    }
    else
    {
      /**
       * x < s
       *
       * min: 0
       * max: hi_x if hi_x < s else s - 1
       *
       * conflict: lo_x >= s
       */
      assert (!bzla_bv_is_zero (s));
      if (bzla_bv_compare (d_x->lo, s) >= 0) return false;
      *min = bzla_bv_zero (mm, bw);
      *max = bzla_bv_compare (d_x->hi, s) < 0 ? bzla_bv_copy (mm, d_x->hi)
                                              : bzla_bv_dec (mm, s);
    }
  }
  else
  {
    if (idx_x)
    {
      /* s >= x
       *
       * min: 0
       * max: hi_x if hi_x <= s else s
       *
       * conflict: lo_x > s
       */
      if (bzla_bv_compare (d_x->lo, s) > 0) return false;
      *min = bzla_bv_zero (mm, bw);
      *max = bzla_bv_compare (d_x->hi, s) <= 0 ? bzla_bv_copy (mm, d_x->hi)
                                               : bzla_bv_copy (mm, s);
    }
    else
    {
      /* x >= s
       *
       * min: lo_x if lo_x >= s else s
       * max: ~0
       *
       * conflict: hi_x < s
       */
      if (bzla_bv_compare (d_x->hi, s) < 0) return false;
      *min = bzla_bv_compare (d_x->lo, s) >= 0 ? bzla_bv_copy (mm, d_x->lo)
                                               : bzla_bv_copy (mm, s);
      *max = bzla_bv_ones (mm, bw);
    }
  }
  return true;
#else
  (void) idx_x;
  return 0;
#endif
}

BzlaBitVector *
bzla_proputils_inv_ult_bvprop(Bzla *bzla,
                              BzlaNode *ult,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(ult);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (ult));
  assert (bzla_hashint_map_contains (domains, ult->id));
  assert (bzla_bv_get_width (t) == 1);
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (ult->e[idx_x]));

  uint32_t bw_x;
  BzlaNode *x;
  BzlaBitVector *res;
  BzlaBitVector *min, *max;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid_domain, is_valid_range;
  BzlaMemMgr *mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_ult++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm   = bzla->mm;
  x    = bzla_node_real_addr (ult->e[idx_x]);
  bw_x = bzla_bv_get_width (s);
  assert (bw_x == bzla_node_bv_get_width (bzla, x));

  d_s = bzla_bvprop_new_fixed (mm, s);
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw_x);
  assert (bzla_bv_get_width (d_x->hi) == bw_x);

  /* propagate target value with respect to constant bits */
  is_valid_domain =
      idx_x ? bzla_bvprop_ult (mm, d_s, d_x, d_t, &d_res_s, &d_res_x, &d_res_t)
            : bzla_bvprop_ult (mm, d_x, d_s, d_t, &d_res_x, &d_res_s, &d_res_t);

  /* determine value range for result ([min, max])*/
  is_valid_range =
      bzla_proputils_inv_interval_ult (mm, t, s, idx_x, d_res_x, &min, &max);

  if (!is_valid_domain || !is_valid_range)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_ult_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_ult--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    res = bzla_proputils_inv_ult (bzla, ult, t, s, idx_x, domains);
    goto DONE;
  }

  res = bzla_bv_new_random_range (mm, &bzla->rng, bw_x, min, max);
  assert (bzla_bvprop_is_consistent (d_res_x, res));
  bzla_bv_free (mm, min);
  bzla_bv_free (mm, max);

#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_ult, ult, s, t, res, idx_x, "<");
#endif
DONE:
  bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: sll                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sll_bvprop(Bzla *bzla,
                              BzlaNode *sll,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(sll);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (sll));
  assert (bzla_hashint_map_contains (domains, sll->id));
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (sll->e[idx_x]));

  uint32_t bw_x;
  uint32_t ctz_s, ctz_t, shift;
  BzlaNode *x;
  BzlaBitVector *res, *res_tmp, *tmp, *ones;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid, done;
  BzlaMemMgr *mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_sll++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  x  = bzla_node_real_addr (sll->e[idx_x]);
  bw_x = bzla_node_bv_get_width (bzla, x);

  d_s = idx_x ? bzla_bvprop_new_fixed (mm, s) : 0;
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw_x);
  assert (bzla_bv_get_width (d_x->hi) == bw_x);
  d_res_s = 0;

  is_valid =
      idx_x ? bzla_bvprop_sll (mm, d_s, d_x, d_t, &d_res_s, &d_res_x, &d_res_t)
            : bzla_bvprop_sll_const (mm, d_x, d_t, s, &d_res_x, &d_res_t);

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_sll_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_sll--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_sll (bzla, sll, t, s, idx_x, domains);
  }

  if (idx_x)
  {
    /* s << x = t
     * -> identify possible shift value via zero LSB in t
     *    (considering zero LSB in s) */
    res = 0;
    do
    {
      if (res) bzla_bv_free (mm, res);

      if (bzla_bv_is_zero (s) && bzla_bv_is_zero (t))
      {
        /* 0...0 << e[1] = 0...0 -> choose res randomly */
        res_tmp = bzla_bv_new_random (mm, &bzla->rng, bw_x);
      }
      else
      {
        /**
         * -> ctz(s) > ctz (t) -> conflict
         * -> shift = ctz(t) - ctz(s)
         *      -> if t = 0 choose shift <= res < bw_x
         *      -> else res = shift
         *           + if all remaining shifted bits match
         *           + and if res < bw_x
         * -> else conflict
         */
        ctz_s = bzla_bv_get_num_trailing_zeros (s);
        ctz_t = bzla_bv_get_num_trailing_zeros (t);
        assert (ctz_s <= ctz_t); /* CONFLICT: ctz_s > ctz_t */
        shift = ctz_t - ctz_s;
        if (bzla_bv_is_zero (t))
        {
          /**
           * x...x0 << e[1] = 0...0
           * -> choose random shift <= res < bw_x
           */
          ones    = bzla_bv_ones (mm, bw_x);
          tmp     = bzla_bv_uint64_to_bv (mm, (uint64_t) shift, bw_x);
          res_tmp = bzla_bv_new_random_range (mm, &bzla->rng, bw_x, tmp, ones);
          bzla_bv_free (mm, ones);
          bzla_bv_free (mm, tmp);
        }
        else
        {
#ifndef NDEBUG
          uint32_t i, j;
          for (i = 0, j = shift, res = 0; i < bzla_bv_get_width (s) - j; i++)
          {
            /* CONFLICT: shifted bits must match */
            assert (bzla_bv_get_bit (s, i) == bzla_bv_get_bit (t, j + i));
          }
#endif
          res_tmp = bzla_bv_uint64_to_bv (mm, (uint64_t) shift, bw_x);
        }
      }
      res = set_const_bits (mm, d_res_x, res_tmp);
      bzla_bv_free (mm, res_tmp);
      tmp  = bzla_bv_sll (mm, s, res);
      done = bzla_bv_compare (tmp, t) == 0;
      bzla_bv_free (mm, tmp);
    } while (!done);
  }
  else
  {
    /* x << s = t
     * -> x = t >> s
     *    set irrelevant MSBs (the ones that get shifted out) randomly */
    res = 0;
    do
    {
      if (res) bzla_bv_free (mm, res);

      tmp = bzla_bv_new_random (mm, &bzla->rng, bw_x);
      res = set_const_bits (mm, d_res_x, tmp);
      bzla_bv_free (mm, tmp);
      tmp  = bzla_bv_sll (mm, res, s);
      done = bzla_bv_compare (tmp, t) == 0;
      bzla_bv_free (mm, tmp);
    } while (!done);
  }

#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_sll, sll, s, t, res, idx_x, "<<");
#endif
  if (d_s) bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  if (d_res_s) bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_srl_bvprop(Bzla *bzla,
                              BzlaNode *srl,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(srl);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (srl));
  assert (bzla_hashint_map_contains (domains, srl->id));
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (srl->e[idx_x]));

  uint32_t bw_x;
  uint32_t clz_s, clz_t, shift;
  BzlaNode *x;
  BzlaBitVector *res, *res_tmp, *tmp, *ones;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid, done;
  BzlaMemMgr *mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_srl++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm   = bzla->mm;
  x    = bzla_node_real_addr (srl->e[idx_x]);
  bw_x = bzla_node_bv_get_width (bzla, x);
  assert (bzla_bv_get_width (s) == bw_x);
  assert (bzla_bv_get_width (t) == bw_x);

  d_s = idx_x ? bzla_bvprop_new_fixed (mm, s) : 0;
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw_x);
  assert (bzla_bv_get_width (d_x->hi) == bw_x);
  d_res_s = 0;

  is_valid =
      idx_x ? bzla_bvprop_srl (mm, d_s, d_x, d_t, &d_res_s, &d_res_x, &d_res_t)
            : bzla_bvprop_srl_const (mm, d_x, d_t, s, &d_res_x, &d_res_t);

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_srl_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_srl--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_srl (bzla, srl, t, s, idx_x, domains);
  }

  if (idx_x)
  {
    /* s >> x = t
     *
     * -> identify possible shift value via zero MSBs in t
     *    (considering zero MSBs in s) */

    res = 0;
    do
    {
      if (res) bzla_bv_free (mm, res);

      if (bzla_bv_is_zero (s) && bzla_bv_is_zero (t))
      {
        /* 0...0 >> e[1] = 0...0 -> choose random res */
        res_tmp = bzla_bv_new_random (mm, &bzla->rng, bw_x);
      }
      else
      {
        /**
         * clz(s) > clz(t) -> conflict
         *
         * -> shift = clz(t) - clz(s)
         *      -> if t = 0 choose shift <= res < bw_x
         *      -> else res = shift
         *           + if all remaining shifted bits match
         *           + and if res < bw_x
         * -> else conflict
         */
        clz_s = bzla_bv_get_num_leading_zeros (s);
        clz_t = bzla_bv_get_num_leading_zeros (t);
        assert (clz_s <= clz_t);
        shift = clz_t - clz_s;
        if (bzla_bv_is_zero (t))
        {
          /**
           * x...x0 >> e[1] = 0...0
           * -> choose random shift <= res < bw_x
           */
          ones    = bzla_bv_ones (mm, bw_x);
          tmp     = bzla_bv_uint64_to_bv (mm, (uint64_t) shift, bw_x);
          res_tmp = bzla_bv_new_random_range (mm, &bzla->rng, bw_x, tmp, ones);
          bzla_bv_free (mm, ones);
          bzla_bv_free (mm, tmp);
        }
        else
        {
#ifndef NDEBUG
          uint32_t i, j;
          for (i = 0, j = shift, res = 0; i < bw_x - j; i++)
          {
            /* CONFLICT: shifted bits must match */
            assert (bzla_bv_get_bit (s, bw_x - 1 - i)
                    == bzla_bv_get_bit (t, bw_x - 1 - (j + i)));
          }
#endif
          res_tmp = bzla_bv_uint64_to_bv (mm, (uint64_t) shift, bw_x);
        }
      }

      res = set_const_bits (mm, d_res_x, res_tmp);
      bzla_bv_free (mm, res_tmp);
      tmp  = bzla_bv_srl (mm, s, res);
      done = bzla_bv_compare (tmp, t) == 0;
      bzla_bv_free (mm, tmp);
    } while (!done);
  }
  else
  {
    /* x >> s = t
     * -> x = t >> s
     *    set irrelevant LSBs (the ones that get shifted out) randomly */
    res = 0;
    do
    {
      if (res) bzla_bv_free (mm, res);

      tmp = bzla_bv_new_random (mm, &bzla->rng, bw_x);
      res = set_const_bits (mm, d_res_x, tmp);
      bzla_bv_free (mm, tmp);
      tmp  = bzla_bv_srl (mm, res, s);
      done = bzla_bv_compare (tmp, t) == 0;
      bzla_bv_free (mm, tmp);
    } while (!done);
  }

#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_srl, srl, s, t, res, idx_x, ">>");
#endif
  if (d_s) bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  if (d_res_s) bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_mul_bvprop(Bzla *bzla,
                              BzlaNode *mul,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              int32_t idx_x,
                              BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(mul);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (mul));
  assert (bzla_hashint_map_contains (domains, mul->id));
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (mul->e[idx_x]));

  uint32_t bw_x;
  BzlaNode *x;
  BzlaBitVector *res, *tmp;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid;
  BzlaMemMgr *mm;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_mul++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm   = bzla->mm;
  x    = bzla_node_real_addr (mul->e[idx_x]);
  bw_x = bzla_bv_get_width (s);
  assert (bw_x == bzla_node_bv_get_width (bzla, x));

  d_s = bzla_bvprop_new_fixed (mm, s);
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw_x);
  assert (bzla_bv_get_width (d_x->hi) == bw_x);
  assert (bzla_bv_get_width (s) == bw_x);
  assert (bzla_bv_get_width (t) == bw_x);

  is_valid = bzla_bvprop_mul (mm, d_x, d_s, d_t, &d_res_x, &d_res_s, &d_res_t);

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_mul_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_mul--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_mul (bzla, mul, t, s, idx_x, domains);
  }

  tmp = bzla_bv_new_random (mm, &bzla->rng, bw_x);
  res = set_const_bits (mm, d_res_x, tmp);
  bzla_bv_free (mm, tmp);
#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_mul, mul, s, t, res, idx_x, "*");
#endif
  bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_udiv_bvprop(Bzla *bzla,
                               BzlaNode *div,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains)
{
  assert(bzla);
  assert(div);
  assert(t);
  assert(s);
  assert(domains);
  // TODO disabled for now, need to rethink inverse value computation with
  // propagator domains
#if 0
  assert (bzla_node_is_regular (div));
  assert (bzla_hashint_map_contains (domains, div->id));
  assert (bzla_bv_get_width (s) == bzla_bv_get_width (t));
  assert (idx_x >= 0 && idx_x <= 1);
  assert (!bzla_node_is_bv_const (div->e[idx_x]));

  uint32_t bw_x;
  BzlaNode *x;
  BzlaBitVector *res, *tmp, *tmp_res, *one, *ones, *up, *lo;
  BzlaBvDomain *d_s, *d_t, *d_x, *d_res_s, *d_res_t, *d_res_x;
  bool is_valid;
  BzlaMemMgr *mm;
  BzlaRNG *rng;

  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_udiv++;
#endif
    BZLA_PROP_SOLVER (bzla)->stats.props_inv += 1;
  }

  mm  = bzla->mm;
  rng = &bzla->rng;

  x  = bzla_node_real_addr (div->e[idx_x]);
  bw_x = bzla_bv_get_width (s);
  assert (bw_x == bzla_node_bv_get_width (bzla, x));

  d_s = bzla_bvprop_new_fixed (mm, s);
  d_t = bzla_bvprop_new_fixed (mm, t);
  d_x = bzla_hashint_map_get (domains, x->id)->as_ptr;
  assert (bzla_bv_get_width (d_x->lo) == bw_x);
  assert (bzla_bv_get_width (d_x->hi) == bw_x);

  is_valid =
      idx_x
          ? bzla_bvprop_udiv (mm, d_s, d_x, d_t, &d_res_s, &d_res_x, &d_res_t)
          : bzla_bvprop_udiv (mm, d_x, d_s, d_t, &d_res_x, &d_res_s, &d_res_t);

  if (!is_valid)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER (bzla)->stats.inv_udiv_conflicts++;
    BZLA_PROP_SOLVER (bzla)->stats.inv_udiv--;
    BZLA_PROP_SOLVER (bzla)->stats.props_inv--;
#endif
    // TODO for now fall back, but we want to be able to handle this smarter
    bzla_bvprop_free (mm, d_s);
    bzla_bvprop_free (mm, d_t);
    bzla_bvprop_free (mm, d_res_s);
    bzla_bvprop_free (mm, d_res_t);
    bzla_bvprop_free (mm, d_res_x);
    return bzla_proputils_inv_udiv (bzla, div, t, s, idx_x, domains);
  }

  one  = bzla_bv_one (mm, bw_x);
  ones = bzla_bv_ones (mm, bw_x);

  /* ----------------------------------------------------------------------
   * s / e[1] = t
   *
   * -> if t = 2^bw_x - 1: + s = t = 2^bw_x - 1 -> e[1] = 1 or e[1] = 0
   *                     + s != t -> e[1] = 0
   * -> if t = 0 and 0 < s < 2^bw_x - 1 choose random e[1] > s
   *             and s = 0            choose random e[1] > 0
   *             else conflict
   * -> if s < t -> conflict
   * -> if t is a divisor of s choose with 0.5 prob out of
   *      + e[1] = t / s
   *      + choose s s.t. s / e[1] = t
   * -> else choose s s.t. s / e[1] = t
   * ---------------------------------------------------------------------- */
  if (idx_x)
  {
    if (!bzla_bv_compare (t, ones))
    {
      if (!bzla_bv_compare (s, t) && bzla_rng_pick_with_prob (rng, 500))
      {
        /**
         * s = t = 2^bw_x - 1 -> choose either e[1] = 0 or e[1] = 1
         * with prob 0.5
         */
        tmp_res = bzla_bv_one (mm, bw_x);
      }
      else
      {
        /* t = 2^bw_x - 1 and s != t -> e[1] = 0 */
        tmp_res = bzla_bv_new (mm, bw_x);
      }
    }
    else if (bzla_bv_is_zero (t))
    {
      if (bzla_bv_is_zero (s))
      {
        /* t = 0 and s = 0 -> choose random e[1] > 0 */
        tmp_res = bzla_bv_new_random_range (mm, rng, bw_x, one, ones);
      }
      else
      {
        assert (bzla_bv_compare (s, ones)); /* CONFLICT: s = ~0  and t = 0 */

        /* t = 0 and 0 < s < 2^bw_x - 1 -> choose random e[1] > s */
        tmp     = bzla_bv_inc (mm, s);
        tmp_res = bzla_bv_new_random_range (mm, rng, bw_x, tmp, ones);
        bzla_bv_free (mm, tmp);
      }
    }
    else
    {
      assert (bzla_bv_compare (s, t) >= 0); /* CONFLICT: s < t */

      /**
       * if t is a divisor of s, choose e[1] = s / t
       * with prob = 0.5 and a s s.t. s / e[1] = t otherwise
       */
      tmp = bzla_bv_urem (mm, s, t);
      if (bzla_bv_is_zero (tmp) && bzla_rng_pick_with_prob (rng, 500))
      {
        bzla_bv_free (mm, tmp);
        tmp_res = bzla_bv_udiv (mm, s, t);
      }
      else
      {
        /**
         * choose e[1] out of all options that yield s / e[1] = t
         * Note: udiv always truncates the results towards 0.
         */

        /* determine upper and lower bounds for e[1]:
         * up = s / t
         * lo = s / (t + 1) + 1
         * if lo > up -> conflict */
        bzla_bv_free (mm, tmp);
        up  = bzla_bv_udiv (mm, s, t); /* upper bound */
        tmp = bzla_bv_inc (mm, t);
        lo  = bzla_bv_udiv (mm, s, tmp); /* lower bound (excl.) */
        bzla_bv_free (mm, tmp);
        tmp = lo;
        lo  = bzla_bv_inc (mm, tmp); /* lower bound (incl.) */
        bzla_bv_free (mm, tmp);

        assert (bzla_bv_compare (lo, up) <= 0); /* CONFLICT: lo > up */

        /* choose lo <= e[1] <= up */
        tmp_res = bzla_bv_new_random_range (mm, rng, bw_x, lo, up);
        bzla_bv_free (mm, lo);
        bzla_bv_free (mm, up);
      }
    }
  }
  /* ----------------------------------------------------------------------
   * e[0] / s = t
   *
   * -> if t = 2^bw_x - 1 and s = 1 e[0] = 2^bw_x-1
   *                    and s = 0, choose random e[0] > 0
   *                    and s > 0 -> conflict
   * -> if s = 0 and t < 2^bw_x - 1 -> conflict
   * -> if s * t does not overflow, choose with 0.5 prob out of
   *      + e[0] = s * t
   *      + choose s s.t. e[0] / s = t
   * -> else choose s s.t. e[0] / s = t
   * ---------------------------------------------------------------------- */
  else
  {
    if (!bzla_bv_compare (t, ones))
    {
      if (!bzla_bv_compare (s, one))
      {
        /* t = 2^bw_x-1 and s = 1 -> e[0] = 2^bw_x-1 */
        tmp_res = bzla_bv_copy (mm, ones);
      }
      else
      {
        assert (bzla_bv_is_zero (s)); /* CONFLICT: t = ~0 and s != 0 */
        /* t = 2^bw_x - 1 and s = 0 -> choose random e[0] */
        tmp_res = bzla_bv_new_random (mm, &bzla->rng, bw_x);
      }
    }
    else
    {
      /* if s * t does not overflow, choose e[0] = s * t
       * with prob = 0.5 and a s s.t. e[0] / s = t otherwise
       * ------------------------------------------------------------------ */

      assert (!bzla_bv_is_umulo (mm, s, t)); /* CONFLICT: overflow: s * t */
      if (bzla_rng_pick_with_prob (rng, 500))
        tmp_res = bzla_bv_mul (mm, s, t);
      else
      {
        /**
         * choose e[0] out of all options that yield
         * e[0] / s = t
         * Note: udiv always truncates the results towards 0.
         */

        /* determine upper and lower bounds for e[0]:
         * up = s * (budiv + 1) - 1
         *      if s * (t + 1) does not overflow
         *      else 2^bw_x - 1
         * lo = s * t */
        lo  = bzla_bv_mul (mm, s, t);
        tmp = bzla_bv_inc (mm, t);
        if (bzla_bv_is_umulo (mm, s, tmp))
        {
          bzla_bv_free (mm, tmp);
          up = bzla_bv_copy (mm, ones);
        }
        else
        {
          up = bzla_bv_mul (mm, s, tmp);
          bzla_bv_free (mm, tmp);
          tmp = bzla_bv_dec (mm, up);
          bzla_bv_free (mm, up);
          up = tmp;
        }

        tmp_res = bzla_bv_new_random_range (
            mm, &bzla->rng, bzla_bv_get_width (s), lo, up);

        bzla_bv_free (mm, up);
        bzla_bv_free (mm, lo);
      }
    }
  }
  res = set_const_bits (mm, d_res_x, tmp_res);
  bzla_bv_free (mm, tmp_res);
#ifndef NDEBUG
  check_result_binary_dbg (bzla, bzla_bv_udiv, div, s, t, res, idx_x, "/");
#endif
  bzla_bv_free (mm, one);
  bzla_bv_free (mm, ones);
  bzla_bvprop_free (mm, d_s);
  bzla_bvprop_free (mm, d_t);
  bzla_bvprop_free (mm, d_res_s);
  bzla_bvprop_free (mm, d_res_t);
  bzla_bvprop_free (mm, d_res_x);
  return res;
#else
  (void) idx_x;
  return 0;
#endif
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_urem_bvprop(Bzla *bzla,
                               BzlaNode *urem,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains)
{
  // TODO
  return bzla_proputils_inv_urem(bzla, urem, t, s, idx_x, domains);
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_concat_bvprop(Bzla *bzla,
                                 BzlaNode *concat,
                                 BzlaBitVector *t,
                                 BzlaBitVector *s,
                                 int32_t idx_x,
                                 BzlaIntHashTable *domains)
{
  // TODO
  return bzla_proputils_inv_concat(bzla, concat, t, s, idx_x, domains);
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_slice_bvprop(Bzla *bzla,
                                BzlaNode *slice,
                                BzlaBitVector *t,
                                BzlaBitVector *s,
                                int32_t idx_x,
                                BzlaIntHashTable *domains)
{
  // TODO
  return bzla_proputils_inv_slice(bzla, slice, t, s, idx_x, domains);
}

/* -------------------------------------------------------------------------- */
/* INV: cond                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_cond_bvprop(Bzla *bzla,
                               BzlaNode *cond,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               int32_t idx_x,
                               BzlaIntHashTable *domains)
{
  // TODO
  return bzla_proputils_inv_cond(bzla, cond, t, s, idx_x, domains);
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
};

static BzlaPropComputeValue kind_to_cons_bv[BZLA_NUM_OPS_NODE] = {
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
};

static BzlaPropComputeValue kind_to_inv_bv[BZLA_NUM_OPS_NODE] = {
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
};

static BzlaPropComputeValue kind_to_inv_bvprop[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_proputils_inv_add_bvprop,
    [BZLA_BV_AND_NODE]    = bzla_proputils_inv_and_bvprop,
    [BZLA_BV_CONCAT_NODE] = bzla_proputils_inv_concat_bvprop,
    [BZLA_BV_EQ_NODE]     = bzla_proputils_inv_eq_bvprop,
    [BZLA_BV_MUL_NODE]    = bzla_proputils_inv_mul_bvprop,
    [BZLA_BV_ULT_NODE]    = bzla_proputils_inv_ult_bvprop,
    [BZLA_BV_SLICE_NODE]  = bzla_proputils_inv_slice_bvprop,
    [BZLA_BV_SLL_NODE]    = bzla_proputils_inv_sll_bvprop,
    [BZLA_BV_SRL_NODE]    = bzla_proputils_inv_srl_bvprop,
    [BZLA_BV_UDIV_NODE]   = bzla_proputils_inv_udiv_bvprop,
    [BZLA_BV_UREM_NODE]   = bzla_proputils_inv_urem_bvprop,
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
};

static BzlaPropIsInv kind_to_is_inv_const[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_is_inv_add_const,
    [BZLA_BV_AND_NODE]    = bzla_is_inv_and_const,
    [BZLA_BV_CONCAT_NODE] = bzla_is_inv_concat_const,
    [BZLA_BV_EQ_NODE]     = bzla_is_inv_eq_const,
    [BZLA_BV_MUL_NODE]    = bzla_is_inv_mul,
    [BZLA_BV_ULT_NODE]    = bzla_is_inv_ult_const,
    [BZLA_BV_SLICE_NODE]  = 0,  // different handling
    [BZLA_BV_SLL_NODE]    = bzla_is_inv_sll_const,
    [BZLA_BV_SRL_NODE]    = bzla_is_inv_srl,
    [BZLA_BV_UDIV_NODE]   = bzla_is_inv_udiv,
    [BZLA_BV_UREM_NODE]   = bzla_is_inv_urem,
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
                BzlaNode *e,
                BzlaBitVector *t,
                BzlaBitVector *s,
                int32_t idx_x)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(e);
  assert(t);
  assert(s);
  (void) s;

  BzlaMemMgr *mm      = bzla->mm;
  bool is_recoverable = bzla_node_is_bv_const(e) ? false : true;

#ifndef NDEBUG
  char *str_s = bzla_bv_to_char(mm, s);
  char *str_t = bzla_bv_to_char(mm, t);
  char *str_o = 0;
  switch (exp->kind)
  {
    case BZLA_BV_AND_NODE: str_o = "&"; break;
    case BZLA_BV_ULT_NODE: str_o = "<"; break;
    case BZLA_BV_SLL_NODE: str_o = "<<"; break;
    case BZLA_BV_SRL_NODE: str_o = ">>"; break;
    case BZLA_BV_MUL_NODE: str_o = "*"; break;
    case BZLA_BV_UDIV_NODE: str_o = "/"; break;
    case BZLA_BV_UREM_NODE: str_o = "%"; break;
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
            str_s,
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
            str_s);
  }
  bzla_mem_freestr(mm, str_s);
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
      assert(exp->arity == 2);
      if (prop_entailed != BZLA_PROP_ENTAILED_OFF)
      {
        BzlaPropInfo prop = {exp, bzla_bv_copy(mm, t), idx_x ? 0 : 1};
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

  bool pick_inv, force_cons;
  int32_t i, idx_s, nconst;
  uint64_t nprops;
  BzlaNode *cur, *real_cur;
  BzlaIntHashTable *domains;
  BzlaHashTableData *d;
  BzlaBitVector *bv_s[3], *bv_t, *bv_s_new, *tmp;
  BzlaMemMgr *mm;
  uint32_t opt_prop_prob_use_inv_value, opt_prop_domains;
  uint32_t opt_prop_const_bits;

  BzlaPropSelectPath select_path;
  BzlaPropComputeValue inv_value, cons_value, compute_value;
  BzlaPropIsInv is_inv;

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

  opt_prop_domains = bzla_opt_get(bzla, BZLA_OPT_PROP_DOMAINS);
  opt_prop_prob_use_inv_value =
      bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE);
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS);

#ifndef NBZLALOG
  if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
    nrecconf_prev    = BZLA_PROP_SOLVER(bzla)->stats.rec_conf;
    nnonrecconf_prev = BZLA_PROP_SOLVER(bzla)->stats.non_rec_conf;
    domains          = BZLA_PROP_SOLVER(bzla)->domains;
    assert(!opt_prop_const_bits || domains);
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

  cur  = root;
  bv_t = bzla_bv_copy(bzla->mm, bvroot);

  for (;;)
  {
    real_cur = bzla_node_real_addr(cur);

#ifndef NDEBUG
    if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND && opt_prop_domains)
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
            assert(bzla_bvprop_is_fixed_bit_true(d, k));
          else if (bzla_aig_is_false(real_cur->av->aigs[j]))
            assert(bzla_bvprop_is_fixed_bit_false(d, k));
          else
            assert(!bzla_bvprop_is_fixed_bit(d, k));
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

      is_inv = 0;
      if (bzla_node_is_bv_cond(real_cur))
      {
        // always invertible
        select_path = select_path_cond;
      }
      else
      {
        is_inv = opt_prop_const_bits ? kind_to_is_inv_const[real_cur->kind]
                                     : kind_to_is_inv[real_cur->kind];
        select_path = kind_to_select_path[real_cur->kind];
      }

      /* select path */
      if (idx_x == -1) idx_x = select_path(bzla, real_cur, bv_t, bv_s);
      assert(idx_x >= 0 && idx_x < real_cur->arity);

      idx_s = idx_x ? 0 : 1;
      /* special case slice: only one child
       * special case cond: we only need assignment of cond to compute value */
      if (bzla_node_is_bv_slice(real_cur) || bzla_node_is_cond(real_cur))
      {
        /* Note: both are always invertible, thus is_inv and record_conflict
         *       will never be called below (is_inv = 0). */
        idx_s = 0;
      }

      /* check invertibility --> if not invertible, fall back to consistent
       * value computation */
      force_cons = false;
      if (opt_prop_const_bits && bzla_node_is_bv_slice(real_cur))
      {
        d = bzla_hashint_map_get(domains, bzla_node_get_id(real_cur->e[idx_x]));
        assert(d);
        force_cons =
            !bzla_is_inv_slice_const(mm,
                                     d->as_ptr,
                                     bv_t,
                                     bzla_node_bv_slice_get_upper(real_cur),
                                     bzla_node_bv_slice_get_lower(real_cur));
      }
      else if (is_inv)
      {
        d = bzla_hashint_map_get(domains, bzla_node_get_id(real_cur->e[idx_x]));
        assert(!opt_prop_const_bits || d);
        force_cons = !is_inv(mm, d ? d->as_ptr : 0, bv_t, bv_s[idx_s], idx_x);
      }

      /* not invertible counts as conflict */
      if (force_cons)
      {
        if (!record_conflict(
                bzla, real_cur, real_cur->e[idx_s], bv_t, bv_s[idx_s], idx_x))
        {
          break; /* non-recoverable conflict */
        }
      }

      if (bzla_node_is_bv_cond(real_cur))
      {
        cons_value = bzla_proputils_cons_cond;
        inv_value  = opt_prop_domains ? bzla_proputils_inv_cond_bvprop
                                     : bzla_proputils_inv_cond;
      }
      else
      {
        cons_value = kind_to_cons_bv[real_cur->kind];
        inv_value  = opt_prop_domains ? kind_to_inv_bvprop[real_cur->kind]
                                     : kind_to_inv_bv[real_cur->kind];
      }
      compute_value = pick_inv && !force_cons ? inv_value : cons_value;

#ifndef NDEBUG
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        BzlaPropInfo prop = {real_cur, bzla_bv_copy(bzla->mm, bv_t), idx_x};
        BZLA_PUSH_STACK(BZLA_PROP_SOLVER(bzla)->prop_path, prop);
      }
#endif
      /* compute new assignment */
      bv_s_new =
          compute_value(bzla, real_cur, bv_t, bv_s[idx_s], idx_x, domains);
      assert(bv_s_new);
#ifndef NBZLALOG
      a = bzla_bv_to_char(bzla->mm, bv_s_new);
      BZLALOG(2, "");
      BZLALOG(2,
              "%s value: %s",
              pick_inv && !force_cons ? "inverse" : "consistent",
              a);
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
