/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlaproputils.h"

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
select_path_add(Bzla *bzla,
                BzlaNode *add,
                BzlaBitVector *bvadd,
                BzlaBitVector **bve)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(bvadd);
  assert(bve);

  (void) bvadd;
  (void) bve;

  int32_t eidx;

  eidx = select_path_non_const(add);
  if (eidx == -1) eidx = select_path_random(bzla, add);
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(add));
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(add->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(add->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_and(Bzla *bzla,
                BzlaNode *and,
                BzlaBitVector *bvand,
                BzlaBitVector **bve)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(bvand);
  assert(bve);

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
        if (bzla_bv_is_zero(bve[i])) eidx = eidx == -1 ? i : -1;
      if (eidx == -1) eidx = select_path_random(bzla, and);
    }
    else if (opt == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* 1) all bits set in bvand must be set in both inputs, but
       * 2) all bits NOT set in bvand can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < and->arity; i++)
      {
        tmp = bzla_bv_and(mm, bvand, bve[i]);
        if (bzla_bv_compare(tmp, bvand)) eidx = eidx == -1 ? i : -1;
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(and->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(and->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_eq(Bzla *bzla,
               BzlaNode *eq,
               BzlaBitVector *bveq,
               BzlaBitVector **bve)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(bveq);
  assert(bve);

  (void) bveq;
  (void) bve;

  int32_t eidx;
  eidx = select_path_non_const(eq);
  if (eidx == -1) eidx = select_path_random(bzla, eq);
  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(eq));
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(eq->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(eq->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_ult(Bzla *bzla,
                BzlaNode *ult,
                BzlaBitVector *bvult,
                BzlaBitVector **bve)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(bvult);
  assert(bve);

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
      bvmax = bzla_bv_ones(mm, bzla_bv_get_width(bve[0]));
      if (bzla_bv_is_one(bvult))
      {
        /* 1...1 < bve[1] */
        if (!bzla_bv_compare(bve[0], bvmax)) eidx = 0;
        /* bve[0] < 0 */
        if (bzla_bv_is_zero(bve[1])) eidx = eidx == -1 ? 1 : -1;
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(ult->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(ult->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_sll(Bzla *bzla,
                BzlaNode *sll,
                BzlaBitVector *bvsll,
                BzlaBitVector **bve)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(bvsll);
  assert(bve);

  int32_t eidx;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp;
  BzlaMemMgr *mm;

  eidx = select_path_non_const(sll);

  mm = bzla->mm;
  bw = bzla_bv_get_width(bvsll);
  assert(bzla_bv_get_width(bve[0]) == bw);
  assert(bzla_bv_get_width(bve[1]) == bw);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (bw > 64)
      {
        bv_bw = bzla_bv_uint64_to_bv(mm, bw, bw);
        tmp   = bzla_bv_ugte(mm, bve[1], bv_bw);
        if (bzla_bv_is_one(tmp) && !bzla_bv_is_zero(bvsll))
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
        tmp   = bzla_bv_slice(mm, bve[1], 32, 0);
        shift = bzla_bv_to_uint64(tmp);
        bzla_bv_free(mm, tmp);
      }
      else
      {
        shift = bzla_bv_to_uint64(bve[1]);
      }
      /* if shift is greater than bit-width, result must be zero */
      if (!bzla_bv_is_zero(bvsll) && shift >= bw)
      {
        eidx = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* bve[1] and number of LSB 0-bits in bvsll must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(bvsll, i))
          {
            eidx = 1;
            goto DONE;
          }
        }
        /* bve[0] and bvsll (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(bve[0], i) != bzla_bv_get_bit(bvsll, j + i))
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(sll->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(sll->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_srl(Bzla *bzla,
                BzlaNode *srl,
                BzlaBitVector *bvsrl,
                BzlaBitVector **bve)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(bvsrl);
  assert(bve);

  int32_t eidx;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp;
  BzlaMemMgr *mm;

  eidx = select_path_non_const(srl);

  mm = bzla->mm;
  bw = bzla_bv_get_width(bvsrl);
  assert(bzla_bv_get_width(bve[0]) == bw);
  assert(bzla_bv_get_width(bve[1]) == bw);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (bw > 64)
      {
        bv_bw = bzla_bv_uint64_to_bv(mm, bw, bw);
        tmp   = bzla_bv_ugte(mm, bve[1], bv_bw);
        if (bzla_bv_is_one(tmp) && !bzla_bv_is_zero(bvsrl))
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
        tmp   = bzla_bv_slice(mm, bve[1], 32, 0);
        shift = bzla_bv_to_uint64(tmp);
        bzla_bv_free(mm, tmp);
      }
      else
      {
        shift = bzla_bv_to_uint64(bve[1]);
      }
      /* if shift is greater than bit-width, result must be zero */
      if (!bzla_bv_is_zero(bvsrl) && shift >= bw)
      {
        eidx = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* bve[1] and number of MSB 0-bits in bvsrl must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit(bvsrl, bw - 1 - i))
          {
            eidx = 1;
            goto DONE;
          }
        }
        /* bve[0] and bvsrl (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit(bve[0], bw - 1 - i)
              != bzla_bv_get_bit(bvsrl, bw - 1 - (j + i)))
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(srl->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(srl->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_mul(Bzla *bzla,
                BzlaNode *mul,
                BzlaBitVector *bvmul,
                BzlaBitVector **bve)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(bvmul);
  assert(bve);

  uint32_t ctz_bvmul;
  int32_t eidx, lsbve0, lsbve1;
  bool iszerobve0, iszerobve1;

  eidx = select_path_non_const(mul);

  if (eidx == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      iszerobve0 = bzla_bv_is_zero(bve[0]);
      iszerobve1 = bzla_bv_is_zero(bve[1]);

      lsbve0 = bzla_bv_get_bit(bve[0], 0);
      lsbve1 = bzla_bv_get_bit(bve[1], 0);

      /* either bve[0] or bve[1] are 0 but bvmul > 0 */
      if ((iszerobve0 || iszerobve1) && !bzla_bv_is_zero(bvmul))
      {
        if (iszerobve0) eidx = 0;
        if (iszerobve1) eidx = eidx == -1 ? 1 : -1;
      }
      /* bvmul is odd but either bve[0] or bve[1] are even */
      else if (bzla_bv_get_bit(bvmul, 0) && (!lsbve0 || !lsbve1))
      {
        if (!lsbve0) eidx = 0;
        if (!lsbve1) eidx = eidx == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in bvmul < number of 0-LSBs in bve[0|1] */
      else
      {
        ctz_bvmul = bzla_bv_get_num_trailing_zeros(bvmul);
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(bve[0])) eidx = 0;
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros(bve[1]))
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(mul->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(mul->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_udiv(Bzla *bzla,
                 BzlaNode *udiv,
                 BzlaBitVector *bvudiv,
                 BzlaBitVector **bve)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(bvudiv);
  assert(bve);

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
      bvmax        = bzla_bv_ones(mm, bzla_bv_get_width(bve[0]));
      cmp_udiv_max = bzla_bv_compare(bvudiv, bvmax);

      /* bve[0] / bve[1] = 1...1 -> choose e[1]
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        eidx = 1;
      else
      {
        /* 1...1 / e[0] = 0 -> choose e[0] */
        if (bzla_bv_is_zero(bvudiv) && !bzla_bv_compare(bve[0], bvmax))
          eidx = 0;
        /* bve[0] < bvudiv -> choose e[0] */
        else if (bzla_bv_compare(bve[0], bvudiv) < 0)
          eidx = 0;
        else
        {
          up  = bzla_bv_udiv(mm, bve[0], bvudiv);
          lo  = bzla_bv_inc(mm, bvudiv);
          tmp = bzla_bv_udiv(mm, bve[0], lo);
          bzla_bv_free(mm, lo);
          lo = bzla_bv_inc(mm, tmp);

          if (bzla_bv_compare(lo, up) > 0) eidx = 0;
          bzla_bv_free(mm, up);
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, tmp);
        }

        /* e[0] / 0 != 1...1 -> choose e[1] */
        if (bzla_bv_is_zero(bve[1]) || bzla_bv_is_umulo(mm, bve[1], bvudiv))
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(udiv->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(udiv->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_urem(Bzla *bzla,
                 BzlaNode *urem,
                 BzlaBitVector *bvurem,
                 BzlaBitVector **bve)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(bvurem);
  assert(bve);

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
      bvmax = bzla_bv_ones(mm, bzla_bv_get_width(bve[0]));
      sub   = bzla_bv_sub(mm, bve[0], bvurem);
      tmp   = bzla_bv_dec(mm, bve[0]);

      /* bvurem = 1...1 -> bve[0] = 1...1 and bve[1] = 0...0 */
      if (!bzla_bv_compare(bvurem, bvmax))
      {
        if (!bzla_bv_is_zero(bve[1])) eidx = 1;
        if (bzla_bv_compare(bve[0], bvmax)) eidx = eidx == -1 ? 0 : -1;
      }
      /* bvurem > 0 and bve[1] = 1 */
      else if (!bzla_bv_is_zero(bvurem) && bzla_bv_is_one(bve[1]))
      {
        eidx = 1;
      }
      /* 0 < bve[1] <= bvurem */
      else if (!bzla_bv_is_zero(bve[1]) && bzla_bv_compare(bve[1], bvurem) <= 0)
      {
        eidx = eidx == -1 ? 1 : -1;
      }
      /* bve[0] < bvurem or
       * bve[0] > bvurem and bve[0] - bvurem <= bvurem or
       *                 and bve[0] - 1 = bvurem */
      else if (bzla_bv_compare(bve[0], bvurem) < 0
               || (bzla_bv_compare(bve[0], bvurem) > 0
                   && (bzla_bv_compare(sub, bvurem) <= 0
                       || !bzla_bv_compare(tmp, bvurem))))
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
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(urem->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(urem->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_concat(Bzla *bzla,
                   BzlaNode *concat,
                   BzlaBitVector *bvconcat,
                   BzlaBitVector **bve)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(bvconcat);
  assert(bve);

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
      /* bve[0] o bve[1] = bvconcat
       * -> bve[0] resp. bve[1] must match with bvconcat */
      bw_concat = bzla_bv_get_width(bvconcat);
      tmp       = bzla_bv_slice(
          mm, bvconcat, bw_concat - 1, bw_concat - bzla_bv_get_width(bve[0]));
      if (bzla_bv_compare(tmp, bve[0])) eidx = 0;
      bzla_bv_free(mm, tmp);
      tmp = bzla_bv_slice(mm, bvconcat, bzla_bv_get_width(bve[1]) - 1, 0);
      if (bzla_bv_compare(tmp, bve[1])) eidx = eidx == -1 ? 1 : -1;
      bzla_bv_free(mm, tmp);
    }

    if (eidx == -1) eidx = select_path_random(bzla, concat);
  }

  assert(eidx >= 0);
#ifndef NBZLALOG
  char *a;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(concat));
  a = bzla_bv_to_char(mm, bve[0]);
  BZLALOG(2, "       e[0]: %s (%s)", bzla_util_node2string(concat->e[0]), a);
  bzla_mem_freestr(mm, a);
  a = bzla_bv_to_char(mm, bve[1]);
  BZLALOG(2, "       e[1]: %s (%s)", bzla_util_node2string(concat->e[1]), a);
  bzla_mem_freestr(mm, a);
  BZLALOG(2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_slice(Bzla *bzla,
                  BzlaNode *slice,
                  BzlaBitVector *bvslice,
                  BzlaBitVector **bve)
{
  assert(bzla);
  assert(slice);
  assert(bzla_node_is_regular(slice));
  assert(bvslice);
  assert(bve);

  assert(!bzla_node_is_bv_const(slice->e[0]));

  (void) bzla;
  (void) slice;
  (void) bvslice;
  (void) bve;
#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;
  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(slice));
  a = bzla_bv_to_char(mm, bve[0]);
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
                 BzlaBitVector **bve)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP
         || bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(bvcond);
  assert(bve);

  bool e1const, e2const;
  int32_t eidx;
  uint32_t prob;
  BzlaBitVector *bve0;

  (void) bvcond;

  bve0 = *bve;
  assert(bve0);

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
    if (((e1const && bzla_bv_is_true(bve0))
         || (e2const && bzla_bv_is_false(bve0)))
        && bzla_rng_pick_with_prob(
            &bzla->rng,
            (prob = bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND_CONST))))
    {
      eidx = 0;

      if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
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
      eidx = bzla_bv_is_true(bve0) ? 1 : 2;
    }
  }

#ifndef NBZLALOG
  char *a;
  BzlaMemMgr *mm = bzla->mm;

  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(cond));
  a = bzla_bv_to_char(mm, bve0);
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
cons_add_bv(Bzla *bzla,
            BzlaNode *add,
            BzlaBitVector *bvadd,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(bvadd);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvadd));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(add->e[eidx]));

  (void) add;
  (void) bve;
  (void) eidx;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_add++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  return bzla_bv_new_random(bzla->mm, &bzla->rng, bzla_bv_get_width(bvadd));
}

static BzlaBitVector *
cons_and_bv(Bzla *bzla,
            BzlaNode *and,
            BzlaBitVector *bvand,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(bvand);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvand));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(and->e[eidx]));

  uint32_t i, bw;
  BzlaBitVector *res;
  BzlaUIntStack dcbits;
  bool b;

  (void) bve;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
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

  /* bve & res = bvand
   * -> all bits set in bvand must be set in res
   * -> all bits not set in bvand are chosen to be set randomly */
  for (i = 0, bw = bzla_bv_get_width(bvand); i < bw; i++)
  {
    if (bzla_bv_get_bit(bvand, i))
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
cons_eq_bv(Bzla *bzla,
           BzlaNode *eq,
           BzlaBitVector *bveq,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(bveq);
  assert(bzla_bv_get_width(bveq) == 1);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(eq->e[eidx]));

  (void) bveq;

  BzlaBitVector *res;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
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
    res = bzla_bv_new_random(bzla->mm, &bzla->rng, bzla_bv_get_width(bve));
  }
  return res;
}

static BzlaBitVector *
cons_ult_bv(Bzla *bzla,
            BzlaNode *ult,
            BzlaBitVector *bvult,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(bvult);
  assert(bzla_bv_get_width(bvult) == 1);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BzlaBitVector *bvmax, *zero, *tmp, *res;
  BzlaMemMgr *mm;

  (void) ult;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_ult++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(bve);
  isult = !bzla_bv_is_zero(bvult);
  zero  = bzla_bv_new(mm, bw);
  bvmax = bzla_bv_ones(mm, bw);

  if (eidx && isult)
  {
    /* bve < res = 1  ->  res > 0 */
    tmp = bzla_bv_one(mm, bw);
    res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
    bzla_bv_free(mm, tmp);
  }
  else if (!eidx && isult)
  {
    /* res < bve = 1  ->  0 <= res < 1...1 */
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
cons_sll_bv(Bzla *bzla,
            BzlaNode *sll,
            BzlaBitVector *bvsll,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(bvsll);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvsll));
  assert(!bzla_node_is_bv_const(sll->e[eidx]));

  uint32_t i, bw, ctz_bvsll, shift;
  BzlaBitVector *res, *bv_shift;
  BzlaMemMgr *mm;

  (void) sll;
  (void) bve;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_sll++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm = bzla->mm;
  bw = bzla_bv_get_width(bvsll);

  ctz_bvsll = bzla_bv_get_num_trailing_zeros(bvsll);
  shift     = bzla_rng_pick_rand(
      &bzla->rng, 0, ctz_bvsll == bw ? ctz_bvsll - 1 : ctz_bvsll);
  bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);

  if (eidx)
  {
    res = bv_shift;
  }
  else
  {
    res = bzla_bv_srl(mm, bvsll, bv_shift);
    for (i = 0; i < shift; i++)
    {
      bzla_bv_set_bit(res, bw - 1 - i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

static BzlaBitVector *
cons_srl_bv(Bzla *bzla,
            BzlaNode *srl,
            BzlaBitVector *bvsrl,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(bvsrl);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvsrl));
  assert(!bzla_node_is_bv_const(srl->e[eidx]));

  uint32_t i, shift, bw;
  BzlaBitVector *res, *bv_shift;
  BzlaMemMgr *mm;

  (void) srl;
  (void) bve;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_srl++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm = bzla->mm;
  bw = bzla_bv_get_width(bvsrl);

  for (i = 0; i < bw; i++)
  {
    if (bzla_bv_get_bit(bvsrl, bw - 1 - i)) break;
  }

  shift    = bzla_rng_pick_rand(&bzla->rng, 0, i == bw ? i - 1 : i);
  bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);

  if (eidx)
  {
    res = bv_shift;
  }
  else
  {
    res = bzla_bv_sll(mm, bvsrl, bv_shift);
    for (i = 0; i < shift; i++)
    {
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
    bzla_bv_free(mm, bv_shift);
  }
  return res;
}

static BzlaBitVector *
cons_mul_bv(Bzla *bzla,
            BzlaNode *mul,
            BzlaBitVector *bvmul,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(bvmul);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvmul));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(mul->e[eidx]));

  uint32_t r, bw, ctz_res, ctz_bvmul;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;

  (void) mul;
  (void) bve;
  (void) eidx;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_mul++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  mm  = bzla->mm;
  bw  = bzla_bv_get_width(bvmul);
  res = bzla_bv_new_random(mm, &bzla->rng, bw);
  if (!bzla_bv_is_zero(bvmul))
  {
    if (bzla_bv_is_zero(res))
    {
      bzla_bv_free(mm, res);
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    /* bvmul odd -> choose odd value > 0 */
    if (bzla_bv_get_bit(bvmul, 0))
    {
      if (!bzla_bv_get_bit(res, 0)) bzla_bv_set_bit(res, 0, 1);
    }
    /* bvmul even -> choose random value > 0
     *               with number of 0-LSBs in res less or equal
     *               than in bvmul */
    else
    {
      ctz_bvmul = bzla_bv_get_num_trailing_zeros(bvmul);
      /* choose res as 2^n with ctz(bvmul) >= ctz(res) with prob 0.1 */
      if (bzla_rng_pick_with_prob(&bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        res = bzla_bv_new(mm, bw);
        bzla_bv_set_bit(
            res, bzla_rng_pick_rand(&bzla->rng, 0, ctz_bvmul - 1), 1);
      }
      /* choose res as bvmul / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (bzla_rng_pick_with_prob(&bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        if ((r = bzla_rng_pick_rand(&bzla->rng, 0, ctz_bvmul)))
        {
          tmp = bzla_bv_slice(mm, bvmul, bw - 1, r);
          res = bzla_bv_uext(mm, tmp, r);
          bzla_bv_free(mm, tmp);
        }
        else
        {
          res = bzla_bv_copy(mm, bvmul);
        }
      }
      /* choose random value with ctz(bvmul) >= ctz(res) with prob 0.8 */
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
             BzlaBitVector *bvudiv,
             BzlaBitVector *bve,
             int32_t eidx)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(bvudiv);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvudiv));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(udiv->e[eidx]));

  uint32_t bw;
  BzlaBitVector *res, *tmp, *tmpbve, *zero, *one, *bvmax;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  bw    = bzla_bv_get_width(bvudiv);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  bvmax = bzla_bv_ones(mm, bw);

  (void) udiv;
  (void) bve;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_udiv++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  if (eidx)
  {
    /* -> bvudiv = 1...1 then res = 0 or res = 1
     * -> else choose res s.t. res * bvudiv does not overflow */
    if (!bzla_bv_compare(bvudiv, bvmax))
      res = bzla_bv_uint64_to_bv(mm, bzla_rng_pick_rand(&bzla->rng, 0, 1), bw);
    else
    {
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, bvmax);
      while (bzla_bv_is_umulo(mm, res, bvudiv))
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
    /* -> bvudiv = 0 then res < 1...1
     * -> bvudiv = 1...1 then choose random res
     * -> else choose tmpbve s.t. res = tmpbve * bvudiv does not overflow */
    if (bzla_bv_is_zero(bvudiv))
    {
      tmp = bzla_bv_dec(mm, bvmax);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
    else if (!bzla_bv_compare(bvudiv, bvmax))
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      tmpbve = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, bvmax);
      while (bzla_bv_is_umulo(mm, tmpbve, bvudiv))
      {
        tmp = bzla_bv_sub(mm, tmpbve, one);
        bzla_bv_free(mm, tmpbve);
        tmpbve = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
        bzla_bv_free(mm, tmp);
      }
      res = bzla_bv_mul(mm, tmpbve, bvudiv);
      bzla_bv_free(mm, tmpbve);
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
             BzlaBitVector *bvurem,
             BzlaBitVector *bve,
             int32_t eidx)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(bvurem);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvurem));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(urem->e[eidx]));

  uint32_t bw;
  BzlaBitVector *res, *bvmax, *tmp;
  BzlaMemMgr *mm;

  (void) urem;
  (void) bve;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_urem++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  mm    = bzla->mm;
  bw    = bzla_bv_get_width(bvurem);
  bvmax = bzla_bv_ones(mm, bw);

  if (eidx)
  {
    /* bvurem = 1...1  ->  res = 0 */
    if (!bzla_bv_compare(bvurem, bvmax))
    {
      res = bzla_bv_new(mm, bw);
    }
    /* else res > bvurem */
    else
    {
      tmp = bzla_bv_inc(mm, bvurem);
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(mm, tmp);
    }
  }
  else
  {
    /* bvurem = 1...1  ->  res = 1...1 */
    if (!bzla_bv_compare(bvurem, bvmax))
    {
      res = bzla_bv_copy(mm, bvmax);
    }
    /* else res >= bvurem */
    else
    {
      res = bzla_bv_new_random_range(mm, &bzla->rng, bw, bvurem, bvmax);
    }
  }

  bzla_bv_free(mm, bvmax);
  return res;
}

static BzlaBitVector *
cons_concat_bv(Bzla *bzla,
               BzlaNode *concat,
               BzlaBitVector *bvconcat,
               BzlaBitVector *bve,
               int32_t eidx)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(bvconcat);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(concat->e[eidx]));

  int32_t idx, bw_t, bw_s;
  uint32_t r;
  BzlaBitVector *res;
  const BzlaBitVector *bvcur;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_concat++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }

  idx  = eidx ? 0 : 1;
  bw_t = bzla_bv_get_width(bvconcat);
  bw_s = bzla_bv_get_width(bve);

  /* If one operand is const, with BZLA_OPT_CONC_FLIP_PROB
   * either slice bits out of current assignment and flip max. one bit
   * randomly, or slice bits out of given assignment 'bve'.  */

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
    res = eidx ? bzla_bv_slice(bzla->mm, bvconcat, bw_t - bw_s - 1, 0)
               : bzla_bv_slice(bzla->mm, bvconcat, bw_t - 1, bw_s);
  }
  return res;
}

static BzlaBitVector *
cons_slice_bv(Bzla *bzla,
              BzlaNode *slice,
              BzlaBitVector *bvslice,
              BzlaBitVector *bve,
              int32_t eidx)
{
  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_slice++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  return inv_slice_bv(bzla, slice, bvslice, bve, eidx);
}

static BzlaBitVector *
cons_cond_bv(Bzla *bzla,
             BzlaNode *cond,
             BzlaBitVector *bvcond,
             BzlaBitVector *bve,
             int32_t eidx)
{
  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.cons_cond++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_cons += 1;
  }
  return inv_cond_bv(bzla, cond, bvcond, bve, eidx);
}

/* ========================================================================== */
/* Inverse value computation                                                  */
/* ========================================================================== */

static BzlaBitVector *
res_rec_conf(Bzla *bzla,
             BzlaNode *exp,
             BzlaNode *e,
             BzlaBitVector *bvexp,
             BzlaBitVector *bve,
             int32_t eidx,
             BzlaBitVector *(*fun)(
                 Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t),
             char *op)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP
         || bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(e);
  assert(bvexp);
  assert(bve);
  assert(op);
  (void) op;
  (void) e;

  bool is_recoverable = bzla_node_is_bv_const(e) ? false : true;
  BzlaBitVector *res =
      bzla_opt_get(bzla, BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT) && !is_recoverable
          ? 0
          : fun(bzla, exp, bvexp, bve, eidx);
  assert(bzla_opt_get(bzla, BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT) || res);

#ifndef NDEBUG
  char *sbve   = bzla_bv_to_char(bzla->mm, bve);
  char *sbvexp = bzla_bv_to_char(bzla->mm, bvexp);
  BZLALOG(2, "");
  if (eidx)
    BZLALOG(2,
            "%s CONFLICT (@%d): %s := %s %s x",
            is_recoverable ? "recoverable" : "non-recoverable",
            bzla_node_get_id(exp),
            sbvexp,
            sbve,
            op);
  else
    BZLALOG(2,
            "%s CONFLICT (@%d): %s := x %s %s",
            is_recoverable ? "recoverable" : "non-recoverable",
            bzla_node_get_id(exp),
            sbvexp,
            op,
            sbve);
  bzla_mem_freestr(bzla->mm, sbve);
  bzla_mem_freestr(bzla->mm, sbvexp);
#endif
  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    /* fix counters since we always increase the counter, even in the conflict
     * case */
    switch (exp->kind)
    {
      case BZLA_BV_ADD_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_add -= 1; break;
      case BZLA_BV_AND_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_and -= 1; break;
      case BZLA_BV_EQ_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_eq -= 1; break;
      case BZLA_BV_ULT_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_ult -= 1; break;
      case BZLA_BV_SLL_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_sll -= 1; break;
      case BZLA_BV_SRL_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_srl -= 1; break;
      case BZLA_BV_MUL_NODE: BZLA_PROP_SOLVER(bzla)->stats.inv_mul -= 1; break;
      case BZLA_BV_UDIV_NODE:
        BZLA_PROP_SOLVER(bzla)->stats.inv_udiv -= 1;
        break;
      case BZLA_BV_UREM_NODE:
        BZLA_PROP_SOLVER(bzla)->stats.inv_urem -= 1;
        break;
      case BZLA_BV_CONCAT_NODE:
        BZLA_PROP_SOLVER(bzla)->stats.inv_concat -= 1;
        break;
      case BZLA_BV_SLICE_NODE:
        BZLA_PROP_SOLVER(bzla)->stats.inv_slice -= 1;
        break;
      default:
        assert(bzla_node_is_bv_cond(exp));
        /* do not decrease, we do not call cons function in conflict case */
    }
#endif
    if (is_recoverable)
    {
      BZLA_PROP_SOLVER(bzla)->stats.rec_conf += 1;
      /* recoverable conflict, push entailed propagation */
      assert(exp->arity == 2);
      BzlaPropInfo prop = {exp, bzla_bv_copy(bzla->mm, bvexp), eidx ? 0 : 1};
      BZLA_PUSH_STACK(BZLA_PROP_SOLVER(bzla)->toprop, prop);
    }
    else
    {
      BZLA_PROP_SOLVER(bzla)->stats.non_rec_conf += 1;
      /* non-recoverable conflict, entailed propagations are thus invalid */
      bzla_proputils_reset_prop_info_stack(bzla->mm,
                                           &BZLA_PROP_SOLVER(bzla)->toprop);
    }
    /* fix counter since we always increase the counter, even in the conflict
     * case */
    BZLA_PROP_SOLVER(bzla)->stats.props_inv -= 1;
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
                        BzlaBitVector *bve,
                        BzlaBitVector *bvexp,
                        BzlaBitVector *res,
                        int32_t eidx,
                        char *op)
{
  assert(bzla);
  assert(fun);
  assert(exp);
  assert(bve);
  assert(bvexp);
  assert(res);
  assert(op);

  (void) exp;
  (void) op;

  BzlaBitVector *tmp;
  char *sbve, *sbvexp, *sres;

  tmp = eidx ? fun(bzla->mm, bve, res) : fun(bzla->mm, res, bve);
  assert(!bzla_bv_compare(tmp, bvexp));
  sbvexp = bzla_bv_to_char(bzla->mm, bvexp);
  sbve   = bzla_bv_to_char(bzla->mm, bve);
  sres   = bzla_bv_to_char(bzla->mm, res);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s %s %s",
          eidx,
          bzla_util_node2string(exp),
          sbvexp,
          eidx ? sbve : sres,
          op,
          eidx ? sres : sbve);
  bzla_bv_free(bzla->mm, tmp);
  bzla_mem_freestr(bzla->mm, sbvexp);
  bzla_mem_freestr(bzla->mm, sbve);
  bzla_mem_freestr(bzla->mm, sres);
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
inv_add_bv(Bzla *bzla,
           BzlaNode *add,
           BzlaBitVector *bvadd,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(add);
  assert(bzla_node_is_regular(add));
  assert(bvadd);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvadd));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(add->e[eidx]));

  BzlaBitVector *res;

  (void) add;
  (void) eidx;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_add++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  /* res + bve = bve + res = bvadd -> res = bvadd - bve */
  res = bzla_bv_sub(bzla->mm, bvadd, bve);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_add, add, bve, bvadd, res, eidx, "+");
#endif
  return res;
}

#ifdef NDEBUG
static BzlaBitVector *
#else
BzlaBitVector *
#endif
inv_and_bv(Bzla *bzla,
           BzlaNode *and,
           BzlaBitVector *bvand,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(and);
  assert(bzla_node_is_regular(and));
  assert(bvand);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvand));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(and->e[eidx]));

  uint32_t i, bw;
  int32_t bitand, bite;
  BzlaNode *e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  BzlaUIntStack dcbits;
  bool b;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_and++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = and->e[eidx ? 0 : 1];
  assert(e);

  b = bzla_rng_pick_with_prob(&bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));
  BZLA_INIT_STACK(mm, dcbits);

  res = bzla_bv_copy(mm, bzla_model_get_bv(bzla, and->e[eidx]));
  assert(res);

  for (i = 0, bw = bzla_bv_get_width(bvand); i < bw; i++)
  {
    bitand = bzla_bv_get_bit(bvand, i);
    bite   = bzla_bv_get_bit(bve, i);

    if (bitand&&!bite)
    {
      /* CONFLICT: all bits set in bvand, must be set in bve ---------------- */
      bzla_bv_free(mm, res);
      res = res_rec_conf(bzla, and, e, bvand, bve, eidx, cons_and_bv, "AND");
      goto DONE;
    }

    /* ----------------------------------------------------------------------
     * res & bve = bve & res = bvand
     *
     * -> all bits set in bvand and bve must be set in res
     * -> all bits not set in bvand but set in bve must not be set in res
     * -> all bits not set in bve can be chosen to be set randomly
     * ---------------------------------------------------------------------- */
    if (bitand)
      bzla_bv_set_bit(res, i, 1);
    else if (bite)
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
  check_result_binary_dbg(bzla, bzla_bv_and, and, bve, bvand, res, eidx, "AND");
#endif

DONE:
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
inv_eq_bv(Bzla *bzla,
          BzlaNode *eq,
          BzlaBitVector *bveq,
          BzlaBitVector *bve,
          int32_t eidx)
{
  assert(bzla);
  assert(eq);
  assert(bzla_node_is_regular(eq));
  assert(bveq);
  assert(bzla_bv_get_width(bveq) == 1);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(eq->e[eidx]));

  BzlaBitVector *res;
  BzlaMemMgr *mm;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_eq++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;

  if (bzla_bv_is_zero(bveq))
  {
    /* res != bveq -> choose random res != bveq ----------------------------- */
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
      } while (!bzla_bv_compare(res, bve));
    }
    else
    {
      res = 0;
      do
      {
        if (res) bzla_bv_free(mm, res);
        res = bzla_bv_new_random(mm, &bzla->rng, bzla_bv_get_width(bve));
      } while (!bzla_bv_compare(res, bve));
    }
  }
  else
  {
    /* res = bveq ----------------------------------------------------------- */
    res = bzla_bv_copy(mm, bve);
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_eq, eq, bve, bveq, res, eidx, "=");
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
inv_ult_bv(Bzla *bzla,
           BzlaNode *ult,
           BzlaBitVector *bvult,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(ult);
  assert(bzla_node_is_regular(ult));
  assert(bvult);
  assert(bzla_bv_get_width(bvult) == 1);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BzlaNode *e;
  BzlaBitVector *res, *zero, *one, *bvmax, *tmp;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_ult++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = ult->e[eidx ? 0 : 1];
  assert(e);

  bw    = bzla_bv_get_width(bve);
  zero  = bzla_bv_new(mm, bw);
  one   = bzla_bv_one(mm, bw);
  bvmax = bzla_bv_ones(mm, bw);
  isult = !bzla_bv_is_zero(bvult);

  res = 0;

  if (eidx)
  {
    if (!bzla_bv_compare(bve, bvmax) && isult)
    {
    BVULT_CONF:
      /* CONFLICT: 1...1 < e[1] --------------------------------------------- */
      res = res_rec_conf(bzla, ult, e, bvult, bve, eidx, cons_ult_bv, "<");
#ifndef NDEBUG
      is_inv = false;
#endif
    }
    else
    {
      if (!isult)
      {
        /* bve >= e[1] ------------------------------------------------------ */
        res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, bve);
      }
      else
      {
        /* bve < e[1] ------------------------------------------------------- */
        tmp = bzla_bv_add(mm, bve, one);
        res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
        bzla_bv_free(mm, tmp);
      }
    }
  }
  else
  {
    if (bzla_bv_is_zero(bve) && isult)
    {
      /* CONFLICT: e[0] < 0 ------------------------------------------------- */
      goto BVULT_CONF;
    }
    else
    {
      if (!isult)
      {
        /* e[0] >= bve ------------------------------------------------------ */
        res = bzla_bv_new_random_range(mm, &bzla->rng, bw, bve, bvmax);
      }
      else
      {
        /* e[0] < bve ------------------------------------------------------- */
        tmp = bzla_bv_sub(mm, bve, one);
        res = bzla_bv_new_random_range(mm, &bzla->rng, bw, zero, tmp);
        bzla_bv_free(mm, tmp);
      }
    }
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(bzla, bzla_bv_ult, ult, bve, bvult, res, eidx, "<");
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
inv_sll_bv(Bzla *bzla,
           BzlaNode *sll,
           BzlaBitVector *bvsll,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(sll);
  assert(bzla_node_is_regular(sll));
  assert(bvsll);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvsll));
  assert(!bzla_node_is_bv_const(sll->e[eidx]));

  uint32_t i, j, ctz_bve, ctz_bvsll, shift, bw;
  BzlaNode *e;
  BzlaBitVector *res, *tmp, *bvmax;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_sll++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = sll->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(bvsll);

  res       = 0;
  bw        = bzla_bv_get_width(bvsll);
  ctz_bvsll = bzla_bv_get_num_trailing_zeros(bvsll);

  /* ------------------------------------------------------------------------
   * bve << e[1] = bvsll
   *
   * -> identify possible shift value via zero LSB in bvsll
   *    (considering zero LSB in bve)
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (bzla_bv_is_zero(bve) && bzla_bv_is_zero(bvsll))
    {
      /* 0...0 << e[1] = 0...0 -> choose res randomly ----------------------- */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /* -> ctz(bve) > ctz (bvsll) -> conflict
       * -> shift = ctz(bvsll) - ctz(bve)
       *      -> if bvsll = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       * -> else conflict
       * -------------------------------------------------------------------- */
      ctz_bve = bzla_bv_get_num_trailing_zeros(bve);
      if (ctz_bve <= ctz_bvsll)
      {
        shift = ctz_bvsll - ctz_bve;

        if (bzla_bv_is_zero(bvsll))
        {
          /* x...x0 << e[1] = 0...0
           * -> choose random shift <= res < 2^bw
           * ---------------------------------------------------------------- */
          bvmax = bzla_bv_ones(mm, bw);
          tmp   = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
          res   = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
          bzla_bv_free(mm, bvmax);
          bzla_bv_free(mm, tmp);
        }
        else
        {
          for (i = 0, j = shift, res = 0; i < bw - j; i++)
          {
            /* CONFLICT: shifted bits must match ---------------------------- */
            if (bzla_bv_get_bit(bve, i) != bzla_bv_get_bit(bvsll, j + i))
              goto BVSLL_CONF;
          }

          res = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        }
      }
      else
      {
      BVSLL_CONF:
        res = res_rec_conf(bzla, sll, e, bvsll, bve, eidx, cons_sll_bv, "<<");
#ifndef NDEBUG
        is_inv = false;
#endif
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] << bve = bvsll
   *
   * -> e[0] = bvsll >> bve
   *    set irrelevant MSBs (the ones that get shifted out) randomly
   * ------------------------------------------------------------------------ */
  else
  {
    /* actual value is small enough to fit into 32 bit (max bit width handled
     * by Bitwuzla is INT32_MAX) */
    if (bw > 64)
    {
      tmp   = bzla_bv_slice(mm, bve, 32, 0);
      shift = bzla_bv_to_uint64(tmp);
      bzla_bv_free(mm, tmp);
    }
    else
    {
      shift = bzla_bv_to_uint64(bve);
    }

    if ((shift < bw && ctz_bvsll < shift) || (shift >= bw && ctz_bvsll != bw))
    {
      /* CONFLICT: the LSBs shifted must be zero ---------------------------- */
      goto BVSLL_CONF;
    }

    res = bzla_bv_srl(mm, bvsll, bve);
    for (i = 0; i < shift && i < bw; i++)
    {
      bzla_bv_set_bit(res,
                      bzla_bv_get_width(res) - 1 - i,
                      bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
  }
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(
        bzla, bzla_bv_sll, sll, bve, bvsll, res, eidx, "<<");
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
inv_srl_bv(Bzla *bzla,
           BzlaNode *srl,
           BzlaBitVector *bvsrl,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(srl);
  assert(bzla_node_is_regular(srl));
  assert(bvsrl);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvsrl));
  assert(!bzla_node_is_bv_const(srl->e[eidx]));

  uint32_t i, j, clz_bve, clz_bvsrl, shift, bw;
  BzlaNode *e;
  BzlaBitVector *res, *bvmax, *tmp;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_srl++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = srl->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(bvsrl);

  res       = 0;
  bw        = bzla_bv_get_width(bvsrl);
  clz_bvsrl = bzla_bv_get_num_leading_zeros(bvsrl);

  /* ------------------------------------------------------------------------
   * bve >> e[1] = bvsll
   *
   * -> identify possible shift value via zero MSBs in bvsll
   *    (considering zero MSBs in bve)
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (bzla_bv_is_zero(bve) && bzla_bv_is_zero(bvsrl))
    {
      /* 0...0 >> e[1] = 0...0 -> choose random res ------------------------- */
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
      /* clz(bve) > clz(bvsrl) -> conflict
       *
       * -> shift = clz(bvsrl) - clz(bve)
       *      -> if bvsrl = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       * -> else conflict
       * -------------------------------------------------------------------- */
      clz_bve = bzla_bv_get_num_leading_zeros(bve);
      if (clz_bve <= clz_bvsrl)
      {
        shift = clz_bvsrl - clz_bve;

        if (bzla_bv_is_zero(bvsrl))
        {
          /* x...x0 >> e[1] = 0...0
           * -> choose random shift <= res < 2^bw
           * ---------------------------------------------------------------- */
          bvmax = bzla_bv_ones(mm, bw);
          tmp   = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
          res   = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
          bzla_bv_free(mm, bvmax);
          bzla_bv_free(mm, tmp);
        }
        else
        {
          for (i = 0, j = shift, res = 0; i < bw - j; i++)
          {
            if (bzla_bv_get_bit(bve, bw - 1 - i)
                != bzla_bv_get_bit(bvsrl, bw - 1 - (j + i)))
            {
              /* CONFLICT: shifted bits must match -------------------------- */
              goto BVSRL_CONF;
            }
          }

          res = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        }
      }
      else
      {
      BVSRL_CONF:
        res = res_rec_conf(bzla, srl, e, bvsrl, bve, eidx, cons_srl_bv, ">>");
#ifndef NDEBUG
        is_inv = false;
#endif
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] >> bve = bvsll
   *
   * -> e[0] = bvsll << bve
   *    set irrelevant LSBs (the ones that get shifted out) randomly
   * ------------------------------------------------------------------------ */
  else
  {
    /* actual value is small enough to fit into 32 bit (max bit width handled
     * by Bitwuzla is INT32_MAX) */
    if (bw > 64)
    {
      tmp   = bzla_bv_slice(mm, bve, 32, 0);
      shift = bzla_bv_to_uint64(tmp);
      bzla_bv_free(mm, tmp);
    }
    else
    {
      shift = bzla_bv_to_uint64(bve);
    }

    if ((shift < bw && clz_bvsrl < shift) || (shift >= bw && clz_bvsrl != bw))
    {
      /* CONFLICT: the MSBs shifted must be zero ---------------------------- */
      goto BVSRL_CONF;
    }

    res = bzla_bv_sll(mm, bvsrl, bve);
    for (i = 0; i < shift && i < bw; i++)
    {
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
    }
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(
        bzla, bzla_bv_srl, srl, bve, bvsrl, res, eidx, ">>");
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
inv_mul_bv(Bzla *bzla,
           BzlaNode *mul,
           BzlaBitVector *bvmul,
           BzlaBitVector *bve,
           int32_t eidx)
{
  assert(bzla);
  assert(mul);
  assert(bzla_node_is_regular(mul));
  assert(bvmul);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvmul));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(mul->e[eidx]));

  int32_t lsbve, lsbvmul, ispow2_bve;
  uint32_t i, j, bw;
  BzlaBitVector *res, *inv, *tmp, *tmp2;
  BzlaMemMgr *mm;
  BzlaNode *e;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_mul++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = mul->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(bvmul);

  res = 0;

  /* ------------------------------------------------------------------------
   * bve * res = bvmul
   *
   * -> if bve = 0: * bvmul = 0 -> choose random value for res
   *                * bvmul > 0 -> conflict
   *
   * -> if bvmul odd and bve even -> conflict
   *
   * -> if bve odd -> determine res via modular inverse (extended euklid)
   *                  (unique solution)
   *
   * -> else if bve is even (non-unique, multiple solutions possible!)
   *      * bve = 2^n: + if number of 0-LSBs in bvmul < n -> conflict
   *                   + else res = bvmul >> n
   *                     (with all bits shifted in randomly set to 0 or 1)
   *      * else: bve = 2^n * m, m is odd
   *              + if number of 0-LSBs in bvmul < n -> conflict
   *              + else c' = bvmul >> n
   *                (with all bits shifted in randomly set to 0 or 1)
   *                -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
   * ------------------------------------------------------------------------ */

  lsbve   = bzla_bv_get_bit(bve, 0);
  lsbvmul = bzla_bv_get_bit(bvmul, 0);

  if (bzla_bv_is_zero(bve))
  {
    /* bve = 0 -> if bvmul = 0 choose random value, else conflict ----------- */
    if (bzla_bv_is_zero(bvmul))
    {
      res = bzla_bv_new_random(mm, &bzla->rng, bw);
    }
    else
    {
    BVMUL_CONF:
      /* CONFLICT: bve = 0 but bvmul != 0 ----------------------------------- */
      res = res_rec_conf(bzla, mul, e, bvmul, bve, eidx, cons_mul_bv, "*");
#ifndef NDEBUG
      is_inv = false;
#endif
    }
  }
  else if (lsbvmul && !lsbve)
  {
    /* CONFLICT: bvmul odd and bve is even ---------------------------------- */
    goto BVMUL_CONF;
  }
  else
  {
    /* ----------------------------------------------------------------------
     * bve odd
     *
     * -> determine res via modular inverse (extended euklid)
     *    (unique solution)
     * ---------------------------------------------------------------------- */
    if (lsbve)
    {
      inv = bzla_bv_mod_inverse(mm, bve);
      res = bzla_bv_mul(mm, inv, bvmul);
      bzla_bv_free(mm, inv);
    }
    /* ----------------------------------------------------------------------
     * bve even
     * (non-unique, multiple solutions possible!)
     *
     * if bve = 2^n: + if number of 0-LSBs in bvmul < n -> conflict
     *               + else res = bvmul >> n
     *                      (with all bits shifted in set randomly)
     * else: bve = 2^n * m, m is odd
     *       + if number of 0-LSBs in bvmul < n -> conflict
     *       + else c' = bvmul >> n (with all bits shifted in set randomly)
     *         res = c' * m^-1 (with m^-1 the mod inverse of m)
     * ---------------------------------------------------------------------- */
    else
    {
      if ((ispow2_bve = bzla_bv_power_of_two(bve)) >= 0)
      {
        for (i = 0; i < bw; i++)
          if (bzla_bv_get_bit(bvmul, i)) break;
        if (i < (uint32_t) ispow2_bve)
        {
          /* CONFLICT: number of 0-LSBs in bvmul < n (for bve = 2^n) -------- */
          goto BVMUL_CONF;
        }
        else
        {
          /* res = bvmul >> n with all bits shifted in set randomly
           * (note: bw is not necessarily power of 2 -> do not use srl)
           * ---------------------------------------------------------------- */
          tmp = bzla_bv_slice(mm, bvmul, bw - 1, ispow2_bve);
          res = bzla_bv_uext(mm, tmp, ispow2_bve);
          assert(bzla_bv_get_width(res) == bw);
          for (i = 0; i < (uint32_t) ispow2_bve; i++)
            bzla_bv_set_bit(
                res, bw - 1 - i, bzla_rng_pick_rand(&bzla->rng, 0, 1));
          bzla_bv_free(mm, tmp);
        }
      }
      else
      {
        for (i = 0; i < bw; i++)
          if (bzla_bv_get_bit(bvmul, i)) break;
        for (j = 0; j < bw; j++)
          if (bzla_bv_get_bit(bve, j)) break;
        if (i < j)
        {
          /* CONFLICT: number of 0-LSB in bvmul < number of 0-LSB in bve ---- */
          goto BVMUL_CONF;
        }
        else
        {
          /* c' = bvmul >> n (with all bits shifted in set randomly)
           * (note: bw is not necessarily power of 2 -> do not use srl)
           * -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
           * ---------------------------------------------------------------- */
          tmp = bzla_bv_slice(mm, bvmul, bw - 1, j);
          res = bzla_bv_uext(mm, tmp, j);
          assert(bzla_bv_get_width(res) == bw);
          bzla_bv_free(mm, tmp);

          tmp  = bzla_bv_slice(mm, bve, bw - 1, j);
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
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(bzla, bzla_bv_mul, mul, bve, bvmul, res, eidx, "*");
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
            BzlaBitVector *bvudiv,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(udiv);
  assert(bzla_node_is_regular(udiv));
  assert(bvudiv);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvudiv));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(udiv->e[eidx]));

  uint32_t bw;
  BzlaNode *e;
  BzlaBitVector *res, *lo, *up, *one, *bvmax, *tmp;
  BzlaMemMgr *mm;
  BzlaRNG *rng;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_udiv++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm  = bzla->mm;
  rng = &bzla->rng;
  e   = udiv->e[eidx ? 0 : 1];
  assert(e);
  bw = bzla_bv_get_width(bve);

  one   = bzla_bv_one(mm, bw);
  bvmax = bzla_bv_ones(mm, bw); /* 2^bw - 1 */

  res = 0;

  /* ------------------------------------------------------------------------
   * bve / e[1] = bvudiv
   *
   * -> if bvudiv = 2^bw - 1: + bve = bvudiv = 2^bw - 1 -> e[1] = 1 or e[1] = 0
   *                          + bve != bvudiv -> e[1] = 0
   * -> if bvudiv = 0 and 0 < bve < 2^bw - 1 choose random e[1] > bve
   *                  and bve = 0            choose random e[1] > 0
   *                  else conflict
   * -> if bve < bvudiv -> conflict
   * -> if bvudiv is a divisor of bve choose with 0.5 prob out of
   *      + e[1] = bvudiv / bve
   *      + choose bve s.t. bve / e[1] = bvudiv
   * -> else choose bve s.t. bve / e[1] = bvudiv
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (!bzla_bv_compare(bvudiv, bvmax))
    {
      if (!bzla_bv_compare(bve, bvudiv)
          && bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
        /* bve = bvudiv = 2^bw - 1 -> choose either e[1] = 0 or e[1] = 1
         * with prob 0.5
         * ------------------------------------------------------------------ */
        res = bzla_bv_one(mm, bw);
      }
      else
      {
        /* bvudiv = 2^bw - 1 and bve != bvudiv -> e[1] = 0 ------------------ */
        res = bzla_bv_new(mm, bw);
      }
    }
    else if (bzla_bv_is_zero(bvudiv))
    {
      if (bzla_bv_is_zero(bve))
      {
        /* bvudiv = 0 and bve = 0 -> choose random e[1] > 0 ----------------- */
        res = bzla_bv_new_random_range(mm, rng, bw, one, bvmax);
      }
      else if (bzla_bv_compare(bve, bvmax))
      {
        /* bvudiv = 0 and 0 < bve < 2^bw - 1 -> choose random e[1] > bve ---- */
        tmp = bzla_bv_inc(mm, bve);
        res = bzla_bv_new_random_range(mm, rng, bw, tmp, bvmax);
        bzla_bv_free(mm, tmp);
      }
      else
      {
      BVUDIV_CONF:
        /* CONFLICT --------------------------------------------------------- */
        res = res_rec_conf(bzla, udiv, e, bvudiv, bve, eidx, cons_udiv_bv, "/");
#ifndef NDEBUG
        is_inv = false;
#endif
      }
    }
    else if (bzla_bv_compare(bve, bvudiv) < 0)
    {
      /* CONFLICT: bve < bvudiv --------------------------------------------- */
      goto BVUDIV_CONF;
    }
    else
    {
      /* if bvudiv is a divisor of bve, choose e[1] = bve / bvudiv
       * with prob = 0.5 and a bve s.t. bve / e[1] = bvudiv otherwise
       * -------------------------------------------------------------------- */
      tmp = bzla_bv_urem(mm, bve, bvudiv);
      if (bzla_bv_is_zero(tmp) && bzla_rng_pick_with_prob(rng, 500))
      {
        bzla_bv_free(mm, tmp);
        res = bzla_bv_udiv(mm, bve, bvudiv);
      }
      else
      {
        /* choose e[1] out of all options that yield bve / e[1] = bvudiv
         * Note: udiv always truncates the results towards 0.
         * ------------------------------------------------------------------ */

        /* determine upper and lower bounds for e[1]:
         * up = bve / bvudiv
         * lo = bve / (bvudiv + 1) + 1
         * if lo > up -> conflict */
        bzla_bv_free(mm, tmp);
        up  = bzla_bv_udiv(mm, bve, bvudiv); /* upper bound */
        tmp = bzla_bv_inc(mm, bvudiv);
        lo  = bzla_bv_udiv(mm, bve, tmp); /* lower bound (excl.) */
        bzla_bv_free(mm, tmp);
        tmp = lo;
        lo  = bzla_bv_inc(mm, tmp); /* lower bound (incl.) */
        bzla_bv_free(mm, tmp);

        if (bzla_bv_compare(lo, up) > 0)
        {
          /* CONFLICT: lo > up ---------------------------------------------- */
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, up);
          goto BVUDIV_CONF;
        }
        else
        {
          /* choose lo <= e[1] <= up ---------------------------------------- */
          res = bzla_bv_new_random_range(mm, rng, bw, lo, up);
          bzla_bv_free(mm, lo);
          bzla_bv_free(mm, up);
        }
      }
    }
  }

  /* ------------------------------------------------------------------------
   * e[0] / bve = bvudiv
   *
   * -> if bvudiv = 2^bw - 1 and bve = 1 e[0] = 2^bw-1
   *                         and bve = 0, choose random e[0] > 0
   *                         and bve > 0 -> conflict
   * -> if bve = 0 and bvudiv < 2^bw - 1 -> conflict
   * -> if bve * bvudiv does not overflow, choose with 0.5 prob out of
   *      + e[0] = bve * bvudiv
   *      + choose bve s.t. e[0] / bve = bvudiv
   * -> else choose bve s.t. e[0] / bve = bvudiv
   * ------------------------------------------------------------------------ */
  else
  {
    if (!bzla_bv_compare(bvudiv, bvmax))
    {
      if (!bzla_bv_compare(bve, one))
      {
        /* bvudiv = 2^bw-1 and bve = 1 -> e[0] = 2^bw-1 --------------------- */
        res = bzla_bv_copy(mm, bvmax);
      }
      else if (bzla_bv_is_zero(bve))
      {
        /* bvudiv = 2^bw - 1 and bve = 0 -> choose random e[0] -------------- */
        res = bzla_bv_new_random(mm, rng, bw);
      }
      else
      {
        /* CONFLICT --------------------------------------------------------- */
        goto BVUDIV_CONF;
      }
    }
    else if (bzla_bv_is_zero(bve))
    {
      /* CONFLICT: bve = 0 and bvudiv < 2^bw - 1 ---------------------------- */
      goto BVUDIV_CONF;
    }
    else
    {
      /* if bve * bvudiv does not overflow, choose e[0] = bve * bvudiv
       * with prob = 0.5 and a bve s.t. e[0] / bve = bvudiv otherwise */

      if (bzla_bv_is_umulo(mm, bve, bvudiv))
      {
        /* CONFLICT: overflow: bve * bvudiv --------------------------------- */
        goto BVUDIV_CONF;
      }
      else
      {
        if (bzla_rng_pick_with_prob(rng, 500))
          res = bzla_bv_mul(mm, bve, bvudiv);
        else
        {
          /* choose e[0] out of all options that yield
           * e[0] / bve = bvudiv
           * Note: udiv always truncates the results towards 0.
           * ---------------------------------------------------------------- */

          /* determine upper and lower bounds for e[0]:
           * up = bve * (budiv + 1) - 1
           *      if bve * (bvudiv + 1) does not overflow
           *      else 2^bw - 1
           * lo = bve * bvudiv */
          lo  = bzla_bv_mul(mm, bve, bvudiv);
          tmp = bzla_bv_inc(mm, bvudiv);
          if (bzla_bv_is_umulo(mm, bve, tmp))
          {
            bzla_bv_free(mm, tmp);
            up = bzla_bv_copy(mm, bvmax);
          }
          else
          {
            up = bzla_bv_mul(mm, bve, tmp);
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_dec(mm, up);
            bzla_bv_free(mm, up);
            up = tmp;
          }

          res = bzla_bv_new_random_range(mm, &bzla->rng, bw, lo, up);

          bzla_bv_free(mm, up);
          bzla_bv_free(mm, lo);
        }
      }
    }
  }

  bzla_bv_free(mm, bvmax);
  bzla_bv_free(mm, one);
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(
        bzla, bzla_bv_udiv, udiv, bve, bvudiv, res, eidx, "/");
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
            BzlaBitVector *bvurem,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(urem);
  assert(bzla_node_is_regular(urem));
  assert(bvurem);
  assert(bve);
  assert(bzla_bv_get_width(bve) == bzla_bv_get_width(bvurem));
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(urem->e[eidx]));

  uint32_t bw, cnt;
  int32_t cmp;
  BzlaNode *e;
  BzlaBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_urem++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = urem->e[eidx ? 0 : 1];
  assert(e);

  bw = bzla_bv_get_width(bvurem);

  bvmax = bzla_bv_ones(mm, bw); /* 2^bw - 1 */
  one   = bzla_bv_one(mm, bw);

  res = 0;

  /* -----------------------------------------------------------------------
   * bve % e[1] = bvurem
   *
   * -> if bvurem = 1...1 -> bve = 1...1 and e[1] = 0...0, else conflict
   * -> if bve = bvurem, choose either e[1] = 0 or some e[1] > bvurem randomly
   * -> if bvurem > 0 and bvurem = bve - 1, conflict
   * -> if bve > bvurem, e[1] = ((bve - bvurem) / n) > bvurem, else conflict
   * -> if bve < bvurem, conflict
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (!bzla_bv_compare(bvurem, bvmax))
    {
      /* CONFLICT: bvurem = 1...1 but bve != 1...1 -------------------------- */
      if (bzla_bv_compare(bve, bvmax))
      {
      BVUREM_CONF:
        res = res_rec_conf(bzla, urem, e, bvurem, bve, eidx, cons_urem_bv, "%");
#ifndef NDEBUG
        is_inv = false;
#endif
      }
      else
      {
        /* bve % e[1] = 1...1 -> bve = 1...1, e[1] = 0 ---------------------- */
        res = bzla_bv_new(mm, bw);
      }
    }
    else
    {
      cmp = bzla_bv_compare(bve, bvurem);

      if (cmp == 0)
      {
        /* bve = bvurem, choose either e[1] = 0 or random e[1] > bvurem ----- */

        /* choose e[1] = 0 with prob = 0.25*/
        if (bzla_rng_pick_with_prob(&bzla->rng, 250)) res = bzla_bv_new(mm, bw);
        /* bvurem < res <= 2^bw - 1 */
        else
        {
          tmp = bzla_bv_add(mm, bvurem, one);
          res = bzla_bv_new_random_range(mm, &bzla->rng, bw, tmp, bvmax);
          bzla_bv_free(mm, tmp);
        }
      }
      else if (cmp > 0)
      {
        /* bve > bvurem, e[1] = (bve - bvurem) / n -------------------------- */
        if (!bzla_bv_is_zero(bvurem))
        {
          tmp = bzla_bv_dec(mm, bve);
          if (!bzla_bv_compare(bvurem, tmp))
          {
            /* CONFLICT:
             * bvurem = bve - 1 -> bve % e[1] = bve - 1
             * -> not possible if bvurem > 0
             * -------------------------------------------------------------- */
            bzla_bv_free(mm, tmp);
            goto BVUREM_CONF;
          }
          bzla_bv_free(mm, tmp);
        }

        sub = bzla_bv_sub(mm, bve, bvurem);

        if (bzla_bv_compare(sub, bvurem) <= 0)
        {
          /* CONFLICT: bve - bvurem <= bvurem ------------------------------- */
          bzla_bv_free(mm, sub);
          goto BVUREM_CONF;
        }
        else
        {
          /* choose either n = 1 or 1 <= n < (bve - bvurem) / bvurem
           * with prob = 0.5
           * ---------------------------------------------------------------- */

          if (bzla_rng_pick_with_prob(&bzla->rng, 500))
          {
            res = bzla_bv_copy(mm, sub);
          }
          else
          {
            /* 1 <= n < (bve - bvurem) / bvurem (non-truncating)
             * (note: div truncates towards 0!)
             * -------------------------------------------------------------- */

            if (bzla_bv_is_zero(bvurem))
            {
              /* bvurem = 0 -> 1 <= n <= bve -------------------------------- */
              up = bzla_bv_copy(mm, bve);
            }
            else
            {
              /* e[1] > bvurem
               * -> (bve - bvurem) / n > bvurem
               * -> (bve - bvurem) / bvurem > n
               * ------------------------------------------------------------ */
              tmp  = bzla_bv_urem(mm, sub, bvurem);
              tmp2 = bzla_bv_udiv(mm, sub, bvurem);
              if (bzla_bv_is_zero(tmp))
              {
                /* (bve - bvurem) / bvurem is not truncated
                 * (remainder is 0), therefore the EXclusive
                 * upper bound
                 * -> up = (bve - bvurem) / bvurem - 1
                 * ---------------------------------------------------------- */
                up = bzla_bv_sub(mm, tmp2, one);
                bzla_bv_free(mm, tmp2);
              }
              else
              {
                /* (bve - bvurem) / bvurem is truncated
                 * (remainder is not 0), therefore the INclusive
                 * upper bound
                 * -> up = (bve - bvurem) / bvurem
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
               * s.t (bve - bvurem) % n = 0
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
                /* res = (bve - bvurem) / n */
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
        }
        bzla_bv_free(mm, sub);
      }
      else
      {
        /* CONFLICT: bve < bvurem ------------------------------------------- */
        goto BVUREM_CONF;
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] % bve = bvurem
   *
   * -> if bve = 0, e[0] = bvurem
   * -> if bvurem = 1...1 and bve != 0, conflict
   * -> if bve <= bvurem, conflict
   * -> if bvurem > 0 and bve = 1, conflict
   * -> else choose either
   *      - e[0] = bvurem, or
   *      - e[0] = bve * n + b, with n s.t. (bve * n + b) does not overflow
   * ------------------------------------------------------------------------ */
  else
  {
    if (bzla_bv_is_zero(bve))
    {
    BVUREM_ZERO_0:
      /* bve = 0 -> e[0] = bvurem ------------------------------------------- */
      res = bzla_bv_copy(mm, bvurem);
    }
    else if (!bzla_bv_is_zero(bvurem) && bzla_bv_is_one(bve))
    {
      /* CONFLICT: bvurem > 0 and bve = 1 ----------------------------------- */
      goto BVUREM_CONF;
    }
    else if (!bzla_bv_compare(bvurem, bvmax))
    {
      if (!bzla_bv_is_zero(bve))
      {
        /* CONFLICT: bve != 0 ----------------------------------------------- */
        goto BVUREM_CONF;
      }
      else
      {
        /* bvurem = 1...1 -> bve = 0, e[0] = 1...1 -------------------------- */
        goto BVUREM_ZERO_0;
      }
    }
    else if (bzla_bv_compare(bve, bvurem) > 0)
    {
      if (bzla_rng_pick_with_prob(&bzla->rng, 500))
      {
      BVUREM_EQ_0:
        /* choose simplest solution (0 <= res < bve -> res = bvurem)
         * with prob 0.5
         * ------------------------------------------------------------------ */
        res = bzla_bv_copy(mm, bvurem);
      }
      else
      {
        /* e[0] = bve * n + bvurem,
         * with n s.t. (bve * n + bvurem) does not overflow
         * ------------------------------------------------------------------ */
        tmp2 = bzla_bv_sub(mm, bvmax, bve);

        /* overflow for n = 1 -> only simplest solution possible */
        if (bzla_bv_compare(tmp2, bvurem) < 0)
        {
          bzla_bv_free(mm, tmp2);
          goto BVUREM_EQ_0;
        }
        else
        {
          bzla_bv_free(mm, tmp2);

          tmp = bzla_bv_copy(mm, bvmax);
          n   = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);

          while (bzla_bv_is_umulo(mm, bve, n))
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_sub(mm, n, one);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
          }

          mul  = bzla_bv_mul(mm, bve, n);
          tmp2 = bzla_bv_sub(mm, bvmax, mul);

          if (bzla_bv_compare(tmp2, bvurem) < 0)
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_sub(mm, n, one);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, &bzla->rng, bw, one, tmp);
            bzla_bv_free(mm, mul);
            mul = bzla_bv_mul(mm, bve, n);
          }

          res = bzla_bv_add(mm, mul, bvurem);
          assert(bzla_bv_compare(res, mul) >= 0);
          assert(bzla_bv_compare(res, bvurem) >= 0);

          bzla_bv_free(mm, tmp);
          bzla_bv_free(mm, tmp2);
          bzla_bv_free(mm, mul);
          bzla_bv_free(mm, n);
        }
      }
    }
    else
    {
      /* CONFLICT: bve <= bvurem -------------------------------------------- */
      goto BVUREM_CONF;
    }
  }

  bzla_bv_free(mm, one);
  bzla_bv_free(mm, bvmax);

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(
        bzla, bzla_bv_urem, urem, bve, bvurem, res, eidx, "%");
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
              BzlaBitVector *bvconcat,
              BzlaBitVector *bve,
              int32_t eidx)
{
  assert(bzla);
  assert(concat);
  assert(bzla_node_is_regular(concat));
  assert(bvconcat);
  assert(bve);
  assert(eidx >= 0 && eidx <= 1);
  assert(!bzla_node_is_bv_const(concat->e[eidx]));

  uint32_t bw_t, bw_s;
  BzlaNode *e;
  BzlaBitVector *res, *tmp;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_concat++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  mm = bzla->mm;
  e  = concat->e[eidx ? 0 : 1];
  assert(e);
  bw_t = bzla_bv_get_width(bvconcat);
  bw_s = bzla_bv_get_width(bve);

  res = 0;

  /* ------------------------------------------------------------------------
   * bve o e[1] = bvconcat
   *
   * -> slice e[1] out of the lower bits of bvconcat
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    tmp = bzla_bv_slice(mm, bvconcat, bw_t - 1, bw_t - bw_s);
    if (bzla_bv_compare(tmp, bve))
    {
    BVCONCAT_CONF:
      /* CONFLICT: bve bits do not match bvconcat --------------------------- */
      res = res_rec_conf(
          bzla, concat, e, bvconcat, bve, eidx, cons_concat_bv, "o");
#ifndef NDEBUG
      is_inv = false;
#endif
    }
    else
    {
      res = bzla_bv_slice(mm, bvconcat, bw_t - bw_s - 1, 0);
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] o bve = bvconcat
   *
   * -> slice e[0] out of the upper bits of bvconcat
   * ------------------------------------------------------------------------ */
  else
  {
    tmp = bzla_bv_slice(mm, bvconcat, bw_s - 1, 0);
    if (bzla_bv_compare(tmp, bve))
    {
      /* CONFLICT: bve bits do not match bvconcat --------------------------- */
      goto BVCONCAT_CONF;
    }
    else
    {
      res = bzla_bv_slice(mm, bvconcat, bw_t - 1, bw_s);
    }
  }
  bzla_bv_free(mm, tmp);
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg(
        bzla, bzla_bv_concat, concat, bve, bvconcat, res, eidx, "o");
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
             BzlaBitVector *bvslice,
             BzlaBitVector *bve,
             int32_t eidx)
{
  assert(bzla);
  assert(slice);
  assert(bzla_node_is_regular(slice));
  assert(bvslice);
  assert(!bzla_node_is_bv_const(slice->e[0]));
  (void) eidx;

  uint32_t i, upper, lower, rlower, rupper, rboth, bw_x;
  BzlaNode *e;
  BzlaBitVector *res;
  BzlaMemMgr *mm;
  bool bkeep, bflip;

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
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
        bkeep ? bzla_bv_get_bit(bve, i) : bzla_rng_pick_rand(&bzla->rng, 0, 1));

  /* set sliced bits to propagated value */
  for (i = lower; i <= upper; i++)
    bzla_bv_set_bit(res, i, bzla_bv_get_bit(bvslice, i - lower));

  /* keep previous value for don't care bits or set randomly with prob
   * BZLA_OPT_PROP_PROB_SLICE_KEEP_DC */
  bw_x = bzla_bv_get_width(res);
  for (i = upper + 1; i < bw_x; i++)
    bzla_bv_set_bit(
        res,
        i,
        bkeep ? bzla_bv_get_bit(bve, i) : bzla_rng_pick_rand(&bzla->rng, 0, 1));

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
  assert(!bzla_bv_compare(tmpdbg, bvslice));
  bzla_bv_free(mm, tmpdbg);

  char *sbvslice = bzla_bv_to_char(mm, bvslice);
  char *sres     = bzla_bv_to_char(mm, res);
  BZLALOG(3,
          "prop (xxxxx): %s: %s := %s[%d:%d]",
          bzla_util_node2string(slice),
          sbvslice,
          sres,
          lower,
          upper);
  bzla_mem_freestr(mm, sbvslice);
  bzla_mem_freestr(mm, sres);
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
            BzlaBitVector *bvcond,
            BzlaBitVector *bve,
            int32_t eidx)
{
  assert(bzla);
  assert(cond);
  assert(bzla_node_is_regular(cond));
  assert(bvcond);
  assert(!bzla_bv_compare(bve, bzla_model_get_bv(bzla, cond->e[0])));
  assert(eidx || !bzla_node_is_bv_const(cond->e[eidx]));

  BzlaBitVector *res, *bve1, *bve2;
  BzlaMemMgr *mm = bzla->mm;

  bve1 = (BzlaBitVector *) bzla_model_get_bv(bzla, cond->e[1]);
  bve2 = (BzlaBitVector *) bzla_model_get_bv(bzla, cond->e[2]);
#ifndef NDEBUG
  char *sbvcond = bzla_bv_to_char(bzla->mm, bvcond);
  char *sbve0   = bzla_bv_to_char(mm, bve);
  char *sbve1   = bzla_bv_to_char(mm, bve1);
  char *sbve2   = bzla_bv_to_char(mm, bve2);
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
  {
#ifndef NDEBUG
    BZLA_PROP_SOLVER(bzla)->stats.inv_cond++;
#endif
    BZLA_PROP_SOLVER(bzla)->stats.props_inv += 1;
  }

  /* either assume that cond is fixed and propagate bvenew
   * to enabled path, or flip condition */

  if (eidx == 0)
  {
    /* flip condition */
    res = bzla_bv_not(mm, bve);
  }
  else
  {
    /* else continue propagating current target value down */
    res = bzla_bv_copy(mm, bvcond);
    if (bzla_node_is_bv_const(cond->e[eidx]))
    {
      bool is_recoverable = !bzla_bv_compare(bvcond, eidx == 1 ? bve2 : bve1);
#ifndef NDEBUG
      if (eidx == 2)
      {
        BZLALOG(2,
                "%s CONFLICT (@%d): %s := %s ? %s : x",
                is_recoverable ? "recoverable" : "non-recoverable",
                bzla_node_get_id(cond),
                sbvcond,
                sbve0,
                sbve1);
      }
      else
      {
        BZLALOG(2,
                "%s CONFLICT (@%d): %s := %s ? x : %s",
                is_recoverable ? "recoverable" : "non-recoverable",
                bzla_node_get_id(cond),
                sbvcond,
                sbve0,
                sbve2);
      }
      BZLALOG(2, "");
#endif
      if (bzla_opt_get(bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_PROP)
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
  char *sres = bzla_bv_to_char(mm, res);
  BZLALOG(3,
          "prop (e[%d]): %s: %s := %s ? %s : %s",
          eidx,
          bzla_util_node2string(cond),
          sbvcond,
          eidx == 0 ? sres : sbve0,
          eidx == 1 ? sres : sbve1,
          eidx == 2 ? sres : sbve2);
  bzla_mem_freestr(mm, sbvcond);
  bzla_mem_freestr(mm, sres);
  bzla_mem_freestr(mm, sbve0);
  bzla_mem_freestr(mm, sbve1);
  bzla_mem_freestr(mm, sbve2);
#endif
  return res;
}

/* ========================================================================== */
/* Propagation move                                                           */
/* ========================================================================== */

static BzlaNode *
select_move(Bzla *bzla,
            BzlaNode *exp,
            BzlaBitVector *bvexp,
            BzlaBitVector *bve[3],
            int32_t (*select_path)(
                Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector **),
            BzlaBitVector *(*compute_value)(
                Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t),
            BzlaBitVector **value)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bvexp);
  assert(bve);
  assert(select_path);
  assert(compute_value);
  assert(value);

  int32_t eidx, idx;

  eidx = select_path(bzla, exp, bvexp, bve);
  assert(eidx >= 0);
  /* special case slice: only one child
   * special case cond: we only need assignment of condition to compute value */
  idx =
      eidx ? 0 : (bzla_node_is_bv_slice(exp) || bzla_node_is_cond(exp) ? 0 : 1);
  *value = compute_value(bzla, exp, bvexp, bve[idx], eidx);
  return exp->e[eidx];
}

uint64_t
bzla_proputils_select_move_prop(Bzla *bzla,
                                BzlaNode *root,
                                BzlaNode **input,
                                BzlaBitVector **assignment)
{
  assert(bzla);
  assert(root);
  assert(bzla_bv_to_uint64((BzlaBitVector *) bzla_model_get_bv(bzla, root))
         == 0);

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
#endif

  *input      = 0;
  *assignment = 0;
  nprops      = 0;

  cur   = root;
  bvcur = bzla_bv_one(bzla->mm, 1);

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
      nprops += 1;
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

      cur = select_move(
          bzla, real_cur, bvcur, bve, select_path, compute_value, &bvenew);
      if (!bvenew) break; /* non-recoverable conflict */

      bzla_bv_free(bzla->mm, bvcur);
      bvcur = bvenew;
    }
  }

  bzla_bv_free(bzla->mm, bvcur);

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
  BzlaNode *cloned_exp;
  BzlaBitVector *cloned_bv;
  BzlaPropInfo cloned_prop;

  BZLA_INIT_STACK(mm, *res);
  assert(BZLA_SIZE_STACK(*stack) || !BZLA_COUNT_STACK(*stack));
  if (BZLA_SIZE_STACK(*stack))
  {
    BZLA_NEWN(mm, res->start, BZLA_SIZE_STACK(*stack));
    res->top = res->start;
    res->end = res->start + BZLA_SIZE_STACK(*stack);

    for (i = 0; i < BZLA_COUNT_STACK(*stack); i++)
    {
      cloned_exp = bzla_nodemap_mapped(exp_map, BZLA_PEEK_STACK(*stack, i).exp);
      assert(cloned_exp);
      cloned_prop.exp = cloned_exp;
      assert(BZLA_PEEK_STACK(*stack, i).bvexp);
      cloned_bv         = bzla_bv_copy(mm, BZLA_PEEK_STACK(*stack, i).bvexp);
      cloned_prop.bvexp = cloned_bv;
      cloned_prop.eidx  = BZLA_PEEK_STACK(*stack, i).eidx;
      assert(cloned_prop.eidx == 0 || cloned_prop.eidx == 1);
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
