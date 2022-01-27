/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaproputils.h"

#include "bzlabv.h"
#include "bzlaconsutils.h"
#include "bzlaessutils.h"
#include "bzlainvutils.h"
#include "bzlalsutils.h"
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

static BzlaBitVector *
bvdomain_random(Bzla *bzla, const BzlaBvDomain *x)
{
  BzlaMemMgr *mm;
  BzlaBvDomainGenerator gen;
  BzlaBitVector *res;

  mm = bzla->mm;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
  return res;
}

/* ========================================================================== */

bool
bzla_is_bv_sext(Bzla *bzla, BzlaNode *n)
{
  assert(bzla);
  assert(n);

  uint32_t msb;
  BzlaNode *ite, *t;

  if (bzla_node_is_inverted(n) || !bzla_node_is_bv_concat(n))
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

bool
bzla_is_bv_xor(Bzla *bzla,
               const BzlaNode *n,
               BzlaNode **res_a,
               BzlaNode **res_b)
{
  assert(bzla);
  assert(n);
  assert(res_a);
  assert(res_b);
  (void) bzla;

  const BzlaNode *e0, *e1, *a, *b;

  *res_a = 0;
  *res_b = 0;

  if (bzla_node_is_inverted(n) || !bzla_node_is_bv_and(n))
  {
    return false;
  }

  e0 = n->e[0];
  e1 = n->e[1];
  if (bzla_node_is_inverted(e0) && bzla_node_is_inverted(e1)
      && bzla_node_is_bv_and(e0) && bzla_node_is_bv_and(e1))
  {
    a = bzla_node_real_addr(e0)->e[0];
    b = bzla_node_real_addr(e0)->e[1];

    if (bzla_node_invert(a) == bzla_node_real_addr(e1)->e[0]
        && bzla_node_invert(b) == bzla_node_real_addr(e1)->e[1])
    {
      *res_a = bzla_node_real_addr(a);
      *res_b = bzla_node_real_addr(b);
      return true;
    }
  }

  return false;
}

bool
bzla_is_bv_sra(Bzla *bzla,
               const BzlaNode *n,
               BzlaNode **res_a,
               BzlaNode **res_b)
{
  assert(bzla);
  assert(n);
  assert(res_a);
  assert(res_b);
  assert(bzla_node_is_regular(n));

  uint32_t bw;
  BzlaNode *e0, *e1;

  *res_a = 0;
  *res_b = 0;

  if (!bzla_node_is_cond(n)) return false;

  if (bzla_node_is_inverted(n->e[0])) return false;
  if (!bzla_node_is_inverted(n->e[1])) return false;
  if (bzla_node_is_inverted(n->e[2])) return false;

  if (!bzla_node_is_bv_slice(n->e[0])) return false;
  if (!bzla_node_is_bv_srl(n->e[1])) return false;
  if (!bzla_node_is_bv_srl(n->e[2])) return false;

  bw = bzla_node_bv_get_width(bzla, n);

  if (bzla_node_bv_slice_get_lower(n->e[0]) != bw - 1) return false;
  if (bzla_node_bv_slice_get_upper(n->e[0]) != bw - 1) return false;

  e0 = n->e[2]->e[0];
  e1 = n->e[2]->e[1];

  if (n->e[0]->e[0] != e0) return false;

  if (bzla_node_real_addr(n->e[1])->e[0] != bzla_node_invert(e0)) return false;
  if (bzla_node_real_addr(n->e[1])->e[1] != e1) return false;

  *res_a = e0;
  *res_b = e1;
  return true;
}

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

  BzlaNode *exp, *children[2];
  char *a;
  BzlaMemMgr *mm = bzla->mm;

  exp = bzla_node_real_addr(pi->exp);

  BZLALOG(2, "");
  BZLALOG(2, "select path: %s", bzla_util_node2string(exp));

  for (size_t i = 0; i < exp->arity; i++)
  {
    a = bzla_bv_to_char(mm, pi->bv[i]);
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_ASHR)
        && bzla_is_bv_sra(bzla,
                          bzla_node_real_addr((BzlaNode *) exp->e[i]),
                          &children[0],
                          &children[1]))
    {
      BZLALOG(2,
              "       e[%zu]: %d sra %d %d (%s)",
              i,
              bzla_node_get_id(exp->e[i]),
              bzla_node_get_id(children[0]),
              bzla_node_get_id(children[1]),
              a);
    }
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_XOR)
        && bzla_is_bv_xor(bzla,
                          bzla_node_real_addr((BzlaNode *) exp->e[i]),
                          &children[0],
                          &children[1]))
    {
      BZLALOG(2,
              "       e[%zu]: %d xor %d %d (%s)",
              i,
              bzla_node_get_id(exp->e[i]),
              bzla_node_get_id(children[0]),
              bzla_node_get_id(children[1]),
              a);
    }
    else
    {
      BZLALOG(
          2, "       e[%zu]: %s (%s)", i, bzla_util_node2string(exp->e[i]), a);
    }
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

static void
select_path_log_bin_aux(
    Bzla *bzla, BzlaPropInfo *pi, BzlaNode *e0, BzlaNode *e1, char *op)
{
  assert(bzla);
  assert(pi);
  assert(e0);
  assert(e1);

  BzlaNode *exp;
  char *a;
  uint32_t arity = 2;
  BzlaMemMgr *mm = bzla->mm;

  exp = bzla_node_real_addr(pi->exp);

  BZLALOG(2, "");
  BZLALOG(2,
          "select path: %d %s %d %d",
          exp->id,
          op,
          bzla_node_get_id(e0),
          bzla_node_get_id(e1));

  for (size_t i = 0; i < arity; i++)
  {
    assert(i ? e1 : e0);
    a = bzla_bv_to_char(mm, pi->bv[i]);
    BZLALOG(
        2, "       e[%zu]: %s (%s)", i, bzla_util_node2string(i ? e1 : e0), a);
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
select_path_non_const(Bzla *bzla, const BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(exp->arity <= 3);
  assert(!bzla_node_is_bv_const(exp->e[0])
         || (exp->arity > 1
             && (!bzla_node_is_bv_const(exp->e[1])
                 || (exp->arity > 2 && !bzla_node_is_bv_const(exp->e[2])))));

  uint32_t i;
  int32_t pos_x;
  BzlaUIntStack nconst;

  pos_x = -1;
  BZLA_INIT_STACK(bzla->mm, nconst);
  for (i = 0; i < exp->arity; i++)
  {
    if (!bzla_node_is_bv_const(exp->e[i]))
    {
      BZLA_PUSH_STACK(nconst, i);
    }
  }
  assert(!BZLA_EMPTY_STACK(nconst));
  if (BZLA_COUNT_STACK(nconst) == 1)
  {
    pos_x = BZLA_PEEK_STACK(nconst, 0);
  }
  assert(exp->arity == 1 || pos_x == -1
         || !bzla_node_is_bv_const(exp->e[pos_x]));
  BZLA_RELEASE_STACK(nconst);
  return pos_x;
}

static int32_t
select_path_random(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  int32_t pos_x = (int32_t) bzla_rng_pick_rand(bzla->rng, 0, exp->arity - 1);
  assert(!bzla_node_is_bv_const(exp->e[pos_x]));
  return pos_x;
}

static BzlaPropIsEssFun kind_to_is_ess[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_is_ess_add,
    [BZLA_BV_AND_NODE]    = bzla_is_ess_and,
    [BZLA_BV_CONCAT_NODE] = bzla_is_ess_concat,
    [BZLA_BV_EQ_NODE]     = bzla_is_ess_eq,
    [BZLA_BV_MUL_NODE]    = bzla_is_ess_mul,
    [BZLA_BV_ULT_NODE]    = bzla_is_ess_ult,
    [BZLA_BV_SLICE_NODE]  = bzla_is_ess_slice,
    [BZLA_BV_SLL_NODE]    = bzla_is_ess_sll,
    [BZLA_BV_SLT_NODE]    = bzla_is_ess_slt,
    [BZLA_BV_SRL_NODE]    = bzla_is_ess_srl,
    [BZLA_BV_UDIV_NODE]   = bzla_is_ess_udiv,
    [BZLA_BV_UREM_NODE]   = bzla_is_ess_urem,
    [BZLA_COND_NODE]      = bzla_is_ess_cond,
};

static BzlaPropIsEssFun kind_to_is_ess_const[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_is_ess_add_const,
    [BZLA_BV_AND_NODE]    = bzla_is_ess_and_const,
    [BZLA_BV_CONCAT_NODE] = bzla_is_ess_concat_const,
    [BZLA_BV_EQ_NODE]     = bzla_is_ess_eq_const,
    [BZLA_BV_MUL_NODE]    = bzla_is_ess_mul_const,
    [BZLA_BV_ULT_NODE]    = bzla_is_ess_ult_const,
    [BZLA_BV_SLICE_NODE]  = bzla_is_ess_slice_const,
    [BZLA_BV_SLL_NODE]    = bzla_is_ess_sll_const,
    [BZLA_BV_SLT_NODE]    = bzla_is_ess_slt_const,
    [BZLA_BV_SRL_NODE]    = bzla_is_ess_srl_const,
    [BZLA_BV_UDIV_NODE]   = bzla_is_ess_udiv_const,
    [BZLA_BV_UREM_NODE]   = bzla_is_ess_urem_const,
    [BZLA_COND_NODE]      = bzla_is_ess_cond_const,
};

static int32_t
select_path(Bzla *bzla, BzlaPropInfo *pi, bool const_bits)
{
  assert(bzla);
  assert(pi);
  assert(bzla_node_is_regular(pi->exp));

  int32_t pos_x;
  uint32_t i;
  BzlaPropIsEssFun is_ess_fun;
  BzlaUIntStack ess;

  pos_x = select_path_non_const(bzla, pi->exp);
  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      is_ess_fun = const_bits ? kind_to_is_ess_const[pi->exp->kind]
                              : kind_to_is_ess[pi->exp->kind];
      if (is_ess_fun)
      {
        BZLA_INIT_STACK(bzla->mm, ess);
        for (i = 0; i < pi->exp->arity; i++)
        {
          if (is_ess_fun(bzla, pi, i))
          {
            BZLA_PUSH_STACK(ess, i);
          }
        }
        if (BZLA_EMPTY_STACK(ess))
        {
          pos_x = select_path_random(bzla, pi->exp);
        }
        else if (BZLA_COUNT_STACK(ess) == 1)
        {
          pos_x = BZLA_PEEK_STACK(ess, 0);
        }
        else
        {
          i     = bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(ess) - 1);
          pos_x = BZLA_PEEK_STACK(ess, i);
        }
        BZLA_RELEASE_STACK(ess);
      }
    }
    else
    {
      pos_x = select_path_random(bzla, pi->exp);
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

static int32_t
select_path_aux(Bzla *bzla,
                BzlaPropInfo *pi,
                BzlaPropIsEssFun is_ess_fun,
                BzlaNode *e0,
                BzlaNode *e1)
{
  int32_t pos_x;

  pos_x = -1;
  if (bzla_node_is_bv_const(e0))
  {
    assert(!bzla_node_is_bv_const(e1));
    pos_x = 1;
  }
  else if (bzla_node_is_bv_const(e1))
  {
    assert(!bzla_node_is_bv_const(e0));
    pos_x = 0;
  }
  if (pos_x == -1)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (is_ess_fun(bzla, pi, 0))
      {
        pos_x = 0;
      }
      if (is_ess_fun(bzla, pi, 1))
      {
        pos_x = pos_x >= 0 ? -1 : 1;
      }
      if (pos_x == -1)
      {
        pos_x = bzla_rng_pick_rand(bzla->rng, 0, 1);
      }
    }
    else
    {
      pos_x = bzla_rng_pick_rand(bzla->rng, 0, 1);
    }
  }
  assert(pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log_bin_aux(bzla, pi, e0, e1, "xor");
#endif
  assert(!bzla_node_is_bv_const(pos_x == 0 ? e0 : e1));
  return pos_x;
}

#if 0
static int32_t
select_path_add (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;

  pos_x = select_path_non_const (pi->exp);
  if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_and (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  uint32_t opt;
  int32_t i, pos_x;
  BzlaNode *exp;
  BzlaBitVector *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  exp = (BzlaNode *) pi->exp;
  s   = (BzlaBitVector **) pi->bv;
  t   = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const (exp);

  if (pos_x == -1)
  {
    opt = bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL);

    if (opt == BZLA_PROP_PATH_SEL_RANDOM)
    {
      pos_x = select_path_random (bzla, exp);
    }
    else if (bzla_node_bv_get_width (bzla, exp) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < exp->arity; i++)
      {
        if (bzla_bv_is_zero (s[i])) pos_x = pos_x == -1 ? i : -1;
      }
      if (pos_x == -1) pos_x = select_path_random (bzla, exp);
    }
    else if (opt == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* 1) all bits set in t must be set in both inputs, but
       * 2) all bits NOT set in t can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < exp->arity; i++)
      {
        tmp = bzla_bv_and (mm, t, s[i]);
        if (bzla_bv_compare (tmp, t)) pos_x = pos_x == -1 ? i : -1;
        bzla_bv_free (mm, tmp);
      }
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, exp);
  }

  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_eq (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  pos_x = select_path_non_const (pi->exp);
  if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_ult (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  BzlaBitVector *ones, *t, **s;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const (pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones = bzla_bv_ones (mm, bzla_bv_get_width (s[0]));
      if (bzla_bv_is_one (t))
      {
        /* 1...1 < s[1] */
        if (!bzla_bv_compare (s[0], ones)) pos_x = 0;
        /* s[0] < 0 */
        if (bzla_bv_is_zero (s[1])) pos_x = pos_x == -1 ? 1 : -1;
      }
      bzla_bv_free (mm, ones);
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }

  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_slt (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  BzlaBitVector *max_signed, *t, **s;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const (pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      max_signed = bzla_bv_max_signed (mm, bzla_bv_get_width (s[0]));
      if (bzla_bv_is_one (t))
      {
        /* max_signed < s[1] */
        if (!bzla_bv_compare (s[0], max_signed)) pos_x = 0;
        /* s[0] < 0 */
        if (bzla_bv_is_min_signed (s[1])) pos_x = pos_x == -1 ? 1 : -1;
      }
      bzla_bv_free (mm, max_signed);
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }

  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_sll (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp, *t, **s;
  BzlaMemMgr *mm;

  pos_x = select_path_non_const (pi->exp);

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;
  bw = bzla_bv_get_width (t);
  assert (bzla_bv_get_width (s[0]) == bw);
  assert (bzla_bv_get_width (s[1]) == bw);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (bw > 64)
      {
        bv_bw = bzla_bv_uint64_to_bv (mm, bw, bw);
        tmp   = bzla_bv_ugte (mm, s[1], bv_bw);
        if (bzla_bv_is_one (tmp) && !bzla_bv_is_zero (t))
        {
          bzla_bv_free (mm, bv_bw);
          bzla_bv_free (mm, tmp);
          pos_x = 1;
          goto DONE;
        }
        bzla_bv_free (mm, bv_bw);
        bzla_bv_free (mm, tmp);
        /* actual value is small enough to fit into 32 bit (max bit width
         * handled by Bitwuzla is INT32_MAX) */
        tmp   = bzla_bv_slice (mm, s[1], 32, 0);
        shift = bzla_bv_to_uint64 (tmp);
        bzla_bv_free (mm, tmp);
      }
      else
      {
        shift = bzla_bv_to_uint64 (s[1]);
      }
      /* if shift is greater than bit-width, result must be zero */
      if (!bzla_bv_is_zero (t) && shift >= bw)
      {
        pos_x = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of LSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit (t, i))
          {
            pos_x = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit (s[0], i) != bzla_bv_get_bit (t, j + i))
          {
            pos_x = pos_x == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }
DONE:
  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_srl (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  uint32_t bw;
  uint64_t i, j, shift;
  BzlaBitVector *bv_bw, *tmp, *t, **s;
  BzlaMemMgr *mm;

  pos_x = select_path_non_const (pi->exp);

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;
  bw = bzla_bv_get_width (t);
  assert (bzla_bv_get_width (s[0]) == bw);
  assert (bzla_bv_get_width (s[1]) == bw);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      if (bw > 64)
      {
        bv_bw = bzla_bv_uint64_to_bv (mm, bw, bw);
        tmp   = bzla_bv_ugte (mm, s[1], bv_bw);
        if (bzla_bv_is_one (tmp) && !bzla_bv_is_zero (t))
        {
          bzla_bv_free (mm, bv_bw);
          bzla_bv_free (mm, tmp);
          pos_x = 1;
          goto DONE;
        }
        bzla_bv_free (mm, bv_bw);
        bzla_bv_free (mm, tmp);
        /* actual value is small enough to fit into 32 bit (max bit width
         * handled by Bitwuzla is INT32_MAX) */
        tmp   = bzla_bv_slice (mm, s[1], 32, 0);
        shift = bzla_bv_to_uint64 (tmp);
        bzla_bv_free (mm, tmp);
      }
      else
      {
        shift = bzla_bv_to_uint64 (s[1]);
      }
      /* if shift is greater than bit-width, result must be zero */
      if (!bzla_bv_is_zero (t) && shift >= bw)
      {
        pos_x = 1;
        goto DONE;
      }
      if (shift < bw)
      {
        /* s[1] and number of MSB 0-bits in t must match */
        for (i = 0; i < shift; i++)
        {
          if (bzla_bv_get_bit (t, bw - 1 - i))
          {
            pos_x = 1;
            goto DONE;
          }
        }
        /* s[0] and t (except for the bits shifted out) must match */
        for (i = 0, j = shift; i < bw - j; i++)
        {
          if (bzla_bv_get_bit (s[0], bw - 1 - i)
              != bzla_bv_get_bit (t, bw - 1 - (j + i)))
          {
            pos_x = pos_x == -1 ? 0 : -1;
            break;
          }
        }
      }
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }
DONE:
  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_sra (Bzla *bzla, BzlaPropInfo *pi, BzlaNode *e0, BzlaNode *e1)
{
  assert (bzla);
  assert (e0);
  assert (e1);

  bool is_signed_s, is_signed_t;
  int32_t pos_x, cmp;
  uint32_t bw, cnt_t, cnt_s0;
  uint64_t i, j;
  BzlaBitVector *t, **s, *bv_cnt_t;
  BzlaMemMgr *mm;

  pos_x = -1;

  if (bzla_node_is_bv_const (e0))
  {
    pos_x = 1;
  }
  if (bzla_node_is_bv_const (e1))
  {
    pos_x = 0;
  }

  mm = bzla->mm;
  s  = (BzlaBitVector **) pi->bv;
  t  = (BzlaBitVector *) pi->target_value;
  bw = bzla_bv_get_width (t);
  assert (bzla_bv_get_width (s[0]) == bw);
  assert (bzla_bv_get_width (s[1]) == bw);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      is_signed_t = bzla_bv_get_bit (t, bw - 1) == 1;
      is_signed_s = bzla_bv_get_bit (s[0], bw - 1) == 1;
      if (is_signed_t != is_signed_s)
      {
        pos_x = 0;
        goto DONE;
      }
      if (is_signed_t)
      {
        cnt_s0 = bzla_bv_get_num_leading_ones (s[0]);
        cnt_t  = bzla_bv_get_num_leading_ones (t);
      }
      else
      {
        cnt_s0 = bzla_bv_get_num_leading_zeros (s[0]);
        cnt_t  = bzla_bv_get_num_leading_zeros (t);
      }
      if (cnt_s0 > cnt_t)
      {
        pos_x = 0;
        goto DONE;
      }

      bv_cnt_t = bzla_bv_uint64_to_bv (mm, cnt_t, bw);
      cmp      = bzla_bv_compare (s[1], bv_cnt_t);
      bzla_bv_free (mm, bv_cnt_t);
      /* if shift is greater or equal to bit-width, result must be zero/ones
       * s[1] and number of MSB 0-bits/1-bits in t must match */
      if (cmp >= 0 && cnt_t != bw)
      {
        pos_x = 1;
        goto DONE;
      }

      assert (cnt_t && cnt_s0);
      if (cnt_t < bw)
      {
        /* s[0] and t (except for the bits shifted out) must match */
        j = is_signed_t && cnt_t > cnt_s0 ? cnt_t - cnt_s0 - 1 : cnt_t - cnt_s0;
        assert (bw - j <= bw);
        for (i = 0; i < bw - j; i++)
        {
          if (bzla_bv_get_bit (s[0], bw - 1 - i)
              != bzla_bv_get_bit (t, bw - 1 - (j + i)))
          {
            pos_x = 0;
            goto DONE;
          }
        }
      }
    }
    if (pos_x == -1) pos_x = bzla_rng_pick_rand (bzla->rng, 0, 1);
  }
DONE:
  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log_bin_aux (bzla, pi, e0, e1, "sra");
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_mul (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  uint32_t ctz_bvmul;
  int32_t pos_x, lsb_s0, lsb_s1;
  bool iszero_s0, iszero_s1;
  BzlaBitVector *t, **s;

  pos_x = select_path_non_const (pi->exp);

  s = (BzlaBitVector **) pi->bv;
  t = (BzlaBitVector *) pi->target_value;

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      iszero_s0 = bzla_bv_is_zero (s[0]);
      iszero_s1 = bzla_bv_is_zero (s[1]);

      lsb_s0 = bzla_bv_get_bit (s[0], 0);
      lsb_s1 = bzla_bv_get_bit (s[1], 0);

      /* either s[0] or s[1] are 0 but t > 0 */
      if ((iszero_s0 || iszero_s1) && !bzla_bv_is_zero (t))
      {
        if (iszero_s0) pos_x = 0;
        if (iszero_s1) pos_x = pos_x == -1 ? 1 : -1;
      }
      /* t is odd but either s[0] or s[1] are even */
      else if (bzla_bv_get_bit (t, 0) && (!lsb_s0 || !lsb_s1))
      {
        if (!lsb_s0) pos_x = 0;
        if (!lsb_s1) pos_x = pos_x == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in t < number of 0-LSBs in s[0|1] */
      else
      {
        ctz_bvmul = bzla_bv_get_num_trailing_zeros (t);
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros (s[0])) pos_x = 0;
        if (ctz_bvmul < bzla_bv_get_num_trailing_zeros (s[1]))
          pos_x = pos_x == -1 ? 1 : -1;
      }
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }
  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_udiv (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x, cmp_udiv_max;
  BzlaBitVector *ones, *up, *lo, *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  s     = (BzlaBitVector **) pi->bv;
  t     = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const (pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones         = bzla_bv_ones (mm, bzla_bv_get_width (s[0]));
      cmp_udiv_max = bzla_bv_compare (t, ones);

      /* s[0] / s[1] = 1...1 -> choose x
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        pos_x = 1;
      else
      {
        /* 1...1 / x = 0 -> choose x */
        if (bzla_bv_is_zero (t) && !bzla_bv_compare (s[0], ones)) pos_x = 0;
        /* s[0] < t -> choose x */
        else if (bzla_bv_compare (s[0], t) < 0)
          pos_x = 0;
        else
        {
          up  = bzla_bv_udiv (mm, s[0], t);
          lo  = bzla_bv_inc (mm, t);
          tmp = bzla_bv_udiv (mm, s[0], lo);
          bzla_bv_free (mm, lo);
          lo = bzla_bv_inc (mm, tmp);

          if (bzla_bv_compare (lo, up) > 0) pos_x = 0;
          bzla_bv_free (mm, up);
          bzla_bv_free (mm, lo);
          bzla_bv_free (mm, tmp);
        }

        /* x / 0 != 1...1 -> choose x */
        if (bzla_bv_is_zero (s[1]) || bzla_bv_is_umulo (mm, s[1], t))
          pos_x = pos_x == -1 ? 1 : -1;
      }
      bzla_bv_free (mm, ones);
    }
    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }

  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_urem (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  BzlaBitVector *ones, *sub, *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  s     = (BzlaBitVector **) pi->bv;
  t     = (BzlaBitVector *) pi->target_value;

  pos_x = select_path_non_const (pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      ones = bzla_bv_ones (mm, bzla_bv_get_width (s[0]));
      sub  = bzla_bv_sub (mm, s[0], t);
      tmp  = bzla_bv_dec (mm, s[0]);

      /* t = 1...1 -> s[0] = 1...1 and s[1] = 0...0 */
      if (!bzla_bv_compare (t, ones))
      {
        if (!bzla_bv_is_zero (s[1])) pos_x = 1;
        if (bzla_bv_compare (s[0], ones)) pos_x = pos_x == -1 ? 0 : -1;
      }
      /* t > 0 and s[1] = 1 */
      else if (!bzla_bv_is_zero (t) && bzla_bv_is_one (s[1]))
      {
        pos_x = 1;
      }
      /* 0 < s[1] <= t */
      else if (!bzla_bv_is_zero (s[1]) && bzla_bv_compare (s[1], t) <= 0)
      {
        pos_x = pos_x == -1 ? 1 : -1;
      }
      /* s[0] < t or
       * s[0] > t and s[0] - t <= t or
       *                 and s[0] - 1 = t */
      else if (bzla_bv_compare (s[0], t) < 0
               || (bzla_bv_compare (s[0], t) > 0
                   && (bzla_bv_compare (sub, t) <= 0
                       || !bzla_bv_compare (tmp, t))))
      {
        pos_x = 0;
      }

      bzla_bv_free (mm, tmp);
      bzla_bv_free (mm, ones);
      bzla_bv_free (mm, sub);
    }

    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }

  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_concat (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);

  int32_t pos_x;
  uint32_t bw_t;
  BzlaBitVector *tmp, *t, **s;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  s     = (BzlaBitVector **) pi->bv;
  t     = (BzlaBitVector *) pi->target_value;
  pos_x = select_path_non_const (pi->exp);

  if (pos_x == -1)
  {
    if (bzla_opt_get (bzla, BZLA_OPT_PROP_PATH_SEL)
        == BZLA_PROP_PATH_SEL_ESSENTIAL)
    {
      /* s[0] o s[1] = t
       * -> s[0] resp. s[1] must match with t */
      bw_t = bzla_bv_get_width (t);
      tmp  = bzla_bv_slice (mm, t, bw_t - 1, bw_t - bzla_bv_get_width (s[0]));
      if (bzla_bv_compare (tmp, s[0])) pos_x = 0;
      bzla_bv_free (mm, tmp);
      tmp = bzla_bv_slice (mm, t, bzla_bv_get_width (s[1]) - 1, 0);
      if (bzla_bv_compare (tmp, s[1])) pos_x = pos_x == -1 ? 1 : -1;
      bzla_bv_free (mm, tmp);
    }

    if (pos_x == -1) pos_x = select_path_random (bzla, pi->exp);
  }

  assert (pos_x >= 0);
  pi->pos_x = pos_x;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  assert (!bzla_node_is_bv_const (pi->exp->e[pos_x]));
  return pos_x;
}

static int32_t
select_path_slice (Bzla *bzla, BzlaPropInfo *pi)
{
  assert (bzla);
  assert (pi);
  assert (!bzla_node_is_bv_const (pi->exp->e[0]));

  (void) bzla;

  pi->pos_x = 0;
#ifndef NBZLALOG
  select_path_log (bzla, pi);
#endif
  return 0;
}
#endif

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
       * -> flip condition with probability BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
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
      if (bzla_rng_pick_with_prob(bzla->rng, *prob))
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
              bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND)))
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
#else
    (void) stats;
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
  BzlaNode *sra_e[2], *xor_e[2];
  bool is_bv_sra = bzla_opt_get(bzla, BZLA_OPT_PROP_ASHR)
                   && bzla_is_bv_sra(bzla, pi->exp, &sra_e[0], &sra_e[1]);
  bool is_bv_xor = bzla_opt_get(bzla, BZLA_OPT_PROP_XOR)
                   && bzla_is_bv_xor(bzla, pi->exp, &xor_e[0], &xor_e[1]);
  if (is_bv_sra)
  {
    assert(!bzla_node_is_bv_const(sra_e[pi->pos_x]));
  }
  else if (is_bv_xor)
  {
    assert(!bzla_node_is_bv_const(xor_e[pi->pos_x]));
  }
  else
  {
    assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));
  }
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
      bzla->mm, bzla->rng, bzla_bv_get_width(pi->target_value));
}

BzlaBitVector *
bzla_proputils_cons_and(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  uint32_t i, bw;
  BzlaMemMgr *mm;
  BzlaBitVector *res, *tmp;
  BzlaUIntStack dcbits;
  bool b;
  const BzlaBitVector *t;

  mm = bzla->mm;
  t  = pi->target_value;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_and);

  b = bzla_rng_pick_with_prob(bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));

  if (b)
  {
    BZLA_INIT_STACK(mm, dcbits);
    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);

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
        bzla_bv_set_bit(res, i, bzla_rng_pick_rand(bzla->rng, 0, 1));
    }

    if (b && BZLA_COUNT_STACK(dcbits))
      bzla_bv_flip_bit(
          res,
          BZLA_PEEK_STACK(
              dcbits,
              bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(dcbits) - 1)));
    BZLA_RELEASE_STACK(dcbits);
  }
  else
  {
    bw  = bzla_bv_get_width(t);
    tmp = bzla_bv_new_random(mm, bzla->rng, bw);
    res = bzla_bv_or(mm, tmp, t);
    bzla_bv_free(mm, tmp);
  }

  return res;
}

BzlaBitVector *
bzla_proputils_cons_xor(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_xor);
  return bzla_bv_new_random(
      bzla->mm, bzla->rng, bzla_bv_get_width(pi->target_value));
}

BzlaBitVector *
bzla_proputils_cons_eq(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif

  BzlaBitVector *res;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_eq);

  if (bzla_rng_pick_with_prob(bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_EQ_FLIP)))
  {
    res = bzla_bv_copy(bzla->mm, pi->bv[pi->pos_x]);
    bzla_bv_flip_bit(
        res, bzla_rng_pick_rand(bzla->rng, 0, bzla_bv_get_width(res) - 1));
  }
  else
  {
    res = bzla_bv_new_random(
        bzla->mm, bzla->rng, bzla_bv_get_width(pi->bv[1 - pi->pos_x]));
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
        assert(!bzla_bv_is_zero(x->lo));
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_one(mm, bw);
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, ones);
        assert(bzla_bvdomain_gen_has_next(&gen));
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
      res  = bzla_bv_new_random_range(mm, bzla->rng, bw, tmp, ones);
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
        assert(!bzla_bv_is_ones(x->lo));
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        zero = bzla_bv_zero(mm, bw);
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_dec(mm, ones);
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, zero, tmp);
        assert(bzla_bvdomain_gen_has_next(&gen));
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
      res  = bzla_bv_new_random_range(mm, bzla->rng, bw, zero, tmp);
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
    res = bzla_bv_new_random(mm, bzla->rng, bw);
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

static BzlaBitVector *
cons_slt_aux(Bzla *bzla, BzlaPropInfo *pi, bool with_const_bits)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, false);
#endif
  bool isslt;
  uint32_t bw;
  BzlaBitVector *max_signed, *min_signed, *tmp, *res;
  BzlaMemMgr *mm;
  const BzlaBvDomain *x;
  const BzlaBitVector *s, *t;
  BzlaBvDomainSignedGenerator gen;
  int32_t pos_x;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_slt);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = with_const_bits ? pi->bvd[pi->pos_x] : 0;
  s     = pi->bv[1 - pi->pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(s);
  isslt = !bzla_bv_is_zero(t);

  max_signed = bzla_bv_max_signed(mm, bw);
  min_signed = bzla_bv_min_signed(mm, bw);
  if (pos_x == 1 && isslt)
  {
    /* s < res = 1  ->  res > min_signed */
    if (x)
    {
      if (bzla_bvdomain_is_fixed(mm, x))
      {
        assert(!bzla_bv_is_min_signed(x->lo));
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        tmp = bzla_bv_inc(mm, min_signed);
        bzla_bvdomain_gen_signed_init_range(
            mm, bzla->rng, &gen, x, tmp, max_signed);
        assert(bzla_bvdomain_gen_signed_has_next(&gen));
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_signed_random(&gen));
        bzla_bvdomain_gen_signed_delete(&gen);
        bzla_bv_free(mm, tmp);
      }
    }
    else
    {
      tmp = bzla_bv_inc(mm, min_signed);
      res = bzla_bv_new_random_signed_range(mm, bzla->rng, bw, tmp, max_signed);
      bzla_bv_free(mm, tmp);
    }
  }
  else if (pos_x == 0 && isslt)
  {
    /* res < s = 1  ->  min_signed <= res < max_signed */
    if (x)
    {
      if (bzla_bvdomain_is_fixed(mm, x))
      {
        assert(!bzla_bv_is_max_signed(x->lo));
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        tmp = bzla_bv_dec(mm, max_signed);
        bzla_bvdomain_gen_signed_init_range(
            mm, bzla->rng, &gen, x, min_signed, tmp);
        assert(bzla_bvdomain_gen_signed_has_next(&gen));
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_signed_random(&gen));
        bzla_bv_free(mm, tmp);
        bzla_bvdomain_gen_signed_delete(&gen);
      }
    }
    else
    {
      tmp = bzla_bv_dec(mm, max_signed);
      res = bzla_bv_new_random_signed_range(mm, bzla->rng, bw, min_signed, tmp);
      bzla_bv_free(mm, tmp);
    }
  }
  else if (x && bzla_bvdomain_is_fixed(mm, x))
  {
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    res = bzla_bv_new_random(mm, bzla->rng, bw);
    if (x)
    {
      set_const_bits(mm, x, &res);
    }
  }

  bzla_bv_free(mm, max_signed);
  bzla_bv_free(mm, min_signed);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_slt(Bzla *bzla, BzlaPropInfo *pi)
{
  return cons_slt_aux(bzla, pi, false);
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
    bv_shift = bzla_bv_new_random(mm, bzla->rng, bw);
  }
  else
  {
    max      = ctz_t < bw ? ctz_t : ((1u << bw) - 1);
    shift    = bzla_rng_pick_rand(bzla->rng, 0, max);
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
      res = bzla_bv_new_random(mm, bzla->rng, bw);
    }
    else
    {
      if (shift)
      {
        left  = bzla_bv_new_random(mm, bzla->rng, shift);
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
    bv_shift = bzla_bv_new_random(mm, bzla->rng, bw);
  }
  else
  {
    max      = clz_t < bw ? clz_t : ((1u << bw) - 1);
    shift    = bzla_rng_pick_rand(bzla->rng, 0, max);
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
      res = bzla_bv_new_random(mm, bzla->rng, bw);
    }
    else
    {
      if (shift)
      {
        right = bzla_bv_new_random(mm, bzla->rng, shift);
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
bzla_proputils_cons_sra(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  bool is_signed;
  uint32_t bw, cnt_t, shift, max;
  BzlaBitVector *res, *bv_shift, *left, *right;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_sra);

  mm = bzla->mm;
  t  = pi->target_value;
  bw = bzla_bv_get_width(t);

  is_signed = bzla_bv_get_bit(t, bw - 1) == 1;
  cnt_t     = is_signed ? bzla_bv_get_num_leading_ones(t)
                    : bzla_bv_get_num_leading_zeros(t);

  if (bw >= 64 && cnt_t == bw)
  {
    shift    = bw;
    bv_shift = bzla_bv_new_random(mm, bzla->rng, bw);
  }
  else
  {
    max      = cnt_t < bw ? cnt_t : ((1u << bw) - 1);
    shift    = bzla_rng_pick_rand(bzla->rng, 0, max);
    bv_shift = bzla_bv_uint64_to_bv(mm, shift, bw);
  }
  if (shift >= bw) shift = bw;

  if (pi->pos_x)
  {
    if (bzla_bv_is_zero(bv_shift) || cnt_t == bw)
    {
      res = bzla_bv_copy(mm, bv_shift);
    }
    else
    {
      res = bzla_bv_dec(mm, bv_shift);
    }
  }
  else
  {
    if (shift == bw)
    {
      res = bzla_bv_new_random(mm, bzla->rng, bw);
      bzla_bv_set_bit(res, bw - 1, is_signed ? 1 : 0);
    }
    else
    {
      if (shift) shift -= 1;
      if (shift == 0)
      {
        res = bzla_bv_copy(mm, t);
      }
      else
      {
        right = bzla_bv_new_random(mm, bzla->rng, shift);
        left  = bzla_bv_slice(mm, t, bw - 1 - shift, 0);
        res   = bzla_bv_concat(mm, left, right);
        bzla_bv_set_bit(res, bw - 1, is_signed ? 1 : 0);
        bzla_bv_free(mm, left);
        bzla_bv_free(mm, right);
      }
    }
  }
  bzla_bv_free(mm, bv_shift);
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
  res = bzla_bv_new_random(mm, bzla->rng, bw);
  if (!bzla_bv_is_zero(t))
  {
    if (bzla_bv_is_zero(res))
    {
      bzla_bv_free(mm, res);
      res = bzla_bv_new_random(mm, bzla->rng, bw);
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
      if (bzla_rng_pick_with_prob(bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        res = bzla_bv_zero(mm, bw);
        bzla_bv_set_bit(res, bzla_rng_pick_rand(bzla->rng, 0, ctz_t - 1), 1);
      }
      /* choose res as t / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (bzla_rng_pick_with_prob(bzla->rng, 100))
      {
        bzla_bv_free(mm, res);
        if ((r = bzla_rng_pick_rand(bzla->rng, 0, ctz_t)))
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
          bzla_bv_set_bit(res, bzla_rng_pick_rand(bzla->rng, 0, ctz_t - 1), 1);
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
      res = bzla_bv_uint64_to_bv(mm, bzla_rng_pick_rand(bzla->rng, 0, 1), bw);
    else
    {
      res = bzla_bv_new_random_range(mm, bzla->rng, bw, one, ones);
      while (bzla_bv_is_umulo(mm, res, t))
      {
        tmp = bzla_bv_sub(mm, res, one);
        bzla_bv_free(mm, res);
        res = bzla_bv_new_random_range(mm, bzla->rng, bw, one, tmp);
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
      res = bzla_bv_new_random_range(mm, bzla->rng, bw, zero, tmp);
      bzla_bv_free(mm, tmp);
    }
    else if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1: choose random res */
      res = bzla_bv_new_random(mm, bzla->rng, bw);
    }
    else
    {
      /* Compute x = y * t + offset with
       *   y \in [1, ones / t]
       * and
       *   offset \in [0, min(y - 1, ones - y * t)].
       */
      max = bzla_bv_udiv(mm, ones, t);
      y   = bzla_bv_new_random_range(mm, bzla->rng, bw, one, max);
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
      offset = bzla_bv_new_random_range(mm, bzla->rng, bw, zero, max);
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
    else if (bzla_rng_pick_with_prob(bzla->rng, 100))
    {
      /* s % 0 = s = t */
      res = bzla_bv_zero(mm, bw);
    }
    else
    {
      /* else res > t */
      ones = bzla_bv_ones(mm, bw);
      tmp  = bzla_bv_inc(mm, t);
      res  = bzla_bv_new_random_range(mm, bzla->rng, bw, tmp, ones);
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
    else if (bzla_rng_pick_with_prob(bzla->rng, 100))
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
        tmp = bzla_bv_new_random_range(mm, bzla->rng, bw, min, max);
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
bzla_proputils_cons_sext(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  (void) pi;
  if (!bzla_is_inv_sext(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }
  return bzla_proputils_inv_sext(bzla, pi);
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
    res = bzla_rng_flip_coin(bzla->rng) ? bzla_bv_one(mm, 1)
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
  res = bzla_bv_new_random(mm, bzla->rng, bzla_bv_get_width(pi->target_value));
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
  BzlaMemMgr *mm;

  if (!bzla_is_cons_and_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_and);

  mm = bzla->mm;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x)) return bzla_bv_copy(mm, x->lo);
  res = bzla_proputils_cons_and(bzla, pi);
  set_const_bits(mm, x, &res);
  return res;
}

BzlaBitVector *
bzla_proputils_cons_xor_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  BzlaBitVector *res;
  BzlaBvDomainGenerator gen;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_xor);

  mm = bzla->mm;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    bzla_bvdomain_gen_init(bzla->mm, bzla->rng, &gen, x);
    res = bzla_bv_copy(bzla->mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
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
  if (!bzla_is_cons_ult_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }
  return cons_ult_aux(bzla, pi, true);
}

BzlaBitVector *
bzla_proputils_cons_slt_const(Bzla *bzla, BzlaPropInfo *pi)
{
  if (!bzla_is_cons_slt_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }
  return cons_slt_aux(bzla, pi, true);
}

BzlaBitVector *
bzla_proputils_cons_sll_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  int32_t pos_x;
  uint32_t bw, ctz_t;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaMemMgr *mm;

  if (!bzla_is_cons_sll_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_sll);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  ctz_t = bzla_bv_get_num_trailing_zeros(t);

  if (ctz_t == bw)
  {
    res = bvdomain_random(bzla, x);
  }
  else
  {
    assert(ctz_t < bw);
    assert(pi->res_x);
    res = bzla_bv_copy(mm, pi->res_x->lo);
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
  uint32_t bw, clz_t;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  if (!bzla_is_cons_srl_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_srl);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  if (clz_t == bw)
  {
    res = bvdomain_random(bzla, x);
  }
  else
  {
    assert(clz_t < bw);
    assert(pi->res_x);
    res = bzla_bv_copy(mm, pi->res_x->lo);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_sra_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  bool is_signed;
  uint32_t pos_x, bw;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  if (!bzla_is_cons_sra_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_sra);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];
  bw    = bzla_bv_get_width(t);

  is_signed = bzla_bv_get_bit(t, bw - 1) == 1;

  if (pos_x && !is_signed && bzla_bv_is_zero(t))
  {
    bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
  else if (pos_x && is_signed && bzla_bv_is_ones(t))
  {
    bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    assert(pi->res_x);
    res = bzla_bv_copy(mm, pi->res_x->lo);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_mul_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_cons_dbg(bzla, pi, true);
#endif
  bool is_fixed;
  uint32_t bw;
  BzlaBitVector *res, *one;
  const BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;
  const BzlaBitVector *t;

  mm = bzla->mm;
  t  = pi->target_value;
  x  = pi->bvd[pi->pos_x];
  bw = bzla_bv_get_width(t);

  if (!bzla_is_cons_mul_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  if (pi->res_x)
  {
    record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_mul);
    assert(bzla_bv_get_bit(t, 0) == 0);
    res = bzla_bv_copy(mm, pi->res_x->lo);
  }
  else if (bzla_bvdomain_is_fixed(mm, x))
  {
    record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_mul);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    res = bzla_proputils_cons_mul(bzla, pi);

    if (!bzla_bvdomain_check_fixed_bits(mm, x, res))
    {
      bzla_bv_free(mm, res);
      is_fixed = bzla_bvdomain_is_fixed(mm, x);

      assert(bzla_bv_get_bit(t, 0));
      assert(!is_fixed || !bzla_bv_is_zero(x->lo));
      one = bzla_bv_one(mm, bw);
      bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, one, 0);
      bzla_bv_free(mm, one);

      /* t odd, res must be odd */
      assert(!bzla_bvdomain_is_fixed_bit_false(x, 0));
      if (is_fixed)
      {
        assert(bzla_bvdomain_is_fixed_bit_true(x, 0));
        res = bzla_bv_copy(mm, x->lo);
      }
      else
      {
        assert(bzla_bvdomain_gen_has_next(&gen));
        res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        bzla_bv_set_bit(res, 0, 1);
      }
      bzla_bvdomain_gen_delete(&gen);
    }
  }
  return res;
}

BzlaBitVector *
bzla_proputils_cons_udiv_const_pos0_aux(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  assert(pi->pos_x == 0);

  uint32_t i, bw;
  const BzlaBitVector *t;
  const BzlaBvDomain *x;
  BzlaBitVector *res;
  BzlaBitVector *min, *max, *s_min, *s_max, *s_tmp, *tmp;
  BzlaBitVector *ones, *one;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  /* remaining solutions other than x = t:
   * min <= x <= ones with min = x->lo / t * t if x->lo / t > 1 and
   *                       min = 2 * t otherwise */

  mm = bzla->mm;
  t  = pi->target_value;
  x  = pi->bvd[0];
  bw = bzla_bv_get_width(t);

  one = bzla_bv_one(mm, bw);

  res = NULL;
  min = NULL;

  tmp = bzla_bv_udiv(mm, x->lo, t);
  if (bzla_bv_compare(tmp, one) <= 0)
  {
    if (bzla_bv_is_uaddo(mm, t, t))
    {
      /* x = t the only solution */
      bzla_bv_free(mm, tmp);
      bzla_bv_free(mm, one);
      return NULL;
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

  /* min / t <= s <= x->hi / t */
  ones  = bzla_bv_ones(mm, bw);
  s_min = bzla_bv_udiv(mm, min, t);
  s_max = bzla_bv_udiv(mm, x->hi, t);
  if (bzla_bv_compare(s_min, s_max) > 0)
  {
    bzla_bv_free(mm, s_max);
    s_max = bzla_bv_copy(mm, ones);
  }
  bzla_bv_free(mm, min);
  min = NULL;
  for (i = 0; i < 20; i++)
  {
    s_tmp = bzla_bv_new_random_range(mm, bzla->rng, bw, s_min, s_max);
    if (bzla_bv_is_umulo(mm, s_tmp, t))
    {
      bzla_bv_free(mm, s_tmp);
      continue;
    }
    /* for s_tmp, min = s_tmp * t and max = min + s - 1 */
    min = bzla_bv_mul(mm, s_tmp, t);
    tmp = bzla_bv_add(mm, s_tmp, min);
    if (bzla_bv_compare(min, tmp) > 0)
    {
      max = bzla_bv_copy(mm, ones);
    }
    else
    {
      max = bzla_bv_dec(mm, tmp);
    }
    bzla_bv_free(mm, tmp);
    bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, min, max);
    if (bzla_bvdomain_gen_has_next(&gen))
    {
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bv_free(mm, s_tmp);
      bzla_bv_free(mm, min);
      min = NULL;
      bzla_bv_free(mm, max);
      bzla_bvdomain_gen_delete(&gen);
      break;
    }
    bzla_bv_free(mm, s_tmp);
    bzla_bv_free(mm, min);
    min = NULL;
    bzla_bv_free(mm, max);
    bzla_bvdomain_gen_delete(&gen);
  }
  bzla_bv_free(mm, s_min);
  bzla_bv_free(mm, s_max);
  if (min) bzla_bv_free(mm, min);
  bzla_bv_free(mm, ones);
  bzla_bv_free(mm, one);

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
  bool check_zero, check_one, check_t;
  BzlaBitVector *res, *max, *zero, *one, *ones;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  if (!bzla_is_cons_udiv_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_udiv);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);

  zero = bzla_bv_zero(mm, bw);
  one  = bzla_bv_one(mm, bw);
  ones = bzla_bv_ones(mm, bw);

  if (bzla_bvdomain_is_fixed(mm, x))
  {
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pos_x)
  {
    if (bzla_bv_is_ones(t))
    {
      /* t = 1...1 then res = 0 or res = 1 */

      assert(!pi->res_x);
      check_zero = bzla_bvdomain_check_fixed_bits(mm, x, zero);
      check_one  = bzla_bvdomain_check_fixed_bits(mm, x, one);

      if (!check_zero)
      {
        assert(check_one);
        res = bzla_bv_one(mm, bw);
      }
      else if (!check_one)
      {
        res = bzla_bv_zero(mm, bw);
      }
      else
      {
        res = bzla_rng_flip_coin(bzla->rng) ? bzla_bv_zero(mm, bw)
                                            : bzla_bv_one(mm, bw);
      }
    }
    else
    {
      assert(!bzla_bv_is_umulo(mm, x->lo, t));
      assert(pi->res_x);
      res = bzla_bv_copy(mm, pi->res_x->lo);
    }
  }
  else
  {
    if (bzla_bv_is_zero(t))
    {
      /* t = 0: random res < 1...1 */
      assert(!pi->res_x);
      assert(!bzla_bv_is_ones(x->lo));
      max = bzla_bv_dec(mm, ones);
      bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, 0, max);
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bv_free(mm, max);
      bzla_bvdomain_gen_delete(&gen);
    }
    else if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1: choose random res */
      assert(!pi->res_x);
      bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bvdomain_gen_delete(&gen);
    }
    else if (!bzla_bv_compare(t, one))
    {
      /* t = 1: choose random res > 0 */
      assert(!pi->res_x);
      bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, one, 0);
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
      bzla_bvdomain_gen_delete(&gen);
    }
    else
    {
      assert(bzla_bv_compare(x->hi, t) >= 0);

      /* simplest solution:
       *   x = t
       *
       * remaining solutions (determined in is_cons_udiv_const):
       *   min <= x <= ones with min = x->lo / t * t if x->lo / t > 1 and
       *                         min = 2 * t otherwise */

      /* pick x = t with prob=10% if possible */
      check_t = bzla_bvdomain_check_fixed_bits(mm, x, t);
      if (check_t && bzla_rng_pick_with_prob(bzla->rng, 100))
      {
        res = bzla_bv_copy(mm, t);
      }
      else
      {
        if (pi->res_x)
        {
          res = bzla_bv_copy(mm, pi->res_x->lo);
        }
        else
        {
          res = bzla_proputils_cons_udiv_const_pos0_aux(bzla, pi);
          if (!res)
          {
            /* x = t the only solution */
            assert(check_t);
            res = bzla_bv_copy(mm, t);
          }
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
bzla_proputils_cons_urem_const_pos0_aux(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  assert(pi->pos_x == 0);

  int32_t pos_x;
  BzlaBitVector *res, *tmp, *min;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_urem);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  t     = pi->target_value;
  x     = pi->bvd[pos_x];

  /* x > t:
   * pick s > t such that x = s + t does not overflow -> t < s < ones - t
   * -> 2*t + 1 <= x <= ones */
  res = NULL;
  min = bzla_bv_inc(mm, t);
  assert(!bzla_bv_is_uaddo(mm, min, t));
  tmp = bzla_bv_add(mm, min, t);
  bzla_bv_free(mm, min);
  min = tmp;
  bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, min, 0);
  if (bzla_bvdomain_gen_has_next(&gen))
  {
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
  }
  bzla_bvdomain_gen_delete(&gen);
  bzla_bv_free(mm, tmp);
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
  BzlaBitVector *res, *zero, *ones, *max, *min;
  const BzlaBvDomain *x;
  const BzlaBitVector *t;
  BzlaBvDomainGenerator gen;
  BzlaMemMgr *mm;

  if (!bzla_is_cons_urem_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

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
    if (check_zero && bzla_rng_pick_with_prob(bzla->rng, 100))
    {
      res = bzla_bv_copy(mm, zero);
    }
    else
    {
      if (!bzla_bv_compare(t, ones))
      {
        /* t = 1...1  ->  res = 0 */
        assert(check_zero);
        res = bzla_bv_copy(mm, zero);
      }
      else if (!pi->res_x)
      {
        assert(check_zero);
        if (bzla_rng_flip_coin(bzla->rng))
        {
          res = bzla_bv_copy(mm, zero);
        }
        else
        {
          min = bzla_bv_inc(mm, t);
          bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, min, 0);
          if (!bzla_bvdomain_gen_has_next(&gen))
          {
            res = bzla_bv_copy(mm, zero);
          }
          else
          {
            res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
          }
          bzla_bv_free(mm, min);
          bzla_bvdomain_gen_delete(&gen);
        }
      }
      else
      {
        /* else res > t */
        res = bzla_bv_copy(mm, pi->res_x->lo);
      }
    }
  }
  else
  {
    if (!bzla_bv_compare(t, ones))
    {
      /* t = 1...1  ->  res = 1...1 */
      assert(bzla_bvdomain_check_fixed_bits(mm, x, ones));
      res = bzla_bv_copy(mm, ones);
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
        assert(bzla_bvdomain_check_fixed_bits(mm, x, t));
        res = bzla_bv_copy(mm, t);
      }
      else
      {
        check_t = bzla_bvdomain_check_fixed_bits(mm, x, t);
        if (check_t && bzla_rng_pick_with_prob(bzla->rng, 100))
        {
          res = bzla_bv_copy(mm, t);
        }
        else if (pi->res_x)
        {
          res = bzla_bv_copy(mm, pi->res_x->lo);
        }
        else
        {
          res = bzla_proputils_cons_urem_const_pos0_aux(bzla, pi);
          if (!res)
          {
            assert(check_t);
            res = bzla_bv_copy(mm, t);
          }
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
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  if (!bzla_is_cons_concat_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }

  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.cons_concat);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pos_x];
  t     = pi->target_value;
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

  assert(bzla_bvdomain_check_fixed_bits(mm, pi->bvd[pos_x], res));
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
bzla_proputils_cons_sext_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(bzla);
  assert(pi);
  (void) bzla;
  if (!bzla_is_inv_sext_const(bzla, pi))
  {
    /* non-recoverable conflict */
    return NULL;
  }
  return bzla_proputils_inv_sext_const(bzla, pi);
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
      bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
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
#else
    (void) stats;
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

  bool is_bv_sra, is_bv_xor;
  uint32_t arity;
  BzlaNode *sra_e[2], *xor_e[2];

  is_bv_sra = bzla_opt_get(bzla, BZLA_OPT_PROP_ASHR)
              && bzla_is_bv_sra(bzla, pi->exp, &sra_e[0], &sra_e[1]);
  is_bv_xor = bzla_opt_get(bzla, BZLA_OPT_PROP_XOR)
              && bzla_is_bv_xor(bzla, pi->exp, &xor_e[0], &xor_e[1]);
  arity = is_bv_sra ? 2 : pi->exp->arity;

  for (uint32_t i = 0; i < arity; ++i)
  {
    assert(pi->bv[i]);
  }

  assert(!same_bw
         || bzla_bv_get_width(pi->bv[1 - pi->pos_x])
                == bzla_bv_get_width(pi->target_value));
  assert(pi->pos_x >= 0);
  assert(pi->pos_x <= 1);
  if (is_bv_sra)
  {
    assert(!bzla_node_is_bv_const(sra_e[pi->pos_x]));
  }
  else if (is_bv_xor)
  {
    assert(!bzla_node_is_bv_const(xor_e[pi->pos_x]));
  }
  else
  {
    assert(!bzla_node_is_bv_const(pi->exp->e[pi->pos_x]));
  }
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
  BzlaBitVector *res, *tmp1, *tmp2, *mask;
  BzlaMemMgr *mm;
  BzlaUIntStack dcbits;
  bool b;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_and);

  s = pi->bv[1 - pi->pos_x];
  t = pi->target_value;
  b = bzla_rng_pick_with_prob(bzla->rng,
                              bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_AND_FLIP));

  if (b)
  {
    BZLA_INIT_STACK(mm, dcbits);

    res = bzla_bv_copy(mm, pi->bv[pi->pos_x]);
    assert(res);

    for (i = 0, bw = bzla_bv_get_width(t); i < bw; i++)
    {
      bit_and = bzla_bv_get_bit(t, i);
      bit_e   = bzla_bv_get_bit(s, i);

      assert(!bit_and || bit_e);

      /* ---------------------------------------------------------------------
       * res & s = s & res = t
       *
       * -> all bits set in t and s must be set in res
       * -> all bits not set in t but set in s must not be set in res
       * -> all bits not set in s can be chosen to be set randomly
       * -------------------------------------------------------------------- */
      if (bit_and)
        bzla_bv_set_bit(res, i, 1);
      else if (bit_e)
        bzla_bv_set_bit(res, i, 0);
      else if (b)
        BZLA_PUSH_STACK(dcbits, i);
      else
        bzla_bv_set_bit(res, i, bzla_rng_pick_rand(bzla->rng, 0, 1));
    }

    if (b && BZLA_COUNT_STACK(dcbits))
      bzla_bv_flip_bit(
          res,
          BZLA_PEEK_STACK(
              dcbits,
              bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(dcbits) - 1)));

    BZLA_RELEASE_STACK(dcbits);
  }
  else
  {
    /* res = (t & s) | (~s & rand) */
    bw   = bzla_bv_get_width(t);
    tmp1 = bzla_bv_new_random(mm, bzla->rng, bw);
    mask = bzla_bv_not(mm, s);
    tmp2 = bzla_bv_and(mm, tmp1, mask);
    bzla_bv_free(mm, mask);
    bzla_bv_free(mm, tmp1);

    tmp1 = bzla_bv_and(mm, t, s);
    res  = bzla_bv_or(mm, tmp1, tmp2);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_and, pi, res, "AND");
#endif

  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: xor                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_xor(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_xor, bzla_is_inv_xor_const, false);
#endif
  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_xor);
  return bzla_bv_xor(bzla->mm, pi->bv[1 - pi->pos_x], pi->target_value);
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
    if (bzla_rng_pick_with_prob(bzla->rng,
                                bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_EQ_FLIP)))
    {
      res = bzla_bv_copy(bzla->mm, pi->bv[pi->pos_x]);
      while (!bzla_bv_compare(res, s))
      {
        if (res) bzla_bv_free(bzla->mm, res);
        res = bzla_bv_copy(bzla->mm, pi->bv[pi->pos_x]);
        bzla_bv_flip_bit(
            res, bzla_rng_pick_rand(bzla->rng, 0, bzla_bv_get_width(res) - 1));
      }
    }
    else
    {
      res = 0;
      do
      {
        if (res) bzla_bv_free(mm, res);
        res = bzla_bv_new_random(mm, bzla->rng, bzla_bv_get_width(s));
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

static bool
is_true_constraint(Bzla *bzla, BzlaNode *n)
{
  BzlaNode *not_n = bzla_node_invert(n);

  if (bzla_hashptr_table_get(bzla->unsynthesized_constraints, n)
      || bzla_hashptr_table_get(bzla->synthesized_constraints, n)
      || bzla_hashptr_table_get(bzla->assumptions, n))
  {
    return bzla_bv_is_true(bzla_model_get_bv(bzla, n));
  }
  else if (bzla_hashptr_table_get(bzla->unsynthesized_constraints, not_n)
           || bzla_hashptr_table_get(bzla->synthesized_constraints, not_n)
           || bzla_hashptr_table_get(bzla->assumptions, not_n))
  {
    return bzla_bv_is_true(bzla_model_get_bv(bzla, not_n));
  }
  return false;
}

static void
compute_ineq_bounds(Bzla *bzla,
                    BzlaPropInfo *pi,
                    BzlaBitVector **res_min,
                    BzlaBitVector **res_max)
{
  assert(bzla);
  assert(pi);
  assert(res_min);
  assert(res_max);

  bool is_signed;
  uint32_t pos_x, bw;
  BzlaNodeKind kind;
  BzlaMemMgr *mm;
  BzlaNode *x, *parent;
  BzlaNodeIterator it;
  const BzlaBitVector *t, *value, *cvalue;
  const BzlaBitVector *min = 0, *max = 0, *min_excl = 0, *max_excl = 0;
  BzlaBitVector *min_value, *max_value;
  int32_t (*bv_cmp_fun)(const BzlaBitVector *, const BzlaBitVector *);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->exp->e[pos_x];
  t     = pi->target_value;
  kind  = pi->exp->kind;

  bw        = bzla_bv_get_width(pi->bv[0]);
  is_signed = kind == BZLA_BV_SLT_NODE;

  if (is_signed)
  {
    bv_cmp_fun = bzla_bv_signed_compare;
    min_value  = bzla_bv_min_signed(mm, bw);
    max_value  = bzla_bv_max_signed(mm, bw);
  }
  else
  {
    assert(kind == BZLA_BV_ULT_NODE);
    bv_cmp_fun = bzla_bv_compare;
    min_value  = bzla_bv_zero(mm, bw);
    max_value  = bzla_bv_ones(mm, bw);
  }

  if (pos_x == 0)
  {
    /* x < s */
    if (bzla_bv_is_true(t))
    {
      min      = min_value;
      max_excl = pi->bv[1];
    }
    /* x >= s */
    else
    {
      min = pi->bv[1];
      max = max_value;
    }
  }
  else
  {
    /* s < x */
    if (bzla_bv_is_true(t))
    {
      min_excl = pi->bv[0];
      max      = max_value;
    }
    /* s >= x */
    else
    {
      min = min_value;
      max = pi->bv[0];
    }
  }

  if (bzla_opt_get(bzla, BZLA_OPT_PROP_INFER_INEQ_BOUNDS))
  {
    // TODO: conflicting ranges
    bzla_iter_parent_init(&it, x);
    while (bzla_iter_parent_has_next(&it))
    {
      parent = bzla_iter_parent_next(&it);

      if (!parent->constraint || parent == pi->exp || kind != parent->kind)
      {
        continue;
      }

      /* Skip all unsatisfied roots. */
      if (!is_true_constraint(bzla, parent)) continue;

      cvalue = bzla_model_get_bv(bzla, parent);

      if (parent->e[0] == x)
      {
        value = bzla_model_get_bv(bzla, parent->e[1]);

        /* x < value */
        if (bzla_bv_is_true(cvalue))
        {
          if (!max_excl || bv_cmp_fun(max_excl, value) > 0)
          {
            max_excl = value;
          }
        }
        /* x >= value */
        else
        {
          if (!min || bv_cmp_fun(min, value) < 0)
          {
            min = value;
          }
        }
      }
      else if (parent->e[1] == x)
      {
        value = bzla_model_get_bv(bzla, parent->e[0]);

        /* value < x */
        if (bzla_bv_is_true(cvalue))
        {
          if (!min_excl || bv_cmp_fun(min_excl, value) < 0)
          {
            min_excl = value;
          }
        }
        /* value >= x */
        else
        {
          if (!max || bv_cmp_fun(max, value) > 0)
          {
            max = value;
          }
        }
      }
    }
  }

  assert(min || min_excl);
  assert(max || max_excl);

  bool conflict = false;

  if ((min_excl && bzla_bv_compare(min_excl, max_value) == 0)
      || (max_excl && bzla_bv_compare(max_excl, min_value) == 0))
  {
    conflict = true;
  }

  if (conflict) goto CONFLICT;

  if ((min && min_excl && bv_cmp_fun(min, min_excl) <= 0) || !min)
  {
    assert(bzla_bv_compare(min_excl, max_value) != 0);
    *res_min = bzla_bv_inc(mm, min_excl);
  }
  else
  {
    assert(min);
    assert(!min_excl || bv_cmp_fun(min, min_excl) > 0);
    *res_min = bzla_bv_copy(mm, min);
  }

  if ((max && max_excl && bv_cmp_fun(max, max_excl) >= 0) || !max)
  {
    assert(bzla_bv_compare(max_excl, min_value) != 0);
    *res_max = bzla_bv_dec(mm, max_excl);
  }
  else
  {
    assert(max);
    assert(!max_excl || bv_cmp_fun(max, max_excl) < 0);
    *res_max = bzla_bv_copy(mm, max);
  }

  assert(*res_min);
  assert(*res_max);
  assert(!conflict);

  /* s is conflicting with currently satisfied inequality constraints */
  conflict = bv_cmp_fun(*res_min, *res_max) > 0;

  if (conflict)
  {
    bzla_bv_free(mm, *res_min);
    bzla_bv_free(mm, *res_max);
  CONFLICT:
    *res_min = 0;
    *res_max = 0;
  }

  bzla_bv_free(mm, min_value);
  bzla_bv_free(mm, max_value);
}

static BzlaBitVector *
inv_ult_concat_new_random(BzlaMemMgr *mm,
                          BzlaRNG *rng,
                          const BzlaBvDomain *x,
                          const BzlaBitVector *min,
                          const BzlaBitVector *max)
{
  uint32_t bw;
  BzlaBvDomainGenerator gen;
  BzlaBitVector *res = 0;

  if (x)
  {
    bzla_bvdomain_gen_init_range(mm, rng, &gen, x, min, max);
    if (bzla_bvdomain_gen_has_next(&gen))
    {
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_next(&gen));
    }
    bzla_bvdomain_gen_delete(&gen);
  }
  else
  {
    bw  = bzla_bv_get_width(min);
    res = bzla_bv_new_random_range(mm, rng, bw, min, max);
  }
  return res;
}

static BzlaBitVector *
inv_ult_concat(Bzla *bzla, BzlaPropInfo *pi, bool with_const_bits)
{
  bool isult;
  int32_t pos_x;
  uint32_t bw_x, bw_x0, bw_x1;
  BzlaBitVector *res, *tmp, *x0, *x1, *s0, *s1;
  BzlaBitVector *min, *max, *min_signed;
  BzlaMemMgr *mm;
  BzlaNode *exp_x, *real_exp_x, *exp_x0, *exp_x1;
  const BzlaBitVector *s, *t, *x;
  BzlaBvDomain *dx0 = 0, *dx1 = 0;
  BzlaRNG *rng;

  mm         = bzla->mm;
  pos_x      = pi->pos_x;
  x          = pi->bv[pos_x];
  s          = pi->bv[1 - pos_x];
  t          = pi->target_value;
  exp_x      = pi->exp->e[pos_x];
  real_exp_x = bzla_node_real_addr(exp_x);

  if (!bzla_node_is_bv_concat(exp_x)) return 0;

  isult = bzla_bv_is_true(t);

  res = 0;

  rng    = bzla->rng;
  exp_x0 = real_exp_x->e[0];
  exp_x1 = real_exp_x->e[1];
  bw_x   = bzla_node_bv_get_width(bzla, exp_x);
  bw_x0  = bzla_node_bv_get_width(bzla, exp_x0);
  bw_x1  = bzla_node_bv_get_width(bzla, exp_x1);
  assert(bw_x - bw_x1 == bw_x0);
  x0 = bzla_bv_slice(mm, x, bw_x - 1, bw_x1);
  x1 = bzla_bv_slice(mm, x, bw_x1 - 1, 0);
  s0 = bzla_bv_slice(mm, s, bw_x - 1, bw_x1);
  s1 = bzla_bv_slice(mm, s, bw_x1 - 1, 0);
  if (with_const_bits)
  {
    dx0 = bzla_bvdomain_slice(mm, pi->bvd[pos_x], bw_x - 1, bw_x1);
    dx1 = bzla_bvdomain_slice(mm, pi->bvd[pos_x], bw_x1 - 1, 0);
  }

  if (bzla_is_bv_sext(bzla, exp_x))
  {
    min_signed = bzla_bv_min_signed(mm, bw_x1);

    /* x < s = t */
    if (pos_x == 0)
    {
      /* x0 o x1 < s0 o s1 */
      if (isult)
      {
        min = bzla_bv_zero(mm, bw_x1);
        /* s0 == zero -> pick x1 < min(min_signed, s1) */
        if (bzla_bv_is_zero(s0))
        {
          tmp = bzla_bv_compare(s1, min_signed) < 0 ? s1 : min_signed;
          max = bzla_bv_is_zero(tmp) ? bzla_bv_copy(mm, tmp)
                                     : bzla_bv_dec(mm, tmp);
        }
        /* s0 == ones -> pick x1 < max(min_signed, s1) */
        else if (bzla_bv_is_ones(s0))
        {
          max = bzla_bv_dec(
              mm, bzla_bv_compare(min_signed, s1) < 0 ? s1 : min_signed);
        }
        /* pick x1 < min_signed */
        else
        {
          max = bzla_bv_dec(mm, min_signed);
        }

        tmp = inv_ult_concat_new_random(mm, rng, dx1, min, max);
        bzla_bv_free(mm, min);
        bzla_bv_free(mm, max);
        if (tmp)
        {
          res = bzla_bv_sext(mm, tmp, bw_x0);
          bzla_bv_free(mm, tmp);
          assert(bzla_bv_compare(res, s) < 0);
        }
      }
      /* x0 o x1 >= s0 o s1 */
      else
      {
        max = bzla_bv_ones(mm, bw_x1);
        /* s0 == zero -> pick x1 >= min(min_signed, s1) */
        if (bzla_bv_is_zero(s0))
        {
          min = bzla_bv_copy(
              mm, bzla_bv_compare(min_signed, s1) < 0 ? min_signed : s1);
        }
        /* s1 == ones -> pick x1 >= max(min_signed, s1) */
        else if (bzla_bv_is_ones(s0))
        {
          min = bzla_bv_copy(
              mm, bzla_bv_compare(min_signed, s1) > 0 ? min_signed : s1);
        }
        /* s0 > zero && s0 < ones -> pick x1 >= min_signed */
        else
        {
          min = bzla_bv_copy(mm, min_signed);
        }

        tmp = inv_ult_concat_new_random(mm, rng, dx1, min, max);
        bzla_bv_free(mm, min);
        bzla_bv_free(mm, max);
        if (tmp)
        {
          res = bzla_bv_sext(mm, tmp, bw_x0);
          assert(bzla_bv_compare(res, s) >= 0);
          bzla_bv_free(mm, tmp);
        }
      }
    }
    /* s < x = t */
    else
    {
      /* s0 o s1 < x0 o x1 */
      if (isult)
      {
        max = bzla_bv_ones(mm, bw_x1);

        /* s0 == zero
         *  1) min_signed <= s1 -> pick x1 >= min_signed
         *  2) else                pick x1 > s1
         */
        if (bzla_bv_is_zero(s0))
        {
          min = bzla_bv_compare(min_signed, s1) <= 0
                    ? bzla_bv_copy(mm, min_signed)
                    : bzla_bv_inc(mm, s1);
        }
        /* s0 == ones
         *  1) min_signed > 1 -> pick x1 >= min_signed
         *  2) else              pick x1 > s1
         */
        else if (bzla_bv_is_ones(s0))
        {
          min = bzla_bv_compare(min_signed, s1) > 0
                    ? bzla_bv_copy(mm, min_signed)
                    : bzla_bv_inc(mm, s1);
        }
        /* s0 > zero && s0 < ones -> pick x1 >= min_signed */
        else
        {
          min = bzla_bv_copy(mm, min_signed);
        }

        tmp = inv_ult_concat_new_random(mm, rng, dx1, min, max);
        bzla_bv_free(mm, min);
        bzla_bv_free(mm, max);
        if (tmp)
        {
          res = bzla_bv_sext(mm, tmp, bw_x0);
          assert(bzla_bv_compare(s, res) < 0);
          bzla_bv_free(mm, tmp);
        }
      }
      /* s0 o s1 >= x0 o x1 */
      else
      {
        min = bzla_bv_zero(mm, bw_x1);
        tmp = bzla_bv_dec(mm, min_signed);

        /* s0 == zero
         *  1) min_signed - 1 < s1 -> pick x1 <= min_signed - 1
         *  2) else                   pick x1 <= s1
         */
        if (bzla_bv_is_zero(s0))
        {
          max = bzla_bv_copy(mm, bzla_bv_compare(tmp, s1) < 0 ? tmp : s1);
        }
        /* s1 == ones
         *  1) s1 >= min_signed -> pick x1 <= s1
         *  2) else                pick x1 <= min_signed - 1
         */
        else if (bzla_bv_is_ones(s0))
        {
          max =
              bzla_bv_copy(mm, bzla_bv_compare(s1, min_signed) >= 0 ? s1 : tmp);
        }
        /* s1 > zero && s1 < ones -> pick x1 < min_signed */
        else
        {
          max = bzla_bv_copy(mm, tmp);
        }

        bzla_bv_free(mm, tmp);
        tmp = inv_ult_concat_new_random(mm, rng, dx1, min, max);
        bzla_bv_free(mm, min);
        bzla_bv_free(mm, max);

        if (tmp)
        {
          res = bzla_bv_sext(mm, tmp, bw_x0);
          assert(bzla_bv_compare(s, res) >= 0);
          bzla_bv_free(mm, tmp);
        }
      }
    }

    bzla_bv_free(mm, min_signed);
  }
  /* For concats we try to only change the value of one of it's children if
   * possible. */
  else
  {
    BzlaBitVector *res_x0 = 0, *res_x1 = 0;

    if (pos_x == 0)
    {
      /* x0 o x1 < s0 o s1 */
      if (isult)
      {
        assert(!bzla_bv_is_zero(s));

        /* x0 > s0 -> pick x0 <= s0 */
        if (bzla_bv_compare(x0, s0) > 0)
        {
          min = bzla_bv_zero(mm, bw_x0);
          max =
              bzla_bv_is_zero(s1) ? bzla_bv_dec(mm, s0) : bzla_bv_copy(mm, s0);
          res_x0 = inv_ult_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        /* x0 == s0 && s1 == zero -> pick x0 < s0 */
        else if (bzla_bv_compare(x0, s0) == 0 && bzla_bv_is_zero(s1))
        {
          assert(!bzla_bv_is_zero(s0));
          min    = bzla_bv_zero(mm, bw_x0);
          max    = bzla_bv_dec(mm, s0);
          res_x0 = inv_ult_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }

        if (res_x0)
        {
          assert(bzla_bv_compare(res_x0, s0) <= 0);

          /* If x0 == s0 && x1 >= s1 -> pick x1 < s1 */
          if (bzla_bv_compare(res_x0, s0) == 0 && bzla_bv_compare(x1, s1) >= 0)
          {
            assert(!bzla_bv_is_zero(s1));
            min    = bzla_bv_zero(mm, bw_x1);
            max    = bzla_bv_dec(mm, s1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, min, max);
            bzla_bv_free(mm, min);
            bzla_bv_free(mm, max);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }

          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_compare(res, s) < 0);
            bzla_bv_free(mm, res_x1);
          }

          bzla_bv_free(mm, res_x0);
        }
      }
      /* x0 o x1 >= s0 o s1 */
      else
      {
        /* x0 < s0 -> pick x0 >= s0 */
        if (bzla_bv_compare(x0, s0) < 0)
        {
          max    = bzla_bv_ones(mm, bw_x0);
          res_x0 = inv_ult_concat_new_random(mm, rng, dx0, s0, max);
          bzla_bv_free(mm, max);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }

        if (res_x0)
        {
          assert(bzla_bv_compare(res_x0, s0) >= 0);

          /* x0 == s0 && x1 < s1 -> pick x1 >= s1 */
          if (bzla_bv_compare(res_x0, s0) == 0 && bzla_bv_compare(x1, s1) < 0)
          {
            max    = bzla_bv_ones(mm, bw_x1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, s1, max);
            bzla_bv_free(mm, max);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }

          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_compare(res, s) >= 0);
            bzla_bv_free(mm, res_x1);
          }

          bzla_bv_free(mm, res_x0);
        }
      }
    }
    else
    {
      /* s0 o s1 < x0 o x1 */
      if (isult)
      {
        assert(!bzla_bv_is_ones(s));

        /* x0 < s0 -> pick x0 >= s0 */
        if (bzla_bv_compare(x0, s0) < 0)
        {
          min =
              bzla_bv_is_ones(s1) ? bzla_bv_inc(mm, s0) : bzla_bv_copy(mm, s0);
          max    = bzla_bv_ones(mm, bw_x0);
          res_x0 = inv_ult_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        /* x0 == s0 && s1 == ones -> pick x0 > s0 */
        else if (bzla_bv_compare(x0, s0) == 0 && bzla_bv_is_ones(s1))
        {
          assert(!bzla_bv_is_ones(s0));
          min    = bzla_bv_inc(mm, s0);
          max    = bzla_bv_ones(mm, bw_x0);
          res_x0 = inv_ult_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }

        if (res_x0)
        {
          assert(bzla_bv_compare(res_x0, s0) >= 0);

          /* x0 == s0 && x1 < s1 -> pick x1 > s1 */
          if (bzla_bv_compare(res_x0, s0) == 0 && bzla_bv_compare(x1, s1) <= 0)
          {
            assert(!bzla_bv_is_ones(s1));
            min    = bzla_bv_inc(mm, s1);
            max    = bzla_bv_ones(mm, bw_x1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, min, max);
            bzla_bv_free(mm, min);
            bzla_bv_free(mm, max);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }

          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_compare(s, res) < 0);
            bzla_bv_free(mm, res_x1);
          }
          bzla_bv_free(mm, res_x0);
        }
      }
      /* s0 o s1 >= x0 o x1 */
      else
      {
        /* s0 < x0 -> pick x0 <= s0 */
        if (bzla_bv_compare(s0, x0) < 0)
        {
          min    = bzla_bv_zero(mm, bw_x0);
          res_x0 = inv_ult_concat_new_random(mm, rng, dx0, min, s0);
          bzla_bv_free(mm, min);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }

        if (res_x0)
        {
          assert(bzla_bv_compare(s0, res_x0) >= 0);

          /* s0 == x0 && s1 < x1 -> pick x1 <= s1 */
          if (bzla_bv_compare(s0, res_x0) == 0 && bzla_bv_compare(s1, x1) < 0)
          {
            min    = bzla_bv_zero(mm, bw_x1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, min, s1);
            bzla_bv_free(mm, min);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }

          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_compare(s, res) >= 0);
            bzla_bv_free(mm, res_x1);
          }
          bzla_bv_free(mm, res_x0);
        }
      }
    }
  }

  bzla_bv_free(mm, x0);
  bzla_bv_free(mm, x1);
  bzla_bv_free(mm, s0);
  bzla_bv_free(mm, s1);

  if (dx0)
  {
    assert(dx1);
    bzla_bvdomain_free(mm, dx0);
    bzla_bvdomain_free(mm, dx1);
  }

  return res;
}

BzlaBitVector *
bzla_proputils_inv_ult(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_ult, bzla_is_inv_ult_const, false);
#endif
  uint32_t bw;
  BzlaBitVector *res, *min, *max;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);

  res = 0;
  compute_ineq_bounds(bzla, pi, &min, &max);

  if (min && max)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT))
    {
      res = inv_ult_concat(bzla, pi, false);
      /* Result not in range min <= res <= max */
      if (res
          && (bzla_bv_compare(min, res) > 0 || bzla_bv_compare(res, max) > 0))
      {
        bzla_bv_free(mm, res);
        res = 0;
      }
    }

    if (!res)
    {
      bw  = bzla_bv_get_width(pi->bv[pi->pos_x]);
      res = bzla_bv_new_random_range(mm, bzla->rng, bw, min, max);
    }

    bzla_bv_free(mm, min);
    bzla_bv_free(mm, max);
  }
  else
  {
    /* conflicting bounds */
    return 0;
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_ult, pi, res, "<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: slt                                                                   */
/* -------------------------------------------------------------------------- */

static BzlaBitVector *
inv_slt_concat_new_random(BzlaMemMgr *mm,
                          BzlaRNG *rng,
                          const BzlaBvDomain *x,
                          const BzlaBitVector *min,
                          const BzlaBitVector *max)
{
  uint32_t bw;
  BzlaBvDomainSignedGenerator gen;
  BzlaBitVector *res = 0;

  if (x)
  {
    bzla_bvdomain_gen_signed_init_range(mm, rng, &gen, x, min, max);
    if (bzla_bvdomain_gen_signed_has_next(&gen))
    {
      res = bzla_bv_copy(mm, bzla_bvdomain_gen_signed_next(&gen));
    }
    bzla_bvdomain_gen_signed_delete(&gen);
  }
  else
  {
    bw  = bzla_bv_get_width(min);
    res = bzla_bv_new_random_signed_range(mm, rng, bw, min, max);
  }
  return res;
}

static BzlaBitVector *
inv_slt_concat(Bzla *bzla,
               BzlaPropInfo *pi,
               bool with_const_bits,
               bool *conflict)
{
  bool isslt;
  int32_t pos_x;
  uint32_t bw_x, bw_x0, bw_x1;
  BzlaBitVector *res, *tmp, *x0, *x1, *s0, *s1, *zero_x0;
  BzlaBitVector *min, *max, *min_signed, *zero, *max_signed, *min_value;
  BzlaMemMgr *mm;
  BzlaNode *exp_x, *real_exp_x, *exp_x0, *exp_x1;
  const BzlaBitVector *s, *t, *x;
  BzlaRNG *rng;
  BzlaBvDomain *dx0 = 0, *dx1 = 0;

  mm         = bzla->mm;
  pos_x      = pi->pos_x;
  x          = pi->bv[pos_x];
  s          = pi->bv[1 - pos_x];
  t          = pi->target_value;
  exp_x      = pi->exp->e[pos_x];
  real_exp_x = bzla_node_real_addr(exp_x);

  if (!bzla_node_is_bv_concat(exp_x)) return 0;

  isslt = bzla_bv_is_true(t);

  res = 0;

  rng    = bzla->rng;
  exp_x0 = real_exp_x->e[0];
  exp_x1 = real_exp_x->e[1];
  bw_x   = bzla_node_bv_get_width(bzla, exp_x);
  bw_x0  = bzla_node_bv_get_width(bzla, exp_x0);
  bw_x1  = bzla_node_bv_get_width(bzla, exp_x1);
  assert(bw_x - bw_x1 == bw_x0);
  x0 = bzla_bv_slice(mm, x, bw_x - 1, bw_x1);
  x1 = bzla_bv_slice(mm, x, bw_x1 - 1, 0);
  s0 = bzla_bv_slice(mm, s, bw_x - 1, bw_x1);
  s1 = bzla_bv_slice(mm, s, bw_x1 - 1, 0);
  if (with_const_bits)
  {
    dx0 = bzla_bvdomain_slice(mm, pi->bvd[pos_x], bw_x - 1, bw_x1);
    dx1 = bzla_bvdomain_slice(mm, pi->bvd[pos_x], bw_x1 - 1, 0);
  }

  if (bzla_is_bv_sext(bzla, exp_x))
  {
    min_signed = bzla_bv_min_signed(mm, bw_x1);
    max_signed = bzla_bv_max_signed(mm, bw_x1);
    zero       = bzla_bv_zero(mm, bw_x1);

    /* x < s = t */
    if (pos_x == 0)
    {
      /* x0 o x1 < s0 o s1 */
      if (isslt)
      {
        /* The minimum value that x can represent is x0 = ones and x1 =
         * min_signed. If s is smaller or equal to the minimum value we have
         * a conflict. */
        min_value = bzla_bv_sext(mm, min_signed, bw_x0);
        *conflict = bzla_bv_signed_compare(s, min_value) <= 0;
        bzla_bv_free(mm, min_value);
        if (!*conflict)
        {
          /* s0 == zero
           *  1) max_signed < s1 -> pick x1 <= max_signed
           *  2) else               pick x1 < s1
           */
          if (bzla_bv_is_zero(s0))
          {
            max = bzla_bv_compare(max_signed, s1) < 0
                      ? bzla_bv_copy(mm, max_signed)
                      : bzla_bv_dec(mm, s1);
          }
          /* s0 == ones -> pick x1 < min(zero, s1) */
          else if (bzla_bv_is_ones(s0))
          {
            max = bzla_bv_dec(mm,
                              bzla_bv_signed_compare(zero, s1) < 0 ? zero : s1);
          }
          /* pick x1 < min_signed */
          else
          {
            max = bzla_bv_dec(mm, min_signed);
          }

          tmp = inv_slt_concat_new_random(mm, rng, dx1, min_signed, max);
          bzla_bv_free(mm, max);
          if (tmp)
          {
            res = bzla_bv_sext(mm, tmp, bw_x0);
            assert(bzla_bv_signed_compare(res, s) < 0);
            bzla_bv_free(mm, tmp);
          }
        }
      }
      /* x0 o x1 >= s0 o s1 */
      else
      {
        zero_x0 = bzla_bv_zero(mm, bw_x0);
        *conflict =
            (bzla_bv_is_zero(s0) && bzla_bv_compare(s1, min_signed) >= 0)
            || bzla_bv_signed_compare(s0, zero_x0) > 0;
        bzla_bv_free(mm, zero_x0);
        if (!*conflict)
        {
          /* s0 == zero -> pick x1 >= max(s1, zero) */
          if (bzla_bv_is_zero(s0))
          {
            min = bzla_bv_signed_compare(s1, zero) > 0 ? s1 : zero;
          }
          /* s1 == ones -> pick x1 >= max(min_signed, s1) */
          else if (bzla_bv_is_ones(s0))
          {
            min = bzla_bv_compare(min_signed, s1) > 0 ? min_signed : s1;
          }
          /* s0 > zero && s0 < ones -> pick x1 >= min_signed */
          else
          {
            min = min_signed;
          }

          tmp = inv_slt_concat_new_random(mm, rng, dx1, min, max_signed);
          if (tmp)
          {
            res = bzla_bv_sext(mm, tmp, bw_x0);
            assert(bzla_bv_signed_compare(res, s) >= 0);
            bzla_bv_free(mm, tmp);
          }
        }
      }
    }
    /* s < x = t */
    else
    {
      /* s0 o s1 < x0 o x1 */
      if (isslt)
      {
        zero_x0 = bzla_bv_zero(mm, bw_x0);

        *conflict =
            (bzla_bv_is_zero(s0) && bzla_bv_compare(s1, max_signed) >= 0)
            || bzla_bv_signed_compare(s0, zero_x0) > 0;
        bzla_bv_free(mm, zero_x0);
        if (!*conflict)
        {
          /* s0 == zero -> pick x1 > s1 */
          if (bzla_bv_is_zero(s0))
          {
            assert(bzla_bv_compare(s1, max_signed) != 0); /* conflict */
            min = bzla_bv_inc(mm, s1);
          }
          /* s0 == ones
           *  1) min_signed > s1 -> pick x1 >= min_signed
           *  2) else               pick x1 > s1
           */
          else if (bzla_bv_is_ones(s0))
          {
            min = bzla_bv_compare(min_signed, s1) > 0
                      ? bzla_bv_copy(mm, min_signed)
                      : bzla_bv_inc(mm, s1);
          }
          /* s0 > zero && s0 < ones -> pick x1 >= min_signed */
          else
          {
            min = bzla_bv_copy(mm, min_signed);
          }

          tmp = inv_slt_concat_new_random(mm, rng, dx1, min, max_signed);
          bzla_bv_free(mm, min);
          if (tmp)
          {
            res = bzla_bv_sext(mm, tmp, bw_x0);
            assert(bzla_bv_signed_compare(s, res) < 0);
            bzla_bv_free(mm, tmp);
          }
        }
      }
      /* s0 o s1 >= x0 o x1 */
      else
      {
        min_value = bzla_bv_sext(mm, min_signed, bw_x0);
        *conflict = bzla_bv_signed_compare(s, min_value) < 0;
        bzla_bv_free(mm, min_value);

        if (!*conflict)
        {
          /* s0 == zero -> pick x1 <= min(s1, max_signed) */
          if (bzla_bv_is_zero(s0))
          {
            max = bzla_bv_compare(s1, max_signed) < 0 ? s1 : max_signed;
          }
          /* s0 == ones -> pick x1 <= min(zero, s1) */
          else if (bzla_bv_is_ones(s0))
          {
            max = bzla_bv_signed_compare(zero, s1) < 0 ? zero : s1;
          }
          /* pick x1 <= max_signed */
          else
          {
            max = max_signed;
          }

          tmp = inv_slt_concat_new_random(mm, rng, dx1, min_signed, max);
          if (tmp)
          {
            res = bzla_bv_sext(mm, tmp, bw_x0);
            assert(bzla_bv_signed_compare(s, res) >= 0);
            bzla_bv_free(mm, tmp);
          }
        }
      }
    }

    bzla_bv_free(mm, max_signed);
    bzla_bv_free(mm, min_signed);
    bzla_bv_free(mm, zero);
  }
  /* For concats we try to only change the value of one of it's children if
   * possible. */
  else
  {
    BzlaBitVector *res_x0 = 0, *res_x1 = 0;

    if (pos_x == 0)
    {
      /* x0 o x1 < s0 o s1 */
      if (isslt)
      {
        assert(!bzla_bv_is_min_signed(s));

        /* x0 > s0 -> pick x0 <= s0 */
        if (bzla_bv_signed_compare(x0, s0) > 0)
        {
          min = bzla_bv_min_signed(mm, bw_x0);
          max =
              bzla_bv_is_zero(s1) ? bzla_bv_dec(mm, s0) : bzla_bv_copy(mm, s0);
          res_x0 = inv_slt_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        /* x0 == s0 && s1 == zero -> pick x0 < s0 */
        else if (bzla_bv_signed_compare(x0, s0) == 0 && bzla_bv_is_zero(s1))
        {
          assert(!bzla_bv_is_min_signed(s0));
          min    = bzla_bv_min_signed(mm, bw_x0);
          max    = bzla_bv_dec(mm, s0);
          res_x0 = inv_slt_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }

        if (res_x0)
        {
          assert(bzla_bv_signed_compare(res_x0, s0) <= 0);

          /* If x0 == s0 && x1 >= s1 -> pick x1 < s1 */
          if (bzla_bv_signed_compare(res_x0, s0) == 0
              && bzla_bv_compare(x1, s1) >= 0)
          {
            assert(!bzla_bv_is_zero(s1));
            min    = bzla_bv_zero(mm, bw_x1);
            max    = bzla_bv_dec(mm, s1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, min, max);
            bzla_bv_free(mm, min);
            bzla_bv_free(mm, max);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }

          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_signed_compare(res, s) < 0);
            bzla_bv_free(mm, res_x1);
          }
          bzla_bv_free(mm, res_x0);
        }
      }
      /* x0 o x1 >= s0 o s1 */
      else
      {
        /* x0 < s0 -> pick x0 >= s0 */
        if (bzla_bv_signed_compare(x0, s0) < 0)
        {
          max    = bzla_bv_max_signed(mm, bw_x0);
          res_x0 = inv_slt_concat_new_random(mm, rng, dx0, s0, max);
          bzla_bv_free(mm, max);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }

        if (res_x0)
        {
          assert(bzla_bv_signed_compare(res_x0, s0) >= 0);

          /* x0 == s0 && x1 < s1 -> pick x1 >= s1 */
          if (bzla_bv_signed_compare(res_x0, s0) == 0
              && bzla_bv_compare(x1, s1) < 0)
          {
            max    = bzla_bv_ones(mm, bw_x1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, s1, max);
            bzla_bv_free(mm, max);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }
          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_signed_compare(res, s) >= 0);
            bzla_bv_free(mm, res_x1);
          }
          bzla_bv_free(mm, res_x0);
        }
      }
    }
    else
    {
      /* s0 o s1 < x0 o x1 */
      if (isslt)
      {
        assert(!bzla_bv_is_max_signed(s));

        /* x0 < s0 -> pick x0 >= s0 */
        if (bzla_bv_signed_compare(x0, s0) < 0)
        {
          min =
              bzla_bv_is_ones(s1) ? bzla_bv_inc(mm, s0) : bzla_bv_copy(mm, s0);
          max    = bzla_bv_max_signed(mm, bw_x0);
          res_x0 = inv_slt_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        /* x0 == s0 && s1 == ones -> pick x0 > s0 */
        else if (bzla_bv_signed_compare(x0, s0) == 0 && bzla_bv_is_ones(s1))
        {
          assert(!bzla_bv_is_max_signed(s0));
          min    = bzla_bv_inc(mm, s0);
          max    = bzla_bv_max_signed(mm, bw_x0);
          res_x0 = inv_slt_concat_new_random(mm, rng, dx0, min, max);
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }
        if (res_x0)
        {
          assert(bzla_bv_signed_compare(res_x0, s0) >= 0);

          /* x0 == s0 && x1 < s1 -> pick x1 > s1 */
          if (bzla_bv_signed_compare(res_x0, s0) == 0
              && bzla_bv_compare(x1, s1) <= 0)
          {
            assert(!bzla_bv_is_ones(s1));
            min    = bzla_bv_inc(mm, s1);
            max    = bzla_bv_ones(mm, bw_x1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, min, max);
            bzla_bv_free(mm, min);
            bzla_bv_free(mm, max);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }
          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_signed_compare(s, res) < 0);
            bzla_bv_free(mm, res_x1);
          }
          bzla_bv_free(mm, res_x0);
        }
      }
      /* s0 o s1 >= x0 o x1 */
      else
      {
        /* s0 < x0 -> pick x0 <= s0 */
        if (bzla_bv_signed_compare(s0, x0) < 0)
        {
          min    = bzla_bv_min_signed(mm, bw_x0);
          res_x0 = inv_slt_concat_new_random(mm, rng, dx0, min, s0);
          bzla_bv_free(mm, min);
        }
        else
        {
          res_x0 = bzla_bv_copy(mm, x0);
        }
        if (res_x0)
        {
          assert(bzla_bv_signed_compare(s0, res_x0) >= 0);

          /* s0 == x0 && s1 < x1 -> pick x1 <= s1 */
          if (bzla_bv_signed_compare(s0, res_x0) == 0
              && bzla_bv_compare(s1, x1) < 0)
          {
            min    = bzla_bv_zero(mm, bw_x1);
            res_x1 = inv_ult_concat_new_random(mm, rng, dx1, min, s1);
            bzla_bv_free(mm, min);
          }
          else
          {
            res_x1 = bzla_bv_copy(mm, x1);
          }

          if (res_x1)
          {
            res = bzla_bv_concat(mm, res_x0, res_x1);
            assert(bzla_bv_signed_compare(s, res) >= 0);
            bzla_bv_free(mm, res_x1);
          }
          bzla_bv_free(mm, res_x0);
        }
      }
    }
  }

  bzla_bv_free(mm, x0);
  bzla_bv_free(mm, x1);
  bzla_bv_free(mm, s0);
  bzla_bv_free(mm, s1);

  if (dx0)
  {
    assert(dx1);
    bzla_bvdomain_free(mm, dx0);
    bzla_bvdomain_free(mm, dx1);
  }

  return res;
}

BzlaBitVector *
bzla_proputils_inv_slt(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_slt, bzla_is_inv_slt_const, false);
#endif
  bool conflict = false;
  uint32_t bw;
  BzlaBitVector *res, *min = 0, *max = 0;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_slt);

  res = 0;
  compute_ineq_bounds(bzla, pi, &min, &max);

  if (min && max)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT))
    {
      res = inv_slt_concat(bzla, pi, false, &conflict);
      if (conflict)
      {
        bzla_bv_free(mm, min);
        bzla_bv_free(mm, max);
        return 0;
      }
      /* Result not in range min <= res <= max */
      if (res
          && (bzla_bv_signed_compare(min, res) > 0
              || bzla_bv_signed_compare(res, max) > 0))
      {
        bzla_bv_free(mm, res);
        res = 0;
      }
    }

    if (!res)
    {
      bw  = bzla_bv_get_width(pi->bv[pi->pos_x]);
      res = bzla_bv_new_random_signed_range(mm, bzla->rng, bw, min, max);
    }

    bzla_bv_free(mm, min);
    bzla_bv_free(mm, max);
  }
  else
  {
    /* conflicting bounds */
    return 0;
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_slt, pi, res, "<s");
#endif
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
      res = bzla_bv_new_random(mm, bzla->rng, bw);
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
         * x...x << x = 0...0
         * -> choose random shift <= res <= ones
         */
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        res  = bzla_bv_new_random_range(mm, bzla->rng, bw, tmp, ones);
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
                      bzla_rng_pick_rand(bzla->rng, 0, 1));
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

static BzlaBitVector *
inv_srl_aux(Bzla *bzla, BzlaPropInfo *pi)
{
  int32_t pos_x;
  uint32_t bw, i, clz_s, clz_t, shift;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  res   = 0;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pi->pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);
  clz_t = bzla_bv_get_num_leading_zeros(t);

  /* ------------------------------------------------------------------------
   * s >> x = t
   *
   * -> determine shift value via zero MSBs in t (considering zero MSBs in s)
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
    if (bzla_bv_is_zero(s) && bzla_bv_is_zero(t))
    {
      /* 0...0 >> x = 0...0 -> choose random res */
      res = bzla_bv_new_random(mm, bzla->rng, bw);
    }
    else
    {
      /**
       * clz(s) > clz(t) -> conflict
       *
       * -> shift = clz(t) - clz(s)
       *      -> if t = 0 choose shift <= res < ones
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
         * x...x >> x = 0...0
         * -> choose random shift <= res <= ones
         */
        ones = bzla_bv_ones(mm, bw);
        tmp  = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
        res  = bzla_bv_new_random_range(mm, bzla->rng, bw, tmp, ones);
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
      bzla_bv_set_bit(res, i, bzla_rng_pick_rand(bzla->rng, 0, 1));
    }
  }
  return res;
}

BzlaBitVector *
bzla_proputils_inv_srl(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_srl, bzla_is_inv_srl_const, true);
#endif
  BzlaBitVector *res;
  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);
  res = inv_srl_aux(bzla, pi);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_srl, pi, res, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: sra                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sra(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_sra, bzla_is_inv_sra_const, true);
#endif
  bool is_signed;
  int32_t pos_x;
  uint32_t bw, i, cnt_s, cnt_t, shift;
  BzlaBitVector *res, *ones, *tmp;
  BzlaMemMgr *mm;
  const BzlaBitVector *s, *t;

  mm = bzla->mm;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_sra);

  res   = 0;
  pos_x = pi->pos_x;
  s     = pi->bv[1 - pi->pos_x];
  t     = pi->target_value;
  bw    = bzla_bv_get_width(t);

  /* ------------------------------------------------------------------------
   * s >>a x = t
   *
   * -> determine shift value via zero/one MSBs in t
   *    (considering zero/one MSBs in s)
   * ------------------------------------------------------------------------ */
  if (pos_x)
  {
    if (bzla_bv_get_bit(s, bw - 1) == 0)
    {
      res = inv_srl_aux(bzla, pi);
    }
    else
    {
      if (bzla_bv_is_ones(s) && bzla_bv_is_ones(t))
      {
        /* 1...1 >>a x = 1...1 -> choose random res */
        res = bzla_bv_new_random(mm, bzla->rng, bw);
      }
      else
      {
        cnt_t = bzla_bv_get_num_leading_ones(t);
        cnt_s = bzla_bv_get_num_leading_ones(s);
        assert(cnt_s <= cnt_t);
        /**
         * shift = clo(t) - clo(s)
         *   -> if t = ones choose shift <= res < bw
         *   -> else res = shift
         */
        shift = cnt_t - cnt_s;
        if (bzla_bv_is_ones(t))
        {
          /**
           * x...x >>a x = 1...1
           * -> choose random shift <= res <= ones
           */
          ones = bzla_bv_ones(mm, bw);
          tmp  = bzla_bv_uint64_to_bv(mm, (uint64_t) shift, bw);
          res  = bzla_bv_new_random_range(mm, bzla->rng, bw, tmp, ones);
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
  }
  /* ------------------------------------------------------------------------
   * x >>a s = t
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

    is_signed = bzla_bv_get_bit(t, bw - 1) == 1;
    cnt_t     = is_signed ? bzla_bv_get_num_leading_ones(t)
                      : bzla_bv_get_num_leading_zeros(t);
    assert((shift >= bw || cnt_t >= shift) && (shift < bw || cnt_t == bw));

    res = bzla_bv_sll(mm, t, s);
    for (i = 0; i < shift && i < bw; i++)
    {
      if (i == bw - 1)
      {
        if (shift > 0 && is_signed)
        {
          bzla_bv_set_bit(res, i, 1);
        }
      }
      else
      {
        bzla_bv_set_bit(res, i, bzla_rng_pick_rand(bzla->rng, 0, 1));
      }
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_sra, pi, res, ">>a");
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
    res = bzla_bv_new_random(mm, bzla->rng, bw);
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
          bzla_bv_set_bit(res, bw - 1 - i, bzla_rng_pick_rand(bzla->rng, 0, 1));
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
          bzla_bv_set_bit(res, bw - 1 - i, bzla_rng_pick_rand(bzla->rng, 0, 1));
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

  rng   = bzla->rng;
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
      if (!bzla_bv_compare(s, t) && bzla_rng_pick_with_prob(bzla->rng, 500))
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
            mm, bzla->rng, bzla_bv_get_width(s), lo, up);

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

        if (bzla_rng_pick_with_prob(bzla->rng, 250))
        {
          /* choose x = 0 with prob = 0.25 */
          res = bzla_bv_zero(mm, bw);
        }
        else
        {
          /* t < res <= 2^bw - 1 */
          tmp = bzla_bv_add(mm, t, one);
          res = bzla_bv_new_random_range(mm, bzla->rng, bw, tmp, ones);
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
        if (bzla_rng_pick_with_prob(bzla->rng, 500))
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
            n   = bzla_bv_new_random_range(mm, bzla->rng, bw, one, n_hi);
            tmp = bzla_bv_urem(mm, sub, n);
            for (cnt = 0; cnt < bw && !bzla_bv_is_zero(tmp); cnt++)
            {
              bzla_bv_free(mm, n);
              bzla_bv_free(mm, tmp);
              n   = bzla_bv_new_random_range(mm, bzla->rng, bw, one, n_hi);
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

      if (bzla_rng_pick_with_prob(bzla->rng, 500))
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
          n   = bzla_bv_new_random_range(mm, bzla->rng, bw, one, tmp);

          while (bzla_bv_is_umulo(mm, s, n))
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_sub(mm, n, one);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, bzla->rng, bw, one, tmp);
          }

          mul  = bzla_bv_mul(mm, s, n);
          tmp2 = bzla_bv_sub(mm, ones, mul);

          /* choose n s.t. addition in s * n + t does not overflow */
          while (bzla_bv_compare(tmp2, t) < 0)
          {
            bzla_bv_free(mm, tmp);
            tmp = bzla_bv_dec(mm, n);
            bzla_bv_free(mm, n);
            n = bzla_bv_new_random_range(mm, bzla->rng, bw, one, tmp);
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
      bzla->rng, bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP));

  bkeep = bflip ? true
                : bzla_rng_pick_with_prob(
                    bzla->rng,
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
        bkeep ? bzla_bv_get_bit(x, i) : bzla_rng_pick_rand(bzla->rng, 0, 1));

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
        bkeep ? bzla_bv_get_bit(x, i) : bzla_rng_pick_rand(bzla->rng, 0, 1));

  if (bflip)
  {
    rboth  = 0;
    rupper = bw_x - 1;
    rlower = 0;

    if (lower)
    {
      rboth += 1;
      rlower = bzla_rng_pick_rand(bzla->rng, 0, lower - 1);
    }

    if (upper + 1 < bw_x)
    {
      rboth += 2;
      rupper = bzla_rng_pick_rand(bzla->rng, upper + 1, bw_x - 1);
    }

    switch (rboth)
    {
      case 3:
        assert(rupper >= upper + 1 && rupper < bw_x);
        assert(rlower < lower);
        bzla_bv_flip_bit(
            res, bzla_rng_pick_with_prob(bzla->rng, 500) ? rupper : rlower);
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

/* -------------------------------------------------------------------------- */
/* INV: sext                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sext(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_sext, bzla_is_inv_sext_const, false);
#endif
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
      res = bzla_rng_flip_coin(bzla->rng) ? bzla_bv_one(mm, 1)
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

  mm = bzla->mm;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    BzlaBitVector *tmp = bzla_bv_add(mm, pi->bv[1 - pi->pos_x], x->lo);
    assert(bzla_bv_compare(tmp, pi->target_value) == 0);
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
  BzlaBitVector *res;
  const BzlaBvDomain *x;

  mm = bzla->mm;
  x  = pi->bvd[pi->pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    const BzlaBitVector *s = pi->bv[1 - pi->pos_x];
    const BzlaBitVector *t = pi->target_value;
    BzlaBitVector *tmp     = bzla_bv_and(mm, s, x->lo);
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
/* INV: xor                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_xor_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_xor, bzla_is_inv_xor_const, true);
#endif
  record_cons_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_xor);
  return bzla_proputils_inv_xor(bzla, pi);
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
  BzlaBitVector *res;
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
    BzlaBitVector *tmp = bzla_bv_eq(mm, s, x->lo);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_eq);
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (bzla_bv_is_zero(t))
  {
    bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
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
  int32_t pos_x;
  BzlaBitVector *res, *min, *max;
  BzlaMemMgr *mm;
  const BzlaBvDomain *x;
  BzlaBvDomainGenerator gen;

  mm = bzla->mm;

  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);

  res = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    const BzlaBitVector *s, *t;
    s = pi->bv[1 - pos_x];
    t = pi->target_value;
    BzlaBitVector *tmp =
        pos_x ? bzla_bv_ult(mm, s, x->lo) : bzla_bv_ult(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_ult);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    compute_ineq_bounds(bzla, pi, &min, &max);

    if (min && max)
    {
      if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT))
      {
        res = inv_ult_concat(bzla, pi, true);
        /* Result not in range min <= res <= max */
        if (res
            && (bzla_bv_compare(min, res) > 0 || bzla_bv_compare(res, max) > 0))
        {
          bzla_bv_free(mm, res);
          res = 0;
        }
      }

      if (!res)
      {
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, min, max);
        if (bzla_bvdomain_gen_has_next(&gen))
        {
          res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
        }
        bzla_bvdomain_gen_delete(&gen);
      }

      bzla_bv_free(mm, min);
      bzla_bv_free(mm, max);
    }

    if (!res)
    {
      /* conflict */
      return 0;
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_ult, pi, res, "<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: slt                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_slt_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_slt, bzla_is_inv_slt_const, false);
#endif
  bool conflict = false;
  int32_t pos_x;
  BzlaBitVector *res, *min, *max;
  BzlaMemMgr *mm;
  const BzlaBvDomain *x;
  BzlaBvDomainSignedGenerator gen;

  mm = bzla->mm;

  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_slt);

  res = 0;
  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    const BzlaBitVector *s, *t;
    s = pi->bv[1 - pos_x];
    t = pi->target_value;
    BzlaBitVector *tmp =
        pos_x ? bzla_bv_slt(mm, s, x->lo) : bzla_bv_slt(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_slt);
    res = bzla_bv_copy(mm, x->lo);
  }
  else
  {
    compute_ineq_bounds(bzla, pi, &min, &max);

    if (min && max)
    {
      if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT))
      {
        res = inv_slt_concat(bzla, pi, true, &conflict);
        if (conflict)
        {
          bzla_bv_free(mm, min);
          bzla_bv_free(mm, max);
          return 0;
        }
        /* Result not in range min <= res <= max */
        if (res
            && (bzla_bv_signed_compare(min, res) > 0
                || bzla_bv_signed_compare(res, max) > 0))
        {
          bzla_bv_free(mm, res);
          res = 0;
        }
      }

      if (!res)
      {
        bzla_bvdomain_gen_signed_init_range(mm, bzla->rng, &gen, x, min, max);
        if (bzla_bvdomain_gen_signed_has_next(&gen))
        {
          res = bzla_bv_copy(mm, bzla_bvdomain_gen_signed_random(&gen));
        }
        bzla_bvdomain_gen_signed_delete(&gen);
      }

      bzla_bv_free(mm, min);
      bzla_bv_free(mm, max);
    }

    if (!res)
    {
      /* conflict */
      return 0;
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_slt, pi, res, "<s");
#endif
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
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  res   = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    BzlaBitVector *tmp;
    const BzlaBitVector *s, *t;
    s   = pi->bv[1 - pos_x];
    t   = pi->target_value;
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
    res = bzla_bv_copy(mm, pi->res_x->lo);
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

static BzlaBitVector *
inv_srl_const_aux(Bzla *bzla, BzlaPropInfo *pi)
{
  int32_t pos_x;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm    = bzla->mm;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];
  res   = 0;

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    BzlaBitVector *tmp;
    const BzlaBitVector *s, *t;
    s   = pi->bv[1 - pos_x];
    t   = pi->target_value;
    tmp = pos_x ? bzla_bv_srl(mm, s, x->lo) : bzla_bv_srl(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pos_x)
  {
    assert(pi->res_x);
    assert(bzla_bvdomain_is_fixed(mm, pi->res_x));
    res = bzla_bv_copy(mm, pi->res_x->lo);
  }
  else
  {
    assert(pi->res_x == 0);
    res = inv_srl_aux(bzla, pi);
    set_const_bits(mm, x, &res);
  }
  return res;
}

BzlaBitVector *
bzla_proputils_inv_srl_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(pi->pos_x || pi->res_x == 0);
  assert(!pi->pos_x || pi->res_x);
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_srl, bzla_is_inv_srl_const, true);
#endif
  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_srl);
  BzlaBitVector *res = inv_srl_const_aux(bzla, pi);
#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_srl, pi, res, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: sra                                                                   */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sra_const(Bzla *bzla, BzlaPropInfo *pi)
{
#ifndef NDEBUG
  check_inv_dbg(bzla, pi, bzla_is_inv_sra, bzla_is_inv_sra_const, true);
#endif
  int32_t pos_x;
  BzlaBitVector *res;
  const BzlaBvDomain *x;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  res   = 0;
  pos_x = pi->pos_x;
  x     = pi->bvd[pos_x];

  if (bzla_bvdomain_is_fixed(mm, x))
  {
#ifndef NDEBUG
    BzlaBitVector *tmp;
    const BzlaBitVector *s, *t;
    s   = pi->bv[1 - pi->pos_x];
    t   = pi->target_value;
    tmp = pos_x ? bzla_bv_sra(mm, s, x->lo) : bzla_bv_sra(mm, x->lo, s);
    assert(bzla_bv_compare(tmp, t) == 0);
    bzla_bv_free(mm, tmp);
#endif
    res = bzla_bv_copy(mm, x->lo);
  }
  else if (pos_x)
  {
    assert(pi->res_x);
    assert(bzla_bvdomain_is_fixed(mm, pi->res_x));
    res = bzla_bv_copy(mm, pi->res_x->lo);
  }
  else
  {
    res = bzla_proputils_inv_sra(bzla, pi);
    set_const_bits(mm, x, &res);
  }

#ifndef NDEBUG
  check_result_binary_dbg(bzla, bzla_bv_sra, pi, res, ">>a");
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
  BzlaBitVector *res;
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
    BzlaBitVector *tmp = bzla_bv_mul(mm, s, x->lo);
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
      BzlaBitVector *tmp = bzla_bv_mul(mm, s, pi->res_x->lo);
      assert(bzla_bv_compare(tmp, t) == 0);
      bzla_bv_free(mm, tmp);
#endif
      res = bzla_bv_copy(mm, pi->res_x->lo);
    }
    else
    {
      res = bzla_bv_new_random(mm, bzla->rng, bzla_bv_get_width(t));
      set_const_bits(mm, pi->res_x, &res);
    }
  }
  else
  {
    if (bzla_bv_is_zero(s))
    {
      record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_mul);

      res = bzla_bv_new_random(mm, bzla->rng, bzla_bv_get_width(t));
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
          mm, bzla->rng, &gen, x, pi->res_x->lo, pi->res_x->hi);
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
          bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, tmp);
          bzla_bv_free(mm, tmp);
        }
        else
        {
          /* x > 0 */
          tmp = bzla_bv_one(mm, bw);
          bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, 0);
          bzla_bv_free(mm, tmp);
        }
      }
      else
      {
        /* x random */
        bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
      }
    }
    else
    {
      assert(bzla_bv_is_zero(t));
      if (pos_x)
      {
        /* x > s */
        tmp = bzla_bv_inc(mm, s);
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, 0);
        bzla_bv_free(mm, tmp);
      }
      else
      {
        /* x < s */
        tmp = bzla_bv_dec(mm, s);
        bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, 0, tmp);
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
            || (bzla_bv_is_zero(x->lo) && bzla_rng_flip_coin(bzla->rng)))
        {
          res = bzla_bv_zero(mm, bw);
        }
        else
        {
          BzlaBvDomainGenerator gen;
          res = 0;
          tmp = bzla_bv_inc(mm, t);
          bzla_bvdomain_gen_init_range(mm, bzla->rng, &gen, x, tmp, 0);
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
            && bzla_rng_flip_coin(bzla->rng))
        {
          /* special case: s % x = 0: one is a simple solution */
          res = bzla_bv_copy(mm, one);
        }
        else
        {
          simple = bzla_bv_sub(mm, s, t); /* simplest solution: s - t */
          if (bzla_bvdomain_check_fixed_bits(mm, x, simple)
              && bzla_rng_flip_coin(bzla->rng))
          {
            res = simple;
          }
          else
          {
            /* try to find some other factor within 10k iterations, else fall
             * back to using the simple solution */
            res = bzla_bvdomain_get_factor(mm, simple, x, t, 10000, bzla->rng);
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
                  && (!res || bzla_rng_flip_coin(bzla->rng)))
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
            && bzla_rng_flip_coin(bzla->rng)))
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
            mm, bzla->rng, &gen, x, pi->res_x->lo, pi->res_x->hi);
      }
      else
      {
        res = bzla_bv_copy(mm, t);
        bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
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

  x = pi->bvd[0];
  assert(bzla_is_inv_slice_const(bzla, pi));

  res = bzla_proputils_inv_slice(bzla, pi);
  set_const_bits(bzla->mm, x, &res);
#ifndef NDEBUG
  const BzlaBitVector *t = pi->target_value;
  uint32_t upper         = bzla_node_bv_slice_get_upper(pi->exp);
  uint32_t lower         = bzla_node_bv_slice_get_lower(pi->exp);
  BzlaMemMgr *mm         = bzla->mm;
  BzlaBitVector *tmpdbg  = bzla_bv_slice(mm, res, upper, lower);
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
/* INV: sext                                                                  */
/* -------------------------------------------------------------------------- */

BzlaBitVector *
bzla_proputils_inv_sext_const(Bzla *bzla, BzlaPropInfo *pi)
{
  assert(pi->res_x);
  return bzla_bv_copy(bzla->mm, pi->res_x->lo);
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
  BzlaBitVector *res;
  const BzlaBvDomain *x;

  record_inv_stats(bzla, &BZLA_PROP_SOLVER(bzla)->stats.inv_cond);

  mm    = bzla->mm;
  pos_x = pi->pos_x;
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
    BzlaBitVector *tmp;
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
    assert(bzla_bv_compare(tmp, pi->target_value) == 0);
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
    bzla_bvdomain_gen_init(mm, bzla->rng, &gen, x);
    assert(bzla_bvdomain_gen_has_next(&gen));
    res = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
    bzla_bvdomain_gen_delete(&gen);
  }
#ifndef NDEBUG
  char *str_res = bzla_bv_to_char(mm, res);
  char *str_t   = bzla_bv_to_char(bzla->mm, pi->target_value);
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

#if 0
static BzlaPropSelectPath kind_to_select_path[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = select_path_add,
    [BZLA_BV_AND_NODE]    = select_path_and,
    [BZLA_BV_CONCAT_NODE] = select_path_concat,
    [BZLA_BV_EQ_NODE]     = select_path_eq,
    [BZLA_BV_MUL_NODE]    = select_path_mul,
    [BZLA_BV_ULT_NODE]    = select_path_ult,
    [BZLA_BV_SLICE_NODE]  = select_path_slice,
    [BZLA_BV_SLL_NODE]    = select_path_sll,
    [BZLA_BV_SLT_NODE]    = select_path_slt,
    [BZLA_BV_SRL_NODE]    = select_path_srl,
    [BZLA_BV_UDIV_NODE]   = select_path_udiv,
    [BZLA_BV_UREM_NODE]   = select_path_urem,
    [BZLA_COND_NODE]      = select_path_cond,
};
#endif

static BzlaPropComputeValueFun kind_to_cons[BZLA_NUM_OPS_NODE] = {
    [BZLA_BV_ADD_NODE]    = bzla_proputils_cons_add,
    [BZLA_BV_AND_NODE]    = bzla_proputils_cons_and,
    [BZLA_BV_CONCAT_NODE] = bzla_proputils_cons_concat,
    [BZLA_BV_EQ_NODE]     = bzla_proputils_cons_eq,
    [BZLA_BV_MUL_NODE]    = bzla_proputils_cons_mul,
    [BZLA_BV_ULT_NODE]    = bzla_proputils_cons_ult,
    [BZLA_BV_SLICE_NODE]  = bzla_proputils_cons_slice,
    [BZLA_BV_SLL_NODE]    = bzla_proputils_cons_sll,
    [BZLA_BV_SLT_NODE]    = bzla_proputils_cons_slt,
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
    [BZLA_BV_SLT_NODE]    = bzla_proputils_cons_slt_const,
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
    [BZLA_BV_SLT_NODE]    = bzla_proputils_inv_slt,
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
    [BZLA_BV_SLT_NODE]    = bzla_proputils_inv_slt_const,
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
    [BZLA_BV_SLT_NODE]    = bzla_is_inv_slt,
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
    [BZLA_BV_SLT_NODE]    = bzla_is_inv_slt_const,
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
  bool is_sra, is_xor;
  uint32_t idx_s = 0;
  BzlaNode *children[2];

  mm = bzla->mm;

  if ((is_sra = bzla_is_bv_sra(bzla, exp, &children[0], &children[1])))
  {
    assert(children[0]);
    assert(children[1]);
    if (exp->arity > 1)
    {
      idx_s = idx_x ? 0 : 1;
    }
    is_recoverable = !bzla_node_is_bv_const(children[idx_s]);
  }
  else if ((is_xor = bzla_is_bv_xor(bzla, exp, &children[0], &children[1])))
  {
    assert(children[0]);
    assert(children[1]);
    if (exp->arity > 1)
    {
      idx_s = idx_x ? 0 : 1;
    }
    is_recoverable = !bzla_node_is_bv_const(children[idx_s]);
  }
  else if (bzla_node_is_cond(exp))
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
  if (is_sra)
  {
    assert(s[0]);
    assert(s[1]);
    BZLALOG(2, "");
    str_s0 = bzla_bv_to_char(mm, s[idx_s]);
    if (idx_x == 0)
    {
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := x >>a %s",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0);
    }
    else
    {
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := %s >>a x",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0);
    }
    bzla_mem_freestr(mm, str_s0);
  }
  else if (is_xor)
  {
    assert(s[0]);
    assert(s[1]);
    BZLALOG(2, "");
    str_s0 = bzla_bv_to_char(mm, s[idx_s]);
    if (idx_x == 0)
    {
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := x ^ %s",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0);
    }
    else
    {
      BZLALOG(2,
              "%srecoverable CONFLICT (@%d): %s := %s ^ x",
              is_recoverable ? "" : "non-",
              bzla_node_get_id(exp),
              str_t,
              str_s0);
    }
    bzla_mem_freestr(mm, str_s0);
  }
  else if (bzla_node_is_cond(exp))
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
      case BZLA_BV_SLT_NODE: str_o = "<s"; break;
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
            prop.idx_x = bzla_rng_flip_coin(bzla->rng) ? 1 : 2;
          }
          else if (idx_x == 1)
          {
            prop.idx_x = bzla_rng_flip_coin(bzla->rng) ? 0 : 2;
          }
          else
          {
            prop.idx_x = bzla_rng_flip_coin(bzla->rng) ? 0 : 1;
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
                                int32_t pos_x,
                                BzlaNode **input,
                                BzlaBitVector **assignment)
{
  assert(bzla);
  assert(root);
  assert(bvroot);

  bool is_inv, pick_inv, pick_rand, has_fixed_bits;
  bool opt_prop_xor, opt_prop_sext, opt_prop_sra;
  int32_t i, arity, nconst;
  uint64_t nprops;
  BzlaNode *cur, *real_cur;
  BzlaIntHashTable *domains;
  BzlaHashTableData *d;
  BzlaBitVector *bv_s[BZLA_NODE_MAX_CHILDREN] = {0, 0, 0};
  BzlaBitVector *bv_t, *bv_s_new, *tmp;
  BzlaMemMgr *mm;
  uint32_t opt_prop_prob_use_inv_value, opt_prop_prob_fallback_rand_value;
  uint32_t opt_prop_const_bits, opt_prop_prob_random_input;
  bool opt_skip_no_progress;
  bool is_sext, is_xor, is_sra;
  BzlaPropInfo pi;
  BzlaNode **children = 0, *tmp_children[2];
  BzlaBvDomainGenerator gen;

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
  opt_prop_prob_fallback_rand_value =
      bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE);
  opt_prop_prob_random_input =
      bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_RANDOM_INPUT);
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS);
  opt_skip_no_progress =
      bzla_opt_get(bzla, BZLA_OPT_PROP_SKIP_NO_PROGRESS) != 0;
  opt_prop_xor  = bzla_opt_get(bzla, BZLA_OPT_PROP_XOR);
  opt_prop_sext = bzla_opt_get(bzla, BZLA_OPT_PROP_SEXT);
  opt_prop_sra  = bzla_opt_get(bzla, BZLA_OPT_PROP_ASHR);

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

    if (bzla_lsutils_is_leaf_node(cur))
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

      /* check if expression is a sign extension (if enabled) */
      is_sext = false;
      if (opt_prop_sext)
      {
        is_sext = bzla_is_bv_sext(bzla, real_cur);
      }

      /* check if expression is an xor (if enabled) */
      is_xor = false;
      if (opt_prop_xor && !is_sext)
      {
        tmp_children[0] = 0;
        tmp_children[1] = 0;
        is_xor =
            bzla_is_bv_xor(bzla, real_cur, &tmp_children[0], &tmp_children[1]);
      }

      /* check if expression is an arithmetic right shift (if enabled) */
      is_sra = false;
      if (opt_prop_sra && !is_sext && !is_xor)
      {
        tmp_children[0] = 0;
        tmp_children[1] = 0;
        is_sra =
            bzla_is_bv_sra(bzla, real_cur, &tmp_children[0], &tmp_children[1]);
      }

      if (is_xor || is_sra)
      {
        arity    = 2;
        children = tmp_children;
      }
      else
      {
        arity    = real_cur->arity;
        children = real_cur->e;
      }

      /* check if all paths are const, if yes -> conflict */
      for (i = 0, nconst = 0; i < arity; i++)
      {
        bv_s[i]  = (BzlaBitVector *) bzla_model_get_bv(bzla, children[i]);
        pi.bv[i] = bv_s[i];
        if (bzla_node_is_bv_const(children[i])) nconst += 1;
      }

      if (nconst > arity - 1) break;

      /* additionally, for ite, if condition and enabled branch are const
       * -> conflict */
      if (bzla_node_is_cond(real_cur) && bzla_node_is_bv_const(children[0])
          && (bzla_node_is_bv_const(real_cur == bzla->true_exp ? children[1]
                                                               : children[2])))
      {
        break;
      }

#ifndef NBZLALOG
      a = bzla_bv_to_char(bzla->mm, bv_t);
      BZLALOG(2, "");
      BZLALOG(2, "propagate: %s", a);
      bzla_mem_freestr(bzla->mm, a);
#endif

      pi.exp          = real_cur;
      pi.res_x        = 0;
      pi.target_value = bv_t;

      /* Initialize domains. */
      if (opt_prop_const_bits)
      {
        assert(domains);
        for (i = 0; i < arity; ++i)
        {
          d = bzla_hashint_map_get(domains, bzla_node_get_id(children[i]));
          assert(d);
          assert(d->as_ptr);
          pi.bvd[i] = d->as_ptr;
        }
      }

      /* select path */
      if (is_sext)
      {
        pi.pos_x = pos_x = 1;
      }
      else if (is_xor)
      {
        pos_x = select_path_aux(
            bzla,
            &pi,
            opt_prop_const_bits ? bzla_is_ess_xor_const : bzla_is_ess_xor,
            children[0],
            children[1]);
      }
      else if (is_sra)
      {
        pos_x = select_path_aux(
            bzla,
            &pi,
            opt_prop_const_bits ? bzla_is_ess_sra_const : bzla_is_ess_sra,
            children[0],
            children[1]);
      }
      else if (bzla_node_is_cond(real_cur))
      {
        pos_x = select_path_cond(bzla, &pi);
      }
      else
      {
        pos_x = select_path(bzla, &pi, opt_prop_const_bits);
      }

      if (!is_sext && nconst == 0
          && bzla_rng_pick_with_prob(bzla->rng, opt_prop_prob_random_input))
      {
        pi.pos_x = pos_x = select_path_random(bzla, pi.exp);
      }
      assert(pi.pos_x == pos_x);

      assert(pos_x >= 0);
      assert(pos_x < arity);

#ifndef NDEBUG
      if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
      {
        BzlaPropEntailInfo prop = {
            real_cur, bzla_bv_copy(bzla->mm, bv_t), pos_x};
        BZLA_PUSH_STACK(BZLA_PROP_SOLVER(bzla)->prop_path, prop);
      }
#endif

      has_fixed_bits = false;
      if (opt_prop_const_bits)
      {
        has_fixed_bits = bzla_bvdomain_has_fixed_bits(mm, pi.bvd[pos_x]);
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
          is_inv_fun     = bzla_is_inv_sext_const;
          cons_value_fun = bzla_proputils_cons_sext_const;
          inv_value_fun  = bzla_proputils_inv_sext_const;
        }
        else if (is_xor)
        {
          is_inv_fun     = bzla_is_inv_xor_const;
          cons_value_fun = bzla_proputils_cons_xor_const;
          inv_value_fun  = bzla_proputils_inv_xor_const;
        }
        else if (is_sra)
        {
          is_inv_fun     = bzla_is_inv_sra_const;
          cons_value_fun = bzla_proputils_cons_sra_const;
          inv_value_fun  = bzla_proputils_inv_sra_const;
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
          is_inv_fun     = bzla_is_inv_sext;
          cons_value_fun = bzla_proputils_cons_sext;
          inv_value_fun  = bzla_proputils_inv_sext;
        }
        else if (is_xor)
        {
          is_inv_fun     = bzla_is_inv_xor;
          cons_value_fun = bzla_proputils_cons_xor;
          inv_value_fun  = bzla_proputils_inv_xor;
        }
        else if (is_sra)
        {
          is_inv_fun     = bzla_is_inv_sra;
          cons_value_fun = bzla_proputils_cons_sra;
          inv_value_fun  = bzla_proputils_inv_sra;
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
          bzla_rng_pick_with_prob(bzla->rng, opt_prop_prob_use_inv_value);
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
        if (opt_prop_const_bits && opt_prop_prob_fallback_rand_value)
        {
          assert(bzla_bvdomain_has_fixed_bits(mm, pi.bvd[pi.pos_x]));
          pick_rand = bzla_rng_pick_with_prob(
              bzla->rng, opt_prop_prob_fallback_rand_value);
          if (pick_rand)
          {
            bzla_bvdomain_gen_init(mm, bzla->rng, &gen, pi.bvd[pi.pos_x]);
            if (bzla_bvdomain_gen_has_next(&gen))
            {
              bv_s_new = bzla_bv_copy(mm, bzla_bvdomain_gen_random(&gen));
            }
            bzla_bvdomain_gen_delete(&gen);
          }
        }

        if (!bv_s_new)
        {
          break;
        }
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
      cur  = children[pos_x];
#ifndef NDEBUG
      if (bzla_hashint_map_contains(domains, bzla_node_get_id(cur)))
      {
        assert(bzla_hashint_map_get(domains, bzla_node_get_id(cur)));
        assert(bzla_bvdomain_check_fixed_bits(
            bzla->mm,
            bzla_hashint_map_get(domains, bzla_node_get_id(cur))->as_ptr,
            bv_t));
      }
#endif

      nprops += 1;
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
