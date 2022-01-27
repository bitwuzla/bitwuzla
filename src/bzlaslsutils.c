/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaslsutils.h"

#include "bzlabv.h"
#include "bzlalog.h"
#include "bzlalsutils.h"
#include "bzlamodel.h"
#include "bzlanode.h"
#include "utils/bzlautil.h"

#define BZLA_SLS_SCORE_CFACT 0.5     /* same as in Z3 (c1) */
#define BZLA_SLS_SCORE_F_CFACT 0.025 /* same as in Z3 (c3) */

/* ==========================================================================
 * SLS score computation
 * ==========================================================================
 *
 *  A(x) .... current assignment of expression x
 *
 *  Boolean variable:
 *  -----------------
 *    score (e) = A(e)
 *
 *  Bit-width bw >= 1:
 *  ------------------
 *
 *    score (e0_[bw] /\ e1_[bw]) =
 *        1/2 * (score (e0) + score (e1))
 *
 *    score (-(-e0_[bw] /\ ... /\ -e1_[bw])) =
 *        max (score (-e0), score (-e1))
 *
 *    score (e0_[bw] = e1_[bw]) =
 *        (A(e0) == A(e1))
 *        ? 1.0
 *        : c1 * (1 - (h (A(e0), A(e1)) / bw)
 *
 *    score (e0_[bw] != e1_[bw]) =
 *        (A (e0) == A (e1)
 *        ? 0.0
 *        : 1.0
 *
 *    s (e0[bw] < e1[bw]) =
 *        (A(e0) < A(e1))
 *        ? 1.0
 *        : c1 * (1 - (min number of bits to flip s.t. e0 < e1) / bw)
 *
 * ========================================================================== */

static uint32_t
hamming_distance(Bzla *bzla, BzlaBitVector *bv1, BzlaBitVector *bv2)
{
  assert(bv1);
  assert(bv2);
  assert(bzla_bv_get_width(bv1) == bzla_bv_get_width(bv2));

  uint32_t res, bw;
  BzlaBitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  bw   = bzla_bv_get_width(bv1);
  zero = bzla_bv_new(bzla->mm, bw);
  ones = bzla_bv_ones(bzla->mm, bw);
  bv   = bzla_bv_xor(bzla->mm, bv1, bv2);
  for (res = 0; !bzla_bv_is_zero(bv); res++)
  {
    bvdec = bzla_bv_add(bzla->mm, bv, ones);
    tmp   = bv;
    bv    = bzla_bv_and(bzla->mm, bv, bvdec);
    bzla_bv_free(bzla->mm, tmp);
    bzla_bv_free(bzla->mm, bvdec);
  }
  bzla_bv_free(bzla->mm, bv);
  bzla_bv_free(bzla->mm, ones);
  bzla_bv_free(bzla->mm, zero);
  return res;
}

// TODO find a better heuristic this might be too expensive
// this is not necessarily the actual minimum, but the minimum if you flip
// bits in bv1 s.t. bv1 < bv2 (if bv2 is 0, we need to flip 1 bit in bv2, too,
// which we do not consider to prevent negative scores)
static uint32_t
min_flip(Bzla *bzla, BzlaBitVector *bv1, BzlaBitVector *bv2)
{
  assert(bv1);
  assert(bv2);
  assert(bzla_bv_get_width(bv1) == bzla_bv_get_width(bv2));

  uint32_t i, j, res, bw;
  BzlaBitVector *tmp;

  if (bzla_bv_is_zero(bv2))
    res = hamming_distance(bzla, bv1, bv2);
  else
  {
    tmp = bzla_bv_copy(bzla->mm, bv1);
    bw  = bzla_bv_get_width(tmp);
    for (res = 0, i = 0, j = bw - 1; i < bw; i++, j--)
    {
      if (!bzla_bv_get_bit(tmp, j)) continue;
      res += 1;
      bzla_bv_set_bit(tmp, j, 0);
      if (bzla_bv_compare(tmp, bv2) < 0) break;
    }
    if (bzla_bv_is_zero(bv2)) res += 1;
    bzla_bv_free(bzla->mm, tmp);
  }
  assert(res <= bzla_bv_get_width(bv1));
  return res;
}

static uint32_t
min_flip_inv(Bzla *bzla, BzlaBitVector *bv1, BzlaBitVector *bv2)
{
  assert(bv1);
  assert(bv2);
  assert(bzla_bv_get_width(bv1) == bzla_bv_get_width(bv2));

  uint32_t i, j, res, bw;
  BzlaBitVector *tmp;

  tmp = bzla_bv_copy(bzla->mm, bv1);
  bw  = bzla_bv_get_width(tmp);
  for (res = 0, i = 0, j = bw - 1; i < bw; i++, j--)
  {
    if (bzla_bv_get_bit(tmp, j)) continue;
    res += 1;
    bzla_bv_set_bit(tmp, j, 1);
    if (bzla_bv_compare(tmp, bv2) >= 0) break;
  }
  bzla_bv_free(bzla->mm, tmp);
  return res;
}

double
bzla_slsutils_compute_score_node(Bzla *bzla,
                                 BzlaIntHashTable *bv_model,
                                 BzlaIntHashTable *fun_model,
                                 BzlaIntHashTable *score,
                                 BzlaNode *exp)
{
  assert(bzla);
  assert(bv_model);
  assert(fun_model);
  assert(score);
  assert(exp);
  assert(bzla_node_bv_get_width(bzla, exp) == 1);

  double res, s0, s1;
  BzlaNode *real_exp;
  BzlaBitVector *bv0, *bv1;
#ifndef NBZLALOG
  BzlaMemMgr *mm;
  char *a0, *a1;
  mm = bzla->mm;
#endif

  res      = 0.0;
  real_exp = bzla_node_real_addr(exp);

  BZLALOG(3, "");
  BZLALOG(3, "*** compute sls score for: %s", bzla_util_node2string(exp));

  if (bzla_node_is_bv_and(real_exp))
  {
    /* ---------------------------------------------------------------------- */
    /* OR                                                                     */
    /* ---------------------------------------------------------------------- */
    if (bzla_node_is_inverted(exp))
    {
      assert(bzla_hashint_map_contains(score,
                                       -bzla_node_get_id((real_exp->e[0]))));
      assert(bzla_hashint_map_contains(score,
                                       -bzla_node_get_id((real_exp->e[1]))));
      s0 = bzla_hashint_map_get(score, -bzla_node_get_id((real_exp->e[0])))
               ->as_dbl;
      s1 = bzla_hashint_map_get(score, -bzla_node_get_id((real_exp->e[1])))
               ->as_dbl;
#ifndef NBZLALOG
      if (bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL) >= 2)
      {
        a0 = bzla_bv_to_char(
            bzla->mm,
            bzla_model_get_bv_aux(
                bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[0])));
        a1 = bzla_bv_to_char(
            bzla->mm,
            bzla_model_get_bv_aux(
                bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[1])));
        BZLALOG(3, "      assignment e[0]: %s", a0);
        BZLALOG(3, "      assignment e[1]: %s", a1);
        bzla_mem_freestr(mm, a0);
        bzla_mem_freestr(mm, a1);
        BZLALOG(3, "      sls score e[0]: %f", s0);
        BZLALOG(3, "      sls score e[1]: %f", s1);
      }
#endif
      res = s0 > s1 ? s0 : s1;
    }
    /* ---------------------------------------------------------------------- */
    /* AND                                                                    */
    /* ---------------------------------------------------------------------- */
    else
    {
      assert(
          bzla_hashint_map_contains(score, bzla_node_get_id((real_exp->e[0]))));
      assert(
          bzla_hashint_map_contains(score, bzla_node_get_id((real_exp->e[1]))));
      s0 = bzla_hashint_map_get(score, bzla_node_get_id((real_exp->e[0])))
               ->as_dbl;
      s1 = bzla_hashint_map_get(score, bzla_node_get_id((real_exp->e[1])))
               ->as_dbl;
#ifndef NBZLALOG
      if (bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL) >= 2)
      {
        a0 = bzla_bv_to_char(
            bzla->mm,
            bzla_model_get_bv_aux(
                bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[0])));
        a1 = bzla_bv_to_char(
            bzla->mm,
            bzla_model_get_bv_aux(
                bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[1])));
        BZLALOG(3, "      assignment e[0]: %s", a0);
        BZLALOG(3, "      assignment e[1]: %s", a1);
        bzla_mem_freestr(mm, a0);
        bzla_mem_freestr(mm, a1);
        BZLALOG(3, "      sls score e[0]: %f", s0);
        BZLALOG(3, "      sls score e[1]: %f", s1);
      }
#endif
      res = (s0 + s1) / 2.0;
      /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
         choose minimum (else it might again result in 1.0) */
      if (res == 1.0 && (s0 < 1.0 || s1 < 1.0)) res = s0 < s1 ? s0 : s1;
    }
  }
  /* ------------------------------------------------------------------------ */
  /* EQ                                                                       */
  /* ------------------------------------------------------------------------ */
  else if (bzla_node_is_bv_eq(real_exp))
  {
    bv0 = (BzlaBitVector *) bzla_model_get_bv_aux(
        bzla, bv_model, fun_model, real_exp->e[0]);
    bv1 = (BzlaBitVector *) bzla_model_get_bv_aux(
        bzla, bv_model, fun_model, real_exp->e[1]);
#ifndef NBZLALOG
    if (bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL) >= 2)
    {
      a0 = bzla_bv_to_char(
          bzla->mm,
          bzla_model_get_bv_aux(
              bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[0])));
      a1 = bzla_bv_to_char(
          bzla->mm,
          bzla_model_get_bv_aux(
              bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[1])));
      BZLALOG(3, "      assignment e[0]: %s", a0);
      BZLALOG(3, "      assignment e[1]: %s", a1);
      bzla_mem_freestr(mm, a0);
      bzla_mem_freestr(mm, a1);
    }
#endif
    if (bzla_node_is_inverted(exp))
      res = !bzla_bv_compare(bv0, bv1) ? 0.0 : 1.0;
    else
      res = !bzla_bv_compare(bv0, bv1)
                ? 1.0
                : BZLA_SLS_SCORE_CFACT
                      * (1.0
                         - hamming_distance(bzla, bv0, bv1)
                               / (double) bzla_bv_get_width(bv0));
  }
  /* ------------------------------------------------------------------------ */
  /* ULT                                                                      */
  /* ------------------------------------------------------------------------ */
  else if (bzla_node_is_bv_ult(real_exp))
  {
    bv0 = (BzlaBitVector *) bzla_model_get_bv_aux(
        bzla, bv_model, fun_model, real_exp->e[0]);
    bv1 = (BzlaBitVector *) bzla_model_get_bv_aux(
        bzla, bv_model, fun_model, real_exp->e[1]);
#ifndef NBZLALOG
    if (bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL) >= 2)
    {
      a0 = bzla_bv_to_char(
          bzla->mm,
          bzla_model_get_bv_aux(
              bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[0])));
      a1 = bzla_bv_to_char(
          bzla->mm,
          bzla_model_get_bv_aux(
              bzla, bv_model, fun_model, bzla_node_invert(real_exp->e[1])));
      BZLALOG(3, "      assignment e[0]: %s", a0);
      BZLALOG(3, "      assignment e[1]: %s", a1);
      bzla_mem_freestr(mm, a0);
      bzla_mem_freestr(mm, a1);
    }
#endif
    if (bzla_node_is_inverted(exp))
      res = bzla_bv_compare(bv0, bv1) >= 0
                ? 1.0
                : BZLA_SLS_SCORE_CFACT
                      * (1.0
                         - min_flip_inv(bzla, bv0, bv1)
                               / (double) bzla_bv_get_width(bv0));
    else
      res = bzla_bv_compare(bv0, bv1) < 0
                ? 1.0
                : BZLA_SLS_SCORE_CFACT
                      * (1.0
                         - min_flip(bzla, bv0, bv1)
                               / (double) bzla_bv_get_width(bv0));
  }
  /* ------------------------------------------------------------------------ */
  /* other BOOLEAN                                                            */
  /* ------------------------------------------------------------------------ */
  else
  {
    assert(bzla_node_bv_get_width(bzla, real_exp) == 1);
#ifndef NBZLALOG
    if (bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL) >= 2)
    {
      a0 = bzla_bv_to_char(
          bzla->mm,
          bzla_model_get_bv_aux(
              bzla, bv_model, fun_model, bzla_node_invert(exp)));
      BZLALOG(3, "      assignment : %s", a0);
      bzla_mem_freestr(mm, a0);
    }
#endif
    res = bzla_bv_get_bit(((BzlaBitVector *) bzla_model_get_bv_aux(
                              bzla, bv_model, fun_model, exp)),
                          0);
  }

  BZLALOG(3, "      sls score : %f", res);
  assert(res >= 0.0 && res <= 1.0);
  return res;
}

static double
recursively_compute_sls_score_node(Bzla *bzla,
                                   BzlaIntHashTable *bv_model,
                                   BzlaIntHashTable *fun_model,
                                   BzlaIntHashTable *score,
                                   BzlaNode *exp)
{
  assert(bzla);
  assert(bv_model);
  assert(fun_model);
  assert(score);
  assert(exp);

  uint32_t i;
  double res;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack stack;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;

  res = 0.0;
  assert(bzla_node_is_bv_eq(exp) || bzla_node_is_bv_ult(exp)
         || bzla_node_bv_get_width(bzla, exp) == 1);

  if (bzla_hashint_map_contains(score, bzla_node_get_id(exp)))
    return bzla_hashint_map_get(score, bzla_node_get_id(exp))->as_dbl;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  mark = bzla_hashint_map_new(mm);

  BZLA_PUSH_STACK(stack, exp);
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = bzla_node_real_addr(cur);
    d        = bzla_hashint_map_get(mark, real_cur->id);

    if ((d && d->as_int == 1)
        || bzla_hashint_map_get(score, bzla_node_get_id(cur)))
      continue;

    if (!d)
    {
      bzla_hashint_map_add(mark, real_cur->id);
      BZLA_PUSH_STACK(stack, cur);

      if (!bzla_lsutils_is_leaf_node(real_cur))
      {
        for (i = 0; i < real_cur->arity; i++)
          BZLA_PUSH_STACK(stack, real_cur->e[i]);
      }
    }
    else
    {
      assert(d->as_int == 0);
      d->as_int = 1;

      if (bzla_node_bv_get_width(bzla, real_cur) != 1) continue;

      res = bzla_slsutils_compute_score_node(
          bzla, bv_model, fun_model, score, cur);

      assert(!bzla_hashint_map_contains(score, bzla_node_get_id(cur)));
      bzla_hashint_map_add(score, bzla_node_get_id(cur))->as_dbl = res;
    }
  }

  BZLA_RELEASE_STACK(stack);
  bzla_hashint_map_delete(mark);

  assert(bzla_hashint_map_contains(score, bzla_node_get_id(exp)));
  assert(res == bzla_hashint_map_get(score, bzla_node_get_id(exp))->as_dbl);
  return res;
}

/* -------------------------------------------------------------------------- */

void
bzla_slsutils_compute_sls_scores(Bzla *bzla,
                                 BzlaIntHashTable *bv_model,
                                 BzlaIntHashTable *fun_model,
                                 BzlaIntHashTable *score)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(bv_model);
  assert(fun_model);
  assert(score);

  uint32_t i;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack stack;
  BzlaPtrHashTableIterator pit;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;

  BZLALOG(3, "");
  BZLALOG(3, "**** compute sls scores ***");

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  mark = bzla_hashint_map_new(mm);

  /* collect roots */
  bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&pit))
    BZLA_PUSH_STACK(stack, bzla_iter_hashptr_next(&pit));

  /* compute score */
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = bzla_node_real_addr(cur);
    d        = bzla_hashint_map_get(mark, real_cur->id);

    if ((d && d->as_int == 1)
        || bzla_hashint_map_contains(score, bzla_node_get_id(cur)))
      continue;

    if (!d)
    {
      bzla_hashint_map_add(mark, real_cur->id);
      BZLA_PUSH_STACK(stack, cur);
      if (!bzla_lsutils_is_leaf_node(real_cur))
      {
        for (i = 0; i < real_cur->arity; i++)
          BZLA_PUSH_STACK(stack, real_cur->e[i]);
      }
    }
    else
    {
      assert(d->as_int == 0);
      d->as_int = 1;
      if (bzla_node_bv_get_width(bzla, real_cur) != 1) continue;
      (void) recursively_compute_sls_score_node(
          bzla, bv_model, fun_model, score, cur);
      (void) recursively_compute_sls_score_node(
          bzla, bv_model, fun_model, score, bzla_node_invert(cur));
    }
  }

  BZLA_RELEASE_STACK(stack);
  bzla_hashint_map_delete(mark);
}
