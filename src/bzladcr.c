/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlanode.h"
#include "bzlaslvfun.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

/* heuristic: minimum depth to the inputs
 *            (considering the whole formula or the bv skeleton, only) */
static void
compute_scores_aux_min_dep(Bzla *bzla, BzlaNodePtrStack *nodes)
{
  assert(bzla);
  assert(BZLA_FUN_SOLVER(bzla)->score);
  assert(nodes);

  uint32_t i, j;
  int32_t min_depth;
  BzlaFunSolver *slv;
  BzlaNodePtrStack stack;
  BzlaNode *cur, *e;
  BzlaPtrHashTable *score;
  BzlaPtrHashBucket *b;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);

  slv   = BZLA_FUN_SOLVER(bzla);
  score = slv->score;
  mark  = bzla_hashint_map_new(mm);

  for (j = 0; j < BZLA_COUNT_STACK(*nodes); j++)
  {
    cur = BZLA_PEEK_STACK(*nodes, j);
    BZLA_PUSH_STACK(stack, cur);
    while (!BZLA_EMPTY_STACK(stack))
    {
      cur = bzla_node_real_addr(BZLA_POP_STACK(stack));
      d   = bzla_hashint_map_get(mark, cur->id);

      if (d && d->as_int == 1) continue;

      if (!d)
      {
        d = bzla_hashint_map_add(mark, cur->id);
        BZLA_PUSH_STACK(stack, cur);

        if (cur->arity == 0)
        {
          if (!(b = bzla_hashptr_table_get(score, cur)))
            b = bzla_hashptr_table_add(score, bzla_node_copy(bzla, cur));
          b->data.as_int = 1;
          d->as_int      = 1;
          continue;
        }

        for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
      }
      else
      {
        assert(d->as_int == 0);
        assert(cur->arity > 0);
        assert(!bzla_node_is_uf(cur));
        d->as_int = 1;

        min_depth = -1;
        for (i = 0; i < cur->arity; i++)
        {
          e = bzla_node_real_addr(cur->e[i]);
          b = bzla_hashptr_table_get(score, e);
          assert(b);
          if (min_depth == -1 || b->data.as_int < min_depth)
            min_depth = b->data.as_int;
        }
        assert(min_depth >= 0);
        if (!(b = bzla_hashptr_table_get(score, cur)))
          b = bzla_hashptr_table_add(score, bzla_node_copy(bzla, cur));
        b->data.as_int = min_depth + 1;
      }
    }
  }

  BZLA_RELEASE_STACK(stack);
  bzla_hashint_map_delete(mark);
}

/* heuristic: minimum number of unique applies on a path to the inputs
 *            (considering the whole formula, or the bv skeleton only) */
static void
compute_scores_aux_min_app(Bzla *bzla, BzlaNodePtrStack *nodes)
{
  assert(bzla);
  assert(BZLA_FUN_SOLVER(bzla)->score);
  assert(nodes);

  double delta;
  uint32_t i, j, k;
  BzlaFunSolver *slv;
  BzlaNode *cur, *e;
  BzlaNodePtrStack stack;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTable *in, *t, *min_t;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);

  slv = BZLA_FUN_SOLVER(bzla);

  qsort(nodes->start,
        BZLA_COUNT_STACK(*nodes),
        sizeof(BzlaNode *),
        bzla_node_compare_by_id_qsort_asc);

  /* compute score */
  for (k = 0; k < BZLA_COUNT_STACK(*nodes); k++)
  {
    cur = BZLA_PEEK_STACK(*nodes, k);
    b   = bzla_hashptr_table_get(slv->score, cur);
    assert(b);
    assert(!b->data.as_ptr);
    b->data.as_ptr =
        bzla_hashptr_table_new(mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    in = b->data.as_ptr;

    if (!cur->parameterized && bzla_node_is_bv_and(cur))
    {
      /* choose min path */
      min_t = 0;
      for (i = 0; i < cur->arity; i++)
      {
        e = bzla_node_real_addr(cur->e[i]);
        b = bzla_hashptr_table_get(slv->score, e);
        assert(b);
        t = (BzlaPtrHashTable *) b->data.as_ptr;
        assert(t);
        if (!min_t || t->count < min_t->count) min_t = t;
      }
      assert(min_t);
      bzla_iter_hashptr_init(&it, min_t);
      while (bzla_iter_hashptr_has_next(&it))
      {
        e = bzla_iter_hashptr_next(&it);
        assert(!bzla_hashptr_table_get(in, e));
        bzla_hashptr_table_add(in, bzla_node_copy(bzla, e));
      }
    }
    else
    {
      for (i = 0; i < cur->arity; i++)
      {
        e = bzla_node_real_addr(cur->e[i]);
        b = bzla_hashptr_table_get(slv->score, e);
        if (b && (t = b->data.as_ptr))
        {
          /* merge tables */
          delta = bzla_util_time_stamp();
          bzla_iter_hashptr_init(&it, t);
          while (bzla_iter_hashptr_has_next(&it))
          {
            e = bzla_iter_hashptr_next(&it);
            if (!bzla_hashptr_table_get(in, e))
              bzla_hashptr_table_add(in, bzla_node_copy(bzla, e));
          }
          slv->time.search_init_apps_compute_scores_merge_applies +=
              bzla_util_time_stamp() - delta;
        }
        else
        {
          mark = bzla_hashint_table_new(mm);
          /* search unique applies */
          BZLA_PUSH_STACK(stack, e);
          while (!BZLA_EMPTY_STACK(stack))
          {
            e = bzla_node_real_addr(BZLA_POP_STACK(stack));
            if (bzla_hashint_table_contains(mark, e->id)) continue;
            bzla_hashint_table_add(mark, e->id);
            if (!e->parameterized && bzla_node_is_apply(e)
                && !bzla_hashptr_table_get(in, e))
              bzla_hashptr_table_add(in, bzla_node_copy(bzla, e));
            for (j = 0; j < e->arity; j++) BZLA_PUSH_STACK(stack, e->e[j]);
          }
          bzla_hashint_table_delete(mark);
        }
      }
    }
  }

  BZLA_RELEASE_STACK(stack);
}

static void
compute_scores_aux(Bzla *bzla, BzlaNodePtrStack *nodes)
{
  assert(BZLA_FUN_SOLVER(bzla)->score);

  uint32_t h;

  h = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);
  if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP)
    compute_scores_aux_min_app(bzla, nodes);
  else if (h == BZLA_JUST_HEUR_BRANCH_MIN_DEP)
    compute_scores_aux_min_dep(bzla, nodes);
  else /* no scores required for BZLA_JUST_HEUR_BRANCH_LEFT */
    assert(h == BZLA_JUST_HEUR_BRANCH_LEFT);
}

void
bzla_dcr_compute_scores(Bzla *bzla)
{
  assert(bzla);

  uint32_t i;
  double start;
  BzlaFunSolver *slv;
  BzlaNode *cur, *e;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack stack, nodes;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;

  /* computing scores only required for BZLA_JUST_HEUR_BRANCH_MIN_DEP and
   * BZLA_JUST_HEUR_BRANCH_MIN_APP */
  if (bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC)
      == BZLA_JUST_HEUR_BRANCH_LEFT)
    return;

  /* Collect all nodes we actually need the score for.  If just is enabled, we
   * only need the children of AND nodes. If dual prop is enabled, we only need
   * APPLY nodes (BV var nodes always have score 0 or 1 depending on the
   * selected heuristic and are treated as such in compare_scores).
   * -> see bzla_dcr_compute_scores_dual_prop */

  start = bzla_util_time_stamp();
  mm    = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, nodes);
  mark = bzla_hashint_table_new(mm);

  slv = BZLA_FUN_SOLVER(bzla);

  if (!slv->score)
    slv->score = bzla_hashptr_table_new(mm,
                                        (BzlaHashPtr) bzla_node_hash_by_id,
                                        (BzlaCmpPtr) bzla_node_compare_by_id);

  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(stack, cur);
    while (!BZLA_EMPTY_STACK(stack))
    {
      cur = bzla_node_real_addr(BZLA_POP_STACK(stack));
      if (bzla_hashint_table_contains(mark, cur->id)) continue;
      bzla_hashint_table_add(mark, cur->id);
      for (i = 0; i < cur->arity; i++)
      {
        e = bzla_node_real_addr(cur->e[i]);
        if (!cur->parameterized && bzla_node_is_bv_and(cur)
            && !bzla_hashptr_table_get(slv->score, e))
        {
          bzla_hashptr_table_add(slv->score, bzla_node_copy(bzla, e));
          /* push onto working stack */
          BZLA_PUSH_STACK(nodes, e);
        }
        BZLA_PUSH_STACK(stack, e);
      }
    }
  }

  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(mark);

  compute_scores_aux(bzla, &nodes);

  BZLA_RELEASE_STACK(nodes);

  slv->time.search_init_apps_compute_scores += bzla_util_time_stamp() - start;
}

void
bzla_dcr_compute_scores_dual_prop(Bzla *bzla)
{
  assert(bzla);

  uint32_t i;
  double start;
  BzlaFunSolver *slv;
  BzlaNode *cur;
  BzlaNodePtrStack stack, nodes;
  BzlaPtrHashTableIterator it;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;

  /* computing scores only required for BZLA_JUST_HEUR_BRANCH_MIN_DEP and
   * BZLA_JUST_HEUR_BRANCH_MIN_APP */
  if (bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC)
      == BZLA_JUST_HEUR_BRANCH_LEFT)
    return;

  start = bzla_util_time_stamp();
  mm    = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  mark = bzla_hashint_table_new(mm);

  slv = BZLA_FUN_SOLVER(bzla);

  /* Collect all nodes we actually need the score for.  If just is enabled, we
   * only need the children of AND nodes. If dual prop is enabled, we only need
   * APPLY nodes (BV var nodes always have score 0 or 1 depending on the
   * selected heuristic and are treated as such in compare_scores).
   * -> see bzla_dcr_compute_scores */

  BZLA_INIT_STACK(mm, nodes);

  if (!slv->score)
    slv->score = bzla_hashptr_table_new(mm,
                                        (BzlaHashPtr) bzla_node_hash_by_id,
                                        (BzlaCmpPtr) bzla_node_compare_by_id);

  /* collect applies in bv skeleton */
  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(stack, cur);
    while (!BZLA_EMPTY_STACK(stack))
    {
      cur = bzla_node_real_addr(BZLA_POP_STACK(stack));
      if (bzla_hashint_table_contains(mark, cur->id)) continue;
      bzla_hashint_table_add(mark, cur->id);

      if (bzla_node_is_apply(cur) || bzla_node_is_fun_eq(cur))
      {
        assert(!cur->parameterized);
        if (!bzla_hashptr_table_get(slv->score, cur))
        {
          bzla_hashptr_table_add(slv->score, bzla_node_copy(bzla, cur));
          /* push onto working stack */
          BZLA_PUSH_STACK(nodes, cur);
        }
        continue;
      }

      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
    }
  }

  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(mark);

  /* compute scores from applies downwards */
  compute_scores_aux(bzla, &nodes);

  BZLA_RELEASE_STACK(nodes);

  slv->time.search_init_apps_compute_scores += bzla_util_time_stamp() - start;
}

int32_t
bzla_dcr_compare_scores(Bzla *bzla, BzlaNode *a, BzlaNode *b)
{
  assert(bzla);
  assert(a);
  assert(b);

  uint32_t h, sa, sb;
  BzlaFunSolver *slv;
  BzlaPtrHashBucket *bucket;

  slv = BZLA_FUN_SOLVER(bzla);

  h  = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);
  a  = bzla_node_real_addr(a);
  b  = bzla_node_real_addr(b);
  sa = sb = 0;

  if (!slv->score) return 0;

  if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP)
  {
    if (bzla_node_is_var(a))
      sa = 0;
    else
    {
      bucket = bzla_hashptr_table_get(slv->score, a);
      assert(bucket);
      sa = ((BzlaPtrHashTable *) bucket->data.as_ptr)->count;
    }

    if (bzla_node_is_var(b))
      sb = 0;
    else
    {
      bucket = bzla_hashptr_table_get(slv->score, b);
      assert(bucket);
      sb = ((BzlaPtrHashTable *) bucket->data.as_ptr)->count;
    }
  }
  else if (h == BZLA_JUST_HEUR_BRANCH_MIN_DEP)
  {
    bucket = bzla_hashptr_table_get(slv->score, a);
    assert(bucket);
    sa = bucket->data.as_int;

    bucket = bzla_hashptr_table_get(slv->score, b);
    assert(bucket);
    sb = bucket->data.as_int;
  }

  return sa < sb;
}

int32_t
bzla_dcr_compare_scores_qsort(const void *p1, const void *p2)
{
  uint32_t h, sa, sb;
  BzlaFunSolver *slv;
  Bzla *bzla;
  BzlaNode *a, *b;
  BzlaPtrHashBucket *bucket;

  sa = sb = 0;
  a       = *((BzlaNode **) p1);
  b       = *((BzlaNode **) p2);
  assert(a->bzla == b->bzla);
  bzla = a->bzla;
  slv  = BZLA_FUN_SOLVER(bzla);

  h = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);

  if (!slv->score) return 0;

  if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP)
  {
    if (bzla_node_is_var(a))
    {
      sa = 0;
    }
    else
    {
      bucket = bzla_hashptr_table_get(slv->score, a);
      assert(bucket);
      assert(bucket->data.as_ptr);
      sa = ((BzlaPtrHashTable *) bucket->data.as_ptr)->count;
    }

    if (bzla_node_is_var(b))
    {
      sb = 0;
    }
    else
    {
      bucket = bzla_hashptr_table_get(slv->score, b);
      assert(bucket);
      assert(bucket->data.as_ptr);
      sb = ((BzlaPtrHashTable *) bucket->data.as_ptr)->count;
    }
  }
  else if (h == BZLA_JUST_HEUR_BRANCH_MIN_DEP)
  {
    if (bzla_node_is_var(a))
    {
      sa = 1;
    }
    else
    {
      bucket = bzla_hashptr_table_get(slv->score, a);
      assert(bucket);
      sa = bucket->data.as_int;
    }

    if (bzla_node_is_var(b))
    {
      sb = 1;
    }
    else
    {
      bucket = bzla_hashptr_table_get(slv->score, b);
      assert(bucket);
      sb = bucket->data.as_int;
    }
  }

  if (sa < sb) return 1;
  if (sa > sb) return -1;
  return 0;
}
