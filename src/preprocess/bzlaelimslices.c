/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaelimslices.h"

#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

struct BzlaSlice
{
  uint32_t upper;
  uint32_t lower;
};

typedef struct BzlaSlice BzlaSlice;

static BzlaSlice *
new_slice(Bzla *bzla, uint32_t upper, uint32_t lower)
{
  BzlaSlice *result;

  assert(bzla != NULL);
  assert(upper >= lower);

  BZLA_NEW(bzla->mm, result);
  result->upper = upper;
  result->lower = lower;
  return result;
}

static void
delete_slice(Bzla *bzla, BzlaSlice *slice)
{
  assert(bzla != NULL);
  assert(slice != NULL);
  BZLA_DELETE(bzla->mm, slice);
}

static uint32_t
hash_slice(BzlaSlice *slice)
{
  uint32_t result;

  assert(slice != NULL);
  assert(slice->upper >= slice->lower);

  result = (uint32_t) slice->upper;
  result += (uint32_t) slice->lower;
  result *= 7334147u;
  return result;
}

static int32_t
compare_slices(BzlaSlice *s1, BzlaSlice *s2)
{
  assert(s1 != NULL);
  assert(s2 != NULL);
  assert(s1->upper >= s1->lower);
  assert(s2->upper >= s2->lower);

  if (s1->upper < s2->upper) return -1;

  if (s1->upper > s2->upper) return 1;

  assert(s1->upper == s1->upper);
  if (s1->lower < s2->lower) return -1;

  if (s1->lower > s2->lower) return 1;

  assert(s1->upper == s2->upper && s1->lower == s2->lower);
  return 0;
}

static int32_t
compare_slices_qsort(const void *p1, const void *p2)
{
  return compare_slices(*((BzlaSlice **) p1), *((BzlaSlice **) p2));
}

static int32_t
compare_int_ptr(const void *p1, const void *p2)
{
  int32_t v1 = *((int32_t *) p1);
  int32_t v2 = *((int32_t *) p2);
  if (v1 < v2) return -1;

  if (v1 > v2) return 1;

  return 0;
}

void
bzla_eliminate_slices_on_bv_vars(Bzla *bzla)
{
  BzlaNode *var, *cur, *result, *lambda_var, *temp;
  BzlaSortId sort;
  BzlaSlice *s1, *s2, *new_s1, *new_s2, *new_s3, **sorted_slices;
  BzlaPtrHashBucket *b_var, *b1, *b2;
  BzlaNodeIterator it;
  BzlaPtrHashTable *slices;
  int32_t i;
  uint32_t min, max, count;
  BzlaNodePtrStack vars;
  double start, delta;
  BzlaMemMgr *mm;
  uint32_t vals[4];

  assert(bzla != NULL);

  start = bzla_util_time_stamp();
  count = 0;

  BZLALOG(1, "start slice elimination");

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, vars);
  for (b_var = bzla->bv_vars->first; b_var != NULL; b_var = b_var->next)
  {
    if (b_var->data.flag) continue;
    var = (BzlaNode *) b_var->key;
    BZLA_PUSH_STACK(vars, var);
    /* mark as processed, required for non-destructive substiution */
    b_var->data.flag = true;
  }

  while (!BZLA_EMPTY_STACK(vars))
  {
    var = BZLA_POP_STACK(vars);
    if (!bzla_node_is_bv_var(var)) continue;
    BZLALOG(2,
            "process %s (%s)",
            bzla_util_node2string(var),
            bzla_util_node2string(bzla_node_get_simplified(bzla, var)));
    assert(bzla_node_is_regular(var));
    slices = bzla_hashptr_table_new(
        mm, (BzlaHashPtr) hash_slice, (BzlaCmpPtr) compare_slices);

    /* find all slices on variable */
    bzla_iter_parent_init(&it, var);
    while (bzla_iter_parent_has_next(&it))
    {
      cur = bzla_iter_parent_next(&it);
      assert(bzla_node_is_regular(cur));
      if (bzla_node_is_simplified(cur))
      {
        assert(bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
        continue;
      }
      if (bzla_node_is_bv_slice(cur))
      {
        s1 = new_slice(bzla,
                       bzla_node_bv_slice_get_upper(cur),
                       bzla_node_bv_slice_get_lower(cur));
        assert(!bzla_hashptr_table_get(slices, s1));
        /* full slices should have been eliminated by rewriting */
        assert(s1->upper - s1->lower + 1 < bzla_node_bv_get_width(bzla, var));
        bzla_hashptr_table_add(slices, s1);
        BZLALOG(2, "  found slice %u %u", s1->upper, s1->lower);
      }
    }

    /* no splitting necessary? */
    if (slices->count == 0u)
    {
      bzla_hashptr_table_delete(slices);
      continue;
    }

    /* add full slice */
    s1 = new_slice(bzla, bzla_node_bv_get_width(bzla, var) - 1, 0);
    assert(!bzla_hashptr_table_get(slices, s1));
    bzla_hashptr_table_add(slices, s1);

  BZLA_SPLIT_SLICES_RESTART:
    for (b1 = slices->last; b1 != NULL; b1 = b1->prev)
    {
      s1 = (BzlaSlice *) b1->key;
      for (b2 = b1->prev; b2 != NULL; b2 = b2->prev)
      {
        s2 = (BzlaSlice *) b2->key;

        assert(compare_slices(s1, s2));

        /* not overlapping? */
        if ((s1->lower > s2->upper) || (s1->upper < s2->lower)
            || (s2->lower > s1->upper) || (s2->upper < s1->lower))
          continue;

        if (s1->upper == s2->upper)
        {
          assert(s1->lower != s2->lower);
          max    = BZLA_MAX_UTIL(s1->lower, s2->lower);
          min    = BZLA_MIN_UTIL(s1->lower, s2->lower);
          new_s1 = new_slice(bzla, max - 1, min);
          if (!bzla_hashptr_table_get(slices, new_s1))
            bzla_hashptr_table_add(slices, new_s1);
          else
            delete_slice(bzla, new_s1);

          if (min == s1->lower)
          {
            bzla_hashptr_table_remove(slices, s1, 0, 0);
            delete_slice(bzla, s1);
          }
          else
          {
            bzla_hashptr_table_remove(slices, s2, 0, 0);
            delete_slice(bzla, s2);
          }
          goto BZLA_SPLIT_SLICES_RESTART;
        }

        if (s1->lower == s2->lower)
        {
          assert(s1->upper != s2->upper);
          max    = BZLA_MAX_UTIL(s1->upper, s2->upper);
          min    = BZLA_MIN_UTIL(s1->upper, s2->upper);
          new_s1 = new_slice(bzla, max, min + 1);
          if (!bzla_hashptr_table_get(slices, new_s1))
            bzla_hashptr_table_add(slices, new_s1);
          else
            delete_slice(bzla, new_s1);
          if (max == s1->upper)
          {
            bzla_hashptr_table_remove(slices, s1, 0, 0);
            delete_slice(bzla, s1);
          }
          else
          {
            bzla_hashptr_table_remove(slices, s2, NULL, NULL);
            delete_slice(bzla, s2);
          }
          goto BZLA_SPLIT_SLICES_RESTART;
        }

        /* regular overlapping case (overlapping at both ends) */
        vals[0] = s1->upper;
        vals[1] = s1->lower;
        vals[2] = s2->upper;
        vals[3] = s2->lower;
        qsort(vals, 4, sizeof(uint32_t), compare_int_ptr);
        new_s1 = new_slice(bzla, vals[3], vals[2] + 1);
        new_s2 = new_slice(bzla, vals[2], vals[1]);
        new_s3 = new_slice(bzla, vals[1] - 1, vals[0]);
        bzla_hashptr_table_remove(slices, s1, 0, 0);
        bzla_hashptr_table_remove(slices, s2, NULL, NULL);
        delete_slice(bzla, s1);
        delete_slice(bzla, s2);
        if (!bzla_hashptr_table_get(slices, new_s1))
          bzla_hashptr_table_add(slices, new_s1);
        else
          delete_slice(bzla, new_s1);
        if (!bzla_hashptr_table_get(slices, new_s2))
          bzla_hashptr_table_add(slices, new_s2);
        else
          delete_slice(bzla, new_s2);
        if (!bzla_hashptr_table_get(slices, new_s3))
          bzla_hashptr_table_add(slices, new_s3);
        else
          delete_slice(bzla, new_s3);
        goto BZLA_SPLIT_SLICES_RESTART;
      }
    }

    /* copy slices to sort them */
    assert(slices->count > 1u);
    BZLA_NEWN(mm, sorted_slices, slices->count);
    i = 0;
    for (b1 = slices->first; b1 != NULL; b1 = b1->next)
    {
      s1                 = (BzlaSlice *) b1->key;
      sorted_slices[i++] = s1;
    }
    qsort(sorted_slices,
          slices->count,
          sizeof(BzlaSlice *),
          compare_slices_qsort);

    s1     = sorted_slices[slices->count - 1];
    sort   = bzla_sort_bv(bzla, s1->upper - s1->lower + 1);
    result = bzla_exp_var(bzla, sort, 0);
    bzla_sort_release(bzla, sort);
    delete_slice(bzla, s1);
    for (i = (int32_t) slices->count - 2; i >= 0; i--)
    {
      s1         = sorted_slices[i];
      sort       = bzla_sort_bv(bzla, s1->upper - s1->lower + 1);
      lambda_var = bzla_exp_var(bzla, sort, 0);
      bzla_sort_release(bzla, sort);
      temp = bzla_exp_bv_concat(bzla, result, lambda_var);
      bzla_node_release(bzla, result);
      result = temp;
      bzla_node_release(bzla, lambda_var);
      delete_slice(bzla, s1);
    }
    BZLA_DELETEN(mm, sorted_slices, slices->count);
    bzla_hashptr_table_delete(slices);

    count++;
    bzla->stats.eliminated_slices++;
    temp = bzla_exp_eq(bzla, var, result);
    bzla_assert_exp(bzla, temp);
    bzla_node_release(bzla, temp);
    bzla_node_release(bzla, result);
  }

  BZLA_RELEASE_STACK(vars);

  delta = bzla_util_time_stamp() - start;
  bzla->time.slicing += delta;
  BZLALOG(1, "end slice elimination");
  BZLA_MSG(bzla->msg, 1, "sliced %u variables in %1.f seconds", count, delta);
}
