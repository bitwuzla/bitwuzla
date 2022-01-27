/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "aigprop.h"

#include <math.h>

#include "bzlaclone.h"
#include "bzlacore.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#define BZLA_AIGPROPLOG(level, fmt, args...) \
  do                                         \
  {                                          \
    if (aprop->loglevel < level) break;      \
    msg(fmt, ##args);                        \
  } while (0)

static void
msg(char *fmt, ...)
{
  va_list msg;

  fputs("[aigprop] ", stdout);
  va_start(msg, fmt);
  vfprintf(stdout, fmt, msg);
  va_end(msg);
  fputc('\n', stdout);
  fflush(stdout);
}

/*------------------------------------------------------------------------*/

#define BZLA_AIGPROP_MAXSTEPS_CFACT 100
#define BZLA_AIGPROP_MAXSTEPS(i) \
  (BZLA_AIGPROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BZLA_AIGPROP_SELECT_CFACT 20

/*------------------------------------------------------------------------*/

int32_t
bzla_aigprop_get_assignment_aig(BzlaAIGProp *aprop, BzlaAIG *aig)
{
  assert(aprop);

  int32_t res;
  int32_t id;

  if (bzla_aig_is_true(aig)) return 1;
  if (bzla_aig_is_false(aig)) return -1;

  id = bzla_aig_get_id(BZLA_REAL_ADDR_AIG(aig));
  assert(bzla_hashint_map_get(aprop->model, id));
  res = bzla_hashint_map_get(aprop->model, id)->as_int;
  res = BZLA_IS_INVERTED_AIG(aig) ? -res : res;
  return res;
}

/*------------------------------------------------------------------------*/

/* score
 *
 * score (aigvar, A) = A (aigvar)
 * score (BZLA_CONST_AIG_TRUE, A) = 1.0
 * score (BZLA_CONST_AIG_FALSE, A) = 0.0
 * score (aig0 /\ aig1, A) = 1/2 * (score (aig0) + score (aig1), A)
 * score (-(-aig0 /\ -aig1), A) = max (score (-aig0), score (-aig1), A)
 */

#define BZLA_AIGPROP_LOG_COMPUTE_SCORE_AIG(cur, left, right, s0, s1, res) \
  do                                                                      \
  {                                                                       \
    a = bzla_aigprop_get_assignment_aig(aprop, left);                     \
    assert(a);                                                            \
    BZLA_AIGPROPLOG(3,                                                    \
                    "        assignment aig0 (%s%d): %d",                 \
                    BZLA_IS_INVERTED_AIG(left) ? "-" : "",                \
                    BZLA_REAL_ADDR_AIG(left)->id,                         \
                    a < 0 ? 0 : 1);                                       \
    a = bzla_aigprop_get_assignment_aig(aprop, right);                    \
    assert(a);                                                            \
    BZLA_AIGPROPLOG(3,                                                    \
                    "        assignment aig1 (%s%d): %d",                 \
                    BZLA_IS_INVERTED_AIG(right) ? "-" : "",               \
                    BZLA_REAL_ADDR_AIG(right)->id,                        \
                    a < 0 ? 0 : 1);                                       \
    BZLA_AIGPROPLOG(3,                                                    \
                    "        score      aig0 (%s%d): %f%s",               \
                    BZLA_IS_INVERTED_AIG(left) ? "-" : "",                \
                    BZLA_REAL_ADDR_AIG(left)->id,                         \
                    s0,                                                   \
                    s0 < 1.0 ? " (< 1.0)" : "");                          \
    BZLA_AIGPROPLOG(3,                                                    \
                    "        score      aig1 (%s%d): %f%s",               \
                    BZLA_IS_INVERTED_AIG(right) ? "-" : "",               \
                    BZLA_REAL_ADDR_AIG(right)->id,                        \
                    s1,                                                   \
                    s1 < 1.0 ? " (< 1.0)" : "");                          \
    BZLA_AIGPROPLOG(3,                                                    \
                    "      * score cur (%s%d): %f%s",                     \
                    BZLA_IS_INVERTED_AIG(cur) ? "-" : "",                 \
                    real_cur->id,                                         \
                    res,                                                  \
                    res < 1.0 ? " (< 1.0)" : "");                         \
  } while (0)

static double
compute_score_aig(BzlaAIGProp *aprop, BzlaAIG *aig)
{
  assert(aprop);
  assert(!bzla_aig_is_const(aig));

  int32_t curid, leftid, rightid;
  double res, sleft, sright;
  BzlaAIGPtrStack stack;
  BzlaAIG *cur, *real_cur, *left, *right;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;
#ifndef NDEBUG
  int32_t a;
#endif

  curid = bzla_aig_get_id(aig);
  if (bzla_hashint_map_contains(aprop->score, curid))
    return bzla_hashint_map_get(aprop->score, curid)->as_dbl;

  mm  = aprop->mm;
  res = 0.0;

  BZLA_INIT_STACK(mm, stack);
  mark = bzla_hashint_map_new(mm);

  BZLA_PUSH_STACK(stack, aig);
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = BZLA_REAL_ADDR_AIG(cur);

    if (bzla_aig_is_const(real_cur)) continue;

    curid = bzla_aig_get_id(cur);
    if (bzla_hashint_map_contains(aprop->score, curid)) continue;

    d = bzla_hashint_map_get(mark, real_cur->id);
    if (d && d->as_int == 1) continue;

    if (!d)
    {
      bzla_hashint_map_add(mark, real_cur->id);
      assert(bzla_aig_is_var(real_cur) || bzla_aig_is_and(real_cur));
      BZLA_PUSH_STACK(stack, cur);
      if (bzla_aig_is_and(real_cur))
      {
        left  = bzla_aig_get_left_child(aprop->amgr, real_cur);
        right = bzla_aig_get_right_child(aprop->amgr, real_cur);
        if (!bzla_aig_is_const(left)) BZLA_PUSH_STACK(stack, left);
        if (!bzla_aig_is_const(right)) BZLA_PUSH_STACK(stack, right);
      }
    }
    else
    {
      assert(d->as_int == 0);
      d->as_int = 1;
      assert(bzla_aigprop_get_assignment_aig(aprop, cur) != 0);
#ifndef NDEBUG
      a = bzla_aigprop_get_assignment_aig(aprop, cur);
      assert(a);
      BZLA_AIGPROPLOG(3, "");
      BZLA_AIGPROPLOG(3,
                      "  ** assignment cur (%s%d): %d",
                      BZLA_IS_INVERTED_AIG(cur) ? "-" : "",
                      real_cur->id,
                      a < 0 ? 0 : 1);
#endif
      assert(!bzla_hashint_map_contains(aprop->score, curid));
      assert(!bzla_hashint_map_contains(aprop->score, -curid));

      if (bzla_aig_is_var(real_cur))
      {
        res = bzla_aigprop_get_assignment_aig(aprop, cur) < 0 ? 0.0 : 1.0;
        BZLA_AIGPROPLOG(3,
                        "        * score cur (%s%d): %f",
                        BZLA_IS_INVERTED_AIG(cur) ? "-" : "",
                        real_cur->id,
                        res);
        BZLA_AIGPROPLOG(3,
                        "        * score cur (%s%d): %f",
                        BZLA_IS_INVERTED_AIG(cur) ? "" : "-",
                        real_cur->id,
                        res == 0.0 ? 1.0 : 0.0);
        bzla_hashint_map_add(aprop->score, curid)->as_dbl = res;
        bzla_hashint_map_add(aprop->score, -curid)->as_dbl =
            res == 0.0 ? 1.0 : 0.0;
      }
      else
      {
        assert(bzla_aig_is_and(real_cur));

        left    = bzla_aig_get_left_child(aprop->amgr, real_cur);
        right   = bzla_aig_get_right_child(aprop->amgr, real_cur);
        leftid  = bzla_aig_get_id(left);
        rightid = bzla_aig_get_id(right);

        assert(bzla_aig_is_const(left)
               || bzla_hashint_map_contains(aprop->score, leftid));
        assert(bzla_aig_is_const(right)
               || bzla_hashint_map_contains(aprop->score, rightid));
        assert(bzla_aig_is_const(left)
               || bzla_hashint_map_contains(aprop->score, -leftid));
        assert(bzla_aig_is_const(right)
               || bzla_hashint_map_contains(aprop->score, -rightid));

        sleft = bzla_aig_is_const(left)
                    ? (bzla_aig_is_true(left) ? 1.0 : 0.0)
                    : bzla_hashint_map_get(aprop->score, leftid)->as_dbl;
        sright = bzla_aig_is_const(right)
                     ? (bzla_aig_is_true(right) ? 1.0 : 0.0)
                     : bzla_hashint_map_get(aprop->score, rightid)->as_dbl;
        res = (sleft + sright) / 2.0;
        /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
           choose minimum (else it might again result in 1.0) */
        if (res == 1.0 && (sleft < 1.0 || sright < 1.0))
          res = sleft < sright ? sleft : sright;
        assert(res >= 0.0 && res <= 1.0);
        bzla_hashint_map_add(aprop->score, real_cur->id)->as_dbl = res;
#ifndef NDEBUG
        BZLA_AIGPROP_LOG_COMPUTE_SCORE_AIG(
            real_cur, left, right, sleft, sright, res);
#endif
        sleft = bzla_aig_is_const(left)
                    ? (bzla_aig_is_true(left) ? 0.0 : 1.0)
                    : bzla_hashint_map_get(aprop->score, -leftid)->as_dbl;
        sright = bzla_aig_is_const(right)
                     ? (bzla_aig_is_true(right) ? 0.0 : 1.0)
                     : bzla_hashint_map_get(aprop->score, -rightid)->as_dbl;
        res = sleft > sright ? sleft : sright;
        assert(res >= 0.0 && res <= 1.0);
        bzla_hashint_map_add(aprop->score, -real_cur->id)->as_dbl = res;
#ifndef NDEBUG
        BZLA_AIGPROP_LOG_COMPUTE_SCORE_AIG(BZLA_INVERT_AIG(real_cur),
                                           BZLA_INVERT_AIG(left),
                                           BZLA_INVERT_AIG(right),
                                           sleft,
                                           sright,
                                           res);
#endif
      }
      assert(bzla_hashint_map_contains(aprop->score, curid));
      assert(bzla_hashint_map_contains(aprop->score, -curid));
    }
  }

  bzla_hashint_map_delete(mark);
  BZLA_RELEASE_STACK(stack);

  assert(bzla_hashint_map_contains(aprop->score, bzla_aig_get_id(aig)));
  assert(bzla_hashint_map_contains(aprop->score, -bzla_aig_get_id(aig)));
  return res;
}

static void
compute_scores(BzlaAIGProp *aprop)
{
  assert(aprop);
  assert(aprop->roots);
  assert(aprop->model);

  BzlaAIGPtrStack stack;
  BzlaIntHashTable *cache;
  BzlaAIG *cur, *real_cur, *left, *right;
  BzlaIntHashTableIterator it;
  BzlaMemMgr *mm;

  BZLA_AIGPROPLOG(3, "*** compute scores");

  mm = aprop->mm;

  BZLA_INIT_STACK(mm, stack);
  cache = bzla_hashint_table_new(mm);

  if (!aprop->score) aprop->score = bzla_hashint_map_new(mm);

  /* collect roots */
  bzla_iter_hashint_init(&it, aprop->roots);
  while (bzla_iter_hashint_has_next(&it))
    BZLA_PUSH_STACK(
        stack, bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it)));

  /* compute scores */
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = BZLA_REAL_ADDR_AIG(cur);

    if (bzla_aig_is_const(real_cur)) continue;
    if (bzla_hashint_map_contains(aprop->score, bzla_aig_get_id(cur))) continue;

    if (!bzla_hashint_table_contains(cache, real_cur->id))
    {
      bzla_hashint_table_add(cache, real_cur->id);
      assert(bzla_aig_is_var(real_cur) || bzla_aig_is_and(real_cur));
      BZLA_PUSH_STACK(stack, cur);
      if (bzla_aig_is_and(real_cur))
      {
        left  = bzla_aig_get_left_child(aprop->amgr, real_cur);
        right = bzla_aig_get_right_child(aprop->amgr, real_cur);
        if (!bzla_aig_is_const(left)
            && !bzla_hashint_table_contains(cache,
                                            BZLA_REAL_ADDR_AIG(left)->id))
          BZLA_PUSH_STACK(stack, left);
        if (!bzla_aig_is_const(right)
            && !bzla_hashint_table_contains(cache,
                                            BZLA_REAL_ADDR_AIG(right)->id))
          BZLA_PUSH_STACK(stack, right);
      }
    }
    else
    {
      compute_score_aig(aprop, cur);
    }
  }

  /* cleanup */
  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(cache);
}

/*------------------------------------------------------------------------*/

static void
recursively_compute_assignment(BzlaAIGProp *aprop, BzlaAIG *aig)
{
  assert(aprop);
  assert(aprop->model);
  assert(aig);

  int32_t aleft, aright;
  BzlaAIG *cur, *real_cur, *left, *right;
  BzlaAIGPtrStack stack;
  BzlaIntHashTable *cache;
  BzlaMemMgr *mm;

  if (bzla_aig_is_const(aig)) return;

  mm = aprop->mm;

  cache = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, stack);
  BZLA_PUSH_STACK(stack, aig);

  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = BZLA_REAL_ADDR_AIG(cur);
    assert(!bzla_aig_is_const(real_cur));
    if (bzla_hashint_map_contains(aprop->model, real_cur->id)) continue;

    if (bzla_aig_is_var(real_cur))
    {
      /* initialize with false */
      bzla_hashint_map_add(aprop->model, real_cur->id)->as_int = -1;
    }
    else
    {
      assert(bzla_aig_is_and(real_cur));
      left  = bzla_aig_get_left_child(aprop->amgr, real_cur);
      right = bzla_aig_get_right_child(aprop->amgr, real_cur);

      if (!bzla_hashint_table_contains(cache, real_cur->id))
      {
        bzla_hashint_table_add(cache, real_cur->id);
        BZLA_PUSH_STACK(stack, cur);
        if (!bzla_aig_is_const(left)
            && !bzla_hashint_table_contains(cache,
                                            BZLA_REAL_ADDR_AIG(left)->id))
          BZLA_PUSH_STACK(stack, left);
        if (!bzla_aig_is_const(right)
            && !bzla_hashint_table_contains(cache,
                                            BZLA_REAL_ADDR_AIG(right)->id))
          BZLA_PUSH_STACK(stack, right);
      }
      else
      {
        aleft = bzla_aigprop_get_assignment_aig(aprop, left);
        assert(aleft);
        aright = bzla_aigprop_get_assignment_aig(aprop, right);
        assert(aright);
        if (aleft < 0 || aright < 0)
          bzla_hashint_map_add(aprop->model, real_cur->id)->as_int = -1;
        else
          bzla_hashint_map_add(aprop->model, real_cur->id)->as_int = 1;
      }
    }
  }

  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(stack);
}

void
bzla_aigprop_delete_model(BzlaAIGProp *aprop)
{
  assert(aprop);

  if (!aprop->model) return;
  bzla_hashint_map_delete(aprop->model);
  aprop->model = 0;
}

void
bzla_aigprop_init_model(BzlaAIGProp *aprop)
{
  assert(aprop);

  if (aprop->model) bzla_aigprop_delete_model(aprop);
  aprop->model = bzla_hashint_map_new(aprop->mm);
}

void
bzla_aigprop_generate_model(BzlaAIGProp *aprop, bool reset)
{
  assert(aprop);
  assert(aprop->roots);

  BzlaIntHashTableIterator it;

  if (reset) bzla_aigprop_init_model(aprop);

  bzla_iter_hashint_init(&it, aprop->roots);
  while (bzla_iter_hashint_has_next(&it))
    recursively_compute_assignment(
        aprop, bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it)));
}

/*------------------------------------------------------------------------*/

static inline void
update_unsatroots_table(BzlaAIGProp *aprop, BzlaAIG *aig, int32_t assignment)
{
  assert(aprop);
  assert(aig);
  assert(!bzla_aig_is_const(aig));
  assert(bzla_hashint_table_contains(aprop->roots, bzla_aig_get_id(aig))
         || bzla_hashint_table_contains(aprop->roots, -bzla_aig_get_id(aig)));
  assert(bzla_aigprop_get_assignment_aig(aprop, aig) != assignment);
  assert(assignment == 1 || assignment == -1);

  uint32_t id;

  id = bzla_aig_get_id(aig);

  if (bzla_hashint_map_contains(aprop->unsatroots, id))
  {
    bzla_hashint_map_remove(aprop->unsatroots, id, 0);
    assert(bzla_aigprop_get_assignment_aig(aprop, aig) == -1);
    assert(assignment == 1);
  }
  else if (bzla_hashint_map_contains(aprop->unsatroots, -id))
  {
    bzla_hashint_map_remove(aprop->unsatroots, -id, 0);
    assert(bzla_aigprop_get_assignment_aig(aprop, BZLA_INVERT_AIG(aig)) == -1);
    assert(assignment == -1);
  }
  else if (assignment == -1)
  {
    bzla_hashint_map_add(aprop->unsatroots, id);
    assert(bzla_aigprop_get_assignment_aig(aprop, aig) == 1);
  }
  else
  {
    bzla_hashint_map_add(aprop->unsatroots, -id);
    assert(bzla_aigprop_get_assignment_aig(aprop, BZLA_INVERT_AIG(aig)) == 1);
  }
}

static void
update_cone(BzlaAIGProp *aprop, BzlaAIG *aig, int32_t assignment)
{
  assert(aprop);
  assert(aig);
  assert(BZLA_IS_REGULAR_AIG(aig));
  assert(bzla_aig_is_var(aig));
  assert(assignment == 1 || assignment == -1);

  int32_t aleft, aright, ass, leftid, rightid;
  uint32_t i;
  double start, delta, sleft, sright, s;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  BzlaAIGPtrStack stack, cone;
  BzlaIntStack *parents;
  BzlaAIG *cur, *left, *right;
  BzlaMemMgr *mm;

  start = bzla_util_time_stamp();

  mm = aprop->mm;

#ifndef NDEBUG
  BzlaIntHashTableIterator it;
  BzlaAIG *root;
  bzla_iter_hashint_init(&it, aprop->roots);
  while (bzla_iter_hashint_has_next(&it))
  {
    root = bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it));
    assert(!bzla_aig_is_false(root));
    if ((!BZLA_IS_INVERTED_AIG(root)
         && bzla_aigprop_get_assignment_aig(aprop, BZLA_REAL_ADDR_AIG(root))
                == -1)
        || (BZLA_IS_INVERTED_AIG(root)
            && bzla_aigprop_get_assignment_aig(aprop, BZLA_REAL_ADDR_AIG(root))
                   == 1))
    {
      assert(
          bzla_hashint_map_contains(aprop->unsatroots, bzla_aig_get_id(root)));
    }
    else if ((!BZLA_IS_INVERTED_AIG(root)
              && bzla_aigprop_get_assignment_aig(aprop,
                                                 BZLA_REAL_ADDR_AIG(root))
                     == 1)
             || (BZLA_IS_INVERTED_AIG(root)
                 && bzla_aigprop_get_assignment_aig(aprop,
                                                    BZLA_REAL_ADDR_AIG(root))
                        == -1))
    {
      assert(
          !bzla_hashint_map_contains(aprop->unsatroots, bzla_aig_get_id(root)));
    }
  }
#endif

  /* reset cone ----------------------------------------------------------- */

  BZLA_INIT_STACK(mm, cone);
  BZLA_INIT_STACK(mm, stack);
  cache = bzla_hashint_table_new(mm);
  BZLA_PUSH_STACK(stack, aig);
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur = BZLA_POP_STACK(stack);
    assert(BZLA_IS_REGULAR_AIG(cur));
    if (bzla_hashint_table_contains(cache, cur->id)) continue;
    bzla_hashint_table_add(cache, cur->id);
    if (cur != aig) BZLA_PUSH_STACK(cone, cur);
    assert(bzla_hashint_map_contains(aprop->parents, cur->id));
    parents = bzla_hashint_map_get(aprop->parents, cur->id)->as_ptr;
    for (i = 0; i < BZLA_COUNT_STACK(*parents); i++)
      BZLA_PUSH_STACK(
          stack, bzla_aig_get_by_id(aprop->amgr, BZLA_PEEK_STACK(*parents, i)));
  }
  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(cache);

  aprop->time.update_cone_reset += bzla_util_time_stamp() - start;

  /* update assignment and score of 'aig' --------------------------------- */
  /* update model */
  d = bzla_hashint_map_get(aprop->model, aig->id);
  assert(d);
  /* update unsatroots table */
  if (d->as_int != assignment
      && (bzla_hashint_table_contains(aprop->roots, aig->id)
          || bzla_hashint_table_contains(aprop->roots, -aig->id)))
    update_unsatroots_table(aprop, aig, assignment);
  d->as_int = assignment;

  /* update score */
  if (aprop->score)
  {
    d         = bzla_hashint_map_get(aprop->score, aig->id);
    d->as_dbl = assignment < 0 ? 0.0 : 1.0;
    d         = bzla_hashint_map_get(aprop->score, -aig->id);
    d->as_dbl = assignment < 0 ? 1.0 : 0.0;
  }

  qsort(cone.start,
        BZLA_COUNT_STACK(cone),
        sizeof(BzlaAIG *),
        bzla_compare_aig_by_id_qsort_asc);

  /* update model of cone ------------------------------------------------- */

  delta = bzla_util_time_stamp();

  for (i = 0; i < BZLA_COUNT_STACK(cone); i++)
  {
    cur = BZLA_PEEK_STACK(cone, i);
    assert(BZLA_IS_REGULAR_AIG(cur));
    assert(bzla_aig_is_and(cur));
    assert(bzla_hashint_map_contains(aprop->model, cur->id));

    left  = bzla_aig_get_left_child(aprop->amgr, cur);
    right = bzla_aig_get_right_child(aprop->amgr, cur);
    aleft = bzla_aigprop_get_assignment_aig(aprop, left);
    assert(aleft);
    aright = bzla_aigprop_get_assignment_aig(aprop, right);
    assert(aright);
    ass = aleft < 0 || aright < 0 ? -1 : 1;
    d   = bzla_hashint_map_get(aprop->model, cur->id);
    assert(d);
    /* update unsatroots table */
    if (d->as_int != ass
        && (bzla_hashint_table_contains(aprop->roots, cur->id)
            || bzla_hashint_table_contains(aprop->roots, -cur->id)))
      update_unsatroots_table(aprop, cur, ass);
    d->as_int = ass;
  }

  aprop->time.update_cone_model_gen += bzla_util_time_stamp() - delta;
  delta = bzla_util_time_stamp();

  /* update score of cone ------------------------------------------------- */

  if (aprop->score)
  {
    delta = bzla_util_time_stamp();
    for (i = 0; i < BZLA_COUNT_STACK(cone); i++)
    {
      cur = BZLA_PEEK_STACK(cone, i);
      assert(BZLA_IS_REGULAR_AIG(cur));
      assert(bzla_aig_is_and(cur));
      assert(bzla_hashint_map_contains(aprop->score, cur->id));
      assert(bzla_hashint_map_contains(aprop->score, -cur->id));

      left    = bzla_aig_get_left_child(aprop->amgr, cur);
      right   = bzla_aig_get_right_child(aprop->amgr, cur);
      leftid  = bzla_aig_get_id(left);
      rightid = bzla_aig_get_id(right);

      sleft = bzla_aig_is_const(left)
                  ? (bzla_aig_is_true(left) ? 1.0 : 0.0)
                  : bzla_hashint_map_get(aprop->score, leftid)->as_dbl;
      sright = bzla_aig_is_const(right)
                   ? (bzla_aig_is_true(right) ? 1.0 : 0.0)
                   : bzla_hashint_map_get(aprop->score, rightid)->as_dbl;
      s = (sleft + sright) / 2.0;
      /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
         choose minimum (else it might again result in 1.0) */
      if (s == 1.0 && (sleft < 1.0 || sright < 1.0))
        s = sleft < sright ? sleft : sright;
      assert(s >= 0.0 && s <= 1.0);
      bzla_hashint_map_get(aprop->score, cur->id)->as_dbl = s;

      sleft = bzla_aig_is_const(left)
                  ? (bzla_aig_is_true(left) ? 0.0 : 1.0)
                  : bzla_hashint_map_get(aprop->score, -leftid)->as_dbl;
      sright = bzla_aig_is_const(right)
                   ? (bzla_aig_is_true(right) ? 1.0 : 0.0)
                   : bzla_hashint_map_get(aprop->score, -rightid)->as_dbl;
      s = sleft > sright ? sleft : sright;
      assert(s >= 0.0 && s <= 1.0);
      bzla_hashint_map_get(aprop->score, -cur->id)->as_dbl = s;
    }
    aprop->time.update_cone_compute_score += bzla_util_time_stamp() - delta;
  }

  BZLA_RELEASE_STACK(cone);

#ifndef NDEBUG
  bzla_iter_hashint_init(&it, aprop->roots);
  while (bzla_iter_hashint_has_next(&it))
  {
    root = bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it));
    if ((!BZLA_IS_INVERTED_AIG(root)
         && bzla_aigprop_get_assignment_aig(aprop, BZLA_REAL_ADDR_AIG(root))
                == -1)
        || (BZLA_IS_INVERTED_AIG(root)
            && bzla_aigprop_get_assignment_aig(aprop, BZLA_REAL_ADDR_AIG(root))
                   == 1))
    {
      assert(
          bzla_hashint_map_contains(aprop->unsatroots, bzla_aig_get_id(root)));
    }
    else if ((!BZLA_IS_INVERTED_AIG(root)
              && bzla_aigprop_get_assignment_aig(aprop,
                                                 BZLA_REAL_ADDR_AIG(root))
                     == 1)
             || (BZLA_IS_INVERTED_AIG(root)
                 && bzla_aigprop_get_assignment_aig(aprop,
                                                    BZLA_REAL_ADDR_AIG(root))
                        == -1))
    {
      assert(
          !bzla_hashint_map_contains(aprop->unsatroots, bzla_aig_get_id(root)));
    }
  }
#endif

  aprop->time.update_cone += bzla_util_time_stamp() - start;
}

/*------------------------------------------------------------------------*/

static BzlaAIG *
select_root(BzlaAIGProp *aprop, uint32_t nmoves)
{
  assert(aprop);
  assert(aprop->unsatroots);
  assert(aprop->score);

  BzlaAIG *res, *cur;
  BzlaIntHashTableIterator it;
  BzlaMemMgr *mm;

  mm  = aprop->mm;
  res = 0;

  if (aprop->use_bandit)
  {
    int32_t *selected;
    double value, max_value, score;
    BzlaHashTableData *d;

    max_value = 0.0;
    bzla_iter_hashint_init(&it, aprop->unsatroots);
    while (bzla_iter_hashint_has_next(&it))
    {
      selected = &aprop->unsatroots->data[it.cur_pos].as_int;
      cur      = bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it));
      assert(bzla_aigprop_get_assignment_aig(aprop, cur) != 1);
      assert(!bzla_aig_is_const(cur));
      d = bzla_hashint_map_get(aprop->score, bzla_aig_get_id(cur));
      assert(d);
      score = d->as_dbl;
      assert(score < 1.0);
      if (!res)
      {
        res = cur;
        *selected += 1;
        continue;
      }
      value = score + BZLA_AIGPROP_SELECT_CFACT * sqrt(log(*selected) / nmoves);
      if (value > max_value)
      {
        res       = cur;
        max_value = value;
        *selected *= 1;
      }
    }
  }
  else
  {
    uint32_t r;
    BzlaAIGPtrStack stack;
    BZLA_INIT_STACK(mm, stack);
    bzla_iter_hashint_init(&it, aprop->unsatroots);
    while (bzla_iter_hashint_has_next(&it))
    {
      cur = bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it));
      assert(bzla_aigprop_get_assignment_aig(aprop, cur) != 1);
      assert(!bzla_aig_is_const(cur));
      BZLA_PUSH_STACK(stack, cur);
    }
    assert(BZLA_COUNT_STACK(stack));
    r   = bzla_rng_pick_rand(aprop->rng, 0, BZLA_COUNT_STACK(stack) - 1);
    res = stack.start[r];
    BZLA_RELEASE_STACK(stack);
  }

  assert(res);

  BZLA_AIGPROPLOG(1, "");
  BZLA_AIGPROPLOG(1,
                  "*** select root: %s%d",
                  BZLA_IS_INVERTED_AIG(res) ? "-" : "",
                  BZLA_REAL_ADDR_AIG(res)->id);
  return res;
}

static bool
select_move(BzlaAIGProp *aprop,
            BzlaAIG *root,
            BzlaAIG **input,
            int32_t *assignment)
{
  assert(aprop);
  assert(root);
  assert(!bzla_aig_is_const(root));
  assert(input);
  assert(assignment);

  bool res;
  int32_t i, asscur, ass[2], assnew;
  uint32_t eidx;
  uint64_t nprops, max_nprops;
  BzlaAIG *cur, *real_cur, *c[2];
  BzlaHashTableData *d;

  *input      = 0;
  *assignment = 0;

  cur        = root;
  asscur     = 1;
  nprops     = aprop->stats.props;
  max_nprops = aprop->nprops;
  res        = true;

  if (bzla_aig_is_var(BZLA_REAL_ADDR_AIG(cur)))
  {
    *input      = BZLA_REAL_ADDR_AIG(cur);
    *assignment = BZLA_IS_INVERTED_AIG(cur) ? -asscur : asscur;
  }
  else
  {
    for (;;)
    {
      if (max_nprops && nprops >= max_nprops)
      {
        res = false;
        break;
      }

      real_cur = BZLA_REAL_ADDR_AIG(cur);
      assert(bzla_aig_is_and(real_cur));
      asscur = BZLA_IS_INVERTED_AIG(cur) ? -asscur : asscur;
      c[0]   = bzla_aig_get_by_id(aprop->amgr, real_cur->children[0]);
      c[1]   = bzla_aig_get_by_id(aprop->amgr, real_cur->children[1]);

      /* conflict */
      if (bzla_aig_is_and(real_cur) && bzla_aig_is_const(c[0])
          && bzla_aig_is_const(c[1]))
        break;

      /* select path and determine path assignment */
      if (bzla_aig_is_const(c[0]))
        eidx = 1;
      else if (bzla_aig_is_const(c[1]))
        eidx = 0;
      else
      {
        /* choose 0-branch if exactly one branch is 0,
         * else choose randomly */
        for (i = 0; i < 2; i++)
        {
          assert(
              bzla_hashint_map_get(aprop->model, BZLA_REAL_ADDR_AIG(c[i])->id));
          d = bzla_hashint_map_get(aprop->model, BZLA_REAL_ADDR_AIG(c[i])->id);
          assert(d);
          ass[i] = BZLA_IS_INVERTED_AIG(c[i]) ? -d->as_int : d->as_int;
        }
        if (ass[0] == -1 && ass[1] == 1)
          eidx = 0;
        else if (ass[0] == 1 && ass[1] == -1)
          eidx = 1;
        else
          eidx = bzla_rng_pick_rand(aprop->rng, 0, 1);
      }
      if (asscur == 1)
        assnew = 1;
      else if (ass[eidx ? 0 : 1] == 1)
        assnew = -1;
      else
      {
        assnew = bzla_rng_pick_rand(aprop->rng, 0, 1);
        if (!assnew) assnew = -1;
      }

      cur    = c[eidx];
      asscur = assnew;
      nprops += 1;

      if (bzla_aig_is_var(BZLA_REAL_ADDR_AIG(cur)))
      {
        *input      = BZLA_REAL_ADDR_AIG(cur);
        *assignment = BZLA_IS_INVERTED_AIG(cur) ? -asscur : asscur;
        break;
      }
    }
  }
  aprop->stats.props = nprops;
  return res;
}

static int32_t
move(BzlaAIGProp *aprop, uint32_t nmoves)
{
  assert(aprop);
  assert(aprop->roots);
  assert(aprop->unsatroots);
  assert(aprop->model);

  int32_t assignment;
  BzlaAIG *root, *input;

  /* roots contain false AIG -> unsat */
  if (!(root = select_root(aprop, nmoves))) return -1;

  if (select_move(aprop, root, &input, &assignment))
  {
    BZLA_AIGPROPLOG(1, "");
    BZLA_AIGPROPLOG(1, "*** move");
#ifndef NDEBUG
    int32_t a = bzla_aigprop_get_assignment_aig(aprop, input);
    BZLA_AIGPROPLOG(1,
                    "    * input: %s%d",
                    BZLA_IS_INVERTED_AIG(input) ? "-" : "",
                    BZLA_REAL_ADDR_AIG(input)->id);
    BZLA_AIGPROPLOG(1, "      prev. assignment: %d", a);
    BZLA_AIGPROPLOG(1, "      new   assignment: %d", assignment);
#endif
    update_cone(aprop, input, assignment);
    aprop->stats.moves += 1;
    return 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

// TODO termination callback?
int32_t
bzla_aigprop_sat(BzlaAIGProp *aprop, BzlaIntHashTable *roots)
{
  assert(aprop);
  assert(roots);

  double start;
  int32_t i, j, max_steps, sat_result, rootid, childid, move_res;
  uint32_t nmoves;
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache;
  BzlaIntHashTableIterator it;
  BzlaHashTableData *d;
  BzlaAIGPtrStack stack;
  BzlaIntStack *childparents;
  BzlaAIG *root, *cur, *child;

  start      = bzla_util_time_stamp();
  sat_result = BZLA_AIGPROP_UNKNOWN;
  nmoves     = 0;

  mm           = aprop->mm;
  aprop->roots = roots;

  /* collect parents (for cone computation) */
  BZLA_INIT_STACK(mm, stack);
  cache = bzla_hashint_map_new(mm);
  assert(!aprop->parents);
  aprop->parents = bzla_hashint_map_new(mm);

  bzla_iter_hashint_init(&it, roots);
  while (bzla_iter_hashint_has_next(&it))
  {
    cur = bzla_aig_get_by_id(aprop->amgr, bzla_iter_hashint_next(&it));
    if (bzla_aig_is_const(cur)) continue;
    BZLA_PUSH_STACK(stack, cur);
  }

  while (!BZLA_EMPTY_STACK(stack))
  {
    cur = BZLA_REAL_ADDR_AIG(BZLA_POP_STACK(stack));
    assert(!bzla_aig_is_const(cur));

    if ((d = bzla_hashint_map_get(cache, cur->id)) && d->as_int == 1) continue;

    if (!d)
    {
      bzla_hashint_map_add(cache, cur->id);
      BZLA_PUSH_STACK(stack, cur);
      BZLA_NEW(mm, childparents);
      BZLA_INIT_STACK(mm, *childparents);
      bzla_hashint_map_add(aprop->parents, cur->id)->as_ptr = childparents;
      if (bzla_aig_is_and(cur))
      {
        for (i = 0; i < 2; i++)
        {
          child = bzla_aig_get_by_id(aprop->amgr, cur->children[i]);
          if (!bzla_aig_is_const(child)) BZLA_PUSH_STACK(stack, child);
        }
      }
    }
    else
    {
      assert(d->as_int == 0);
      d->as_int = 1;
      if (bzla_aig_is_var(cur)) continue;
      for (i = 0; i < 2; i++)
      {
        if (bzla_aig_is_const(
                bzla_aig_get_by_id(aprop->amgr, cur->children[i])))
          continue;
        childid = cur->children[i] < 0 ? -cur->children[i] : cur->children[i];
        assert(bzla_hashint_map_contains(aprop->parents, childid));
        childparents = bzla_hashint_map_get(aprop->parents, childid)->as_ptr;
        assert(childparents);
        BZLA_PUSH_STACK(*childparents, cur->id);
      }
    }
  }
  bzla_hashint_map_delete(cache);
  BZLA_RELEASE_STACK(stack);

  /* generate initial model, all inputs are initialized with false */
  bzla_aigprop_generate_model(aprop, true);

  for (;;)
  {
    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert(!aprop->unsatroots);
    aprop->unsatroots = bzla_hashint_map_new(mm);
    bzla_iter_hashint_init(&it, roots);
    while (bzla_iter_hashint_has_next(&it))
    {
      rootid = bzla_iter_hashint_next(&it);
      root   = bzla_aig_get_by_id(aprop->amgr, rootid);
      if (bzla_aig_is_true(root)) continue;
      if (bzla_aig_is_false(root)) goto UNSAT;
      if (bzla_hashint_table_contains(aprop->roots, -rootid)) goto UNSAT;
      assert(bzla_aigprop_get_assignment_aig(aprop, root));
      if (!bzla_hashint_map_contains(aprop->unsatroots, rootid)
          && bzla_aigprop_get_assignment_aig(aprop, root) == -1)
        bzla_hashint_map_add(aprop->unsatroots, rootid);
    }

    /* compute initial score */
    compute_scores(aprop);

    if (!aprop->unsatroots->count) goto SAT;

    for (j = 0, max_steps = BZLA_AIGPROP_MAXSTEPS(aprop->stats.restarts + 1);
         !aprop->use_restarts || j < max_steps;
         j++)
    {
      move_res = move(aprop, nmoves);
      if (move_res == -1)
        goto UNSAT;
      else if (move_res == 0)
        goto UNKNOWN;
      assert(move_res == 1);
      nmoves += 1;
      if (!aprop->unsatroots->count) goto SAT;
    }

    /* restart */
    bzla_aigprop_generate_model(aprop, true);
    bzla_hashint_map_delete(aprop->score);
    aprop->score = 0;
    bzla_hashint_map_delete(aprop->unsatroots);
    aprop->unsatroots = 0;
    aprop->stats.restarts += 1;
  }
SAT:
  sat_result = BZLA_AIGPROP_SAT;
  goto DONE;
UNSAT:
  sat_result = BZLA_AIGPROP_UNSAT;
  goto DONE;
UNKNOWN:
  sat_result = BZLA_AIGPROP_UNKNOWN;
DONE:
  bzla_iter_hashint_init(&it, aprop->parents);
  while (bzla_iter_hashint_has_next(&it))
  {
    childparents = bzla_iter_hashint_next_data(&it)->as_ptr;
    assert(childparents);
    BZLA_RELEASE_STACK(*childparents);
    BZLA_DELETE(mm, childparents);
  }
  bzla_hashint_map_delete(aprop->parents);
  aprop->parents = 0;
  if (aprop->unsatroots) bzla_hashint_map_delete(aprop->unsatroots);
  aprop->unsatroots = 0;
  aprop->roots      = 0;
  if (aprop->score) bzla_hashint_map_delete(aprop->score);
  aprop->score = 0;

  aprop->time.sat += bzla_util_time_stamp() - start;
  return sat_result;
}

BzlaAIGProp *
bzla_aigprop_clone_aigprop(BzlaAIGMgr *clone, BzlaAIGProp *aprop)
{
  assert(clone);

  BzlaAIGProp *res;
  BzlaMemMgr *mm;

  if (!aprop) return 0;

  mm = bzla_mem_mgr_new();
  BZLA_CNEW(mm, res);
  memcpy(res, aprop, sizeof(BzlaAIGProp));
  res->mm   = mm;
  res->rng  = bzla_rng_clone(aprop->rng, mm);
  res->amgr = clone;
  res->unsatroots =
      bzla_hashint_map_clone(mm, aprop->unsatroots, bzla_clone_data_as_int, 0);
  res->score =
      bzla_hashint_map_clone(mm, aprop->score, bzla_clone_data_as_dbl, 0);
  res->model =
      bzla_hashint_map_clone(mm, aprop->model, bzla_clone_data_as_int, 0);
  return res;
}

BzlaAIGProp *
bzla_aigprop_new_aigprop(BzlaAIGMgr *amgr,
                         uint32_t loglevel,
                         uint32_t seed,
                         uint32_t use_restarts,
                         uint32_t use_bandit,
                         uint64_t nprops)
{
  assert(amgr);

  BzlaAIGProp *res;
  BzlaMemMgr *mm;

  mm = bzla_mem_mgr_new();
  BZLA_CNEW(mm, res);
  res->amgr         = amgr;
  res->mm           = mm;
  res->rng          = bzla_rng_new(res->mm, seed);
  res->loglevel     = loglevel;
  res->seed         = seed;
  res->use_restarts = use_restarts;
  res->use_bandit   = use_bandit;
  res->nprops       = nprops;

  return res;
}

void
bzla_aigprop_delete_aigprop(BzlaAIGProp *aprop)
{
  assert(aprop);
  BzlaMemMgr *mm;

  bzla_rng_delete(aprop->rng);
  if (aprop->unsatroots) bzla_hashint_map_delete(aprop->unsatroots);
  if (aprop->score) bzla_hashint_map_delete(aprop->score);
  if (aprop->model) bzla_hashint_map_delete(aprop->model);
  mm = aprop->mm;
  BZLA_DELETE(mm, aprop);
  bzla_mem_mgr_delete(mm);
}

#if 0
void
bzla_aigprop_print_stats (BzlaAIGProp * aprop)
{
  assert (aprop);
  msg ("");
  msg ("restarts: %d", aprop->stats.restarts);
  msg ("moves: %d", aprop->stats.moves);
}

void
bzla_aigprop_print_time_stats (BzlaAIGProp * aprop)
{
  assert (aprop);
  msg ("");
  msg ("%.2f seconds for sat call (AIG propagation)", aprop->time.sat);
}
#endif
