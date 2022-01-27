/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaslvsls.h"

#include <math.h>

#include "bzlabv.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlalsutils.h"
#include "bzlamodel.h"
#include "bzlaprintmodel.h"
#include "bzlaproputils.h"
#include "bzlaslsutils.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlanodemap.h"
#include "utils/bzlautil.h"

/* same restart scheme as in Z3 */
#define BZLA_SLS_MAXSTEPS_CFACT 100 /* same as in Z3 (c4) */
#define BZLA_SLS_MAXSTEPS(i) \
  (BZLA_SLS_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BZLA_SLS_SELECT_CFACT 20 /* same as in Z3 (c2) */

#define BZLA_SLS_PROB_SCORE_F 50 /* = 0.05 (same as in Z3 (sp)) */

/* choose move with one candidate rather than group-wise move
 * for random walk (prob=0.05) */
#define BZLA_SLS_PROB_SINGLE_VS_GW 50
/* randomize all candidates rather than one only (prob=0.5) */
#define BZLA_SLS_PROB_RAND_ALL_VS_ONE 500
/* start ranges from MSB rather than LSB (prob=0.5) */
#define BZLA_SLS_PROB_RANGE_MSB_VS_LSB 500
/* start segments from MSB rather than LSB (prob=0.5) */
#define BZLA_SLS_PROB_SEG_MSB_VS_LSB 500

/*------------------------------------------------------------------------*/

static double
compute_sls_score_formula(Bzla *bzla, BzlaIntHashTable *score, bool *done)
{
  assert(bzla);
  assert(score);

  double res, sc, weight;
  int32_t id;
  BzlaSLSSolver *slv;
  BzlaIntHashTableIterator it;

  slv = BZLA_SLS_SOLVER(bzla);
  assert(slv);
  assert(slv->roots);
  assert(slv->weights);

  res = 0.0;
  if (done) *done = true;

  bzla_iter_hashint_init(&it, slv->weights);
  while (bzla_iter_hashint_has_next(&it))
  {
    weight =
        (double) ((BzlaSLSConstrData *) slv->weights->data[it.cur_pos].as_ptr)
            ->weight;
    id = bzla_iter_hashint_next(&it);
    sc = bzla_hashint_map_get(score, id)->as_dbl;
    assert(sc >= 0.0 && sc <= 1.0);
    if (done && sc < 1.0) *done = false;
    res += weight * sc;
  }
  return res;
}

static BzlaNode *
select_candidate_constraint(Bzla *bzla, uint32_t nmoves)
{
  assert(bzla);

  double score;
  int32_t id;
  BzlaNode *res;
  BzlaSLSSolver *slv;
  BzlaIntHashTableIterator it;

  slv = BZLA_SLS_SOLVER(bzla);
  assert(slv);
  assert(slv->roots);
  assert(slv->score);

  res = 0;

  if (bzla_opt_get(bzla, BZLA_OPT_SLS_USE_BANDIT))
  {
    double value, max_value;
    BzlaSLSConstrData *d;

    max_value = 0.0;
    bzla_iter_hashint_init(&it, slv->roots);
    while (bzla_iter_hashint_has_next(&it))
    {
      id = bzla_iter_hashint_next(&it);
      assert(!bzla_node_is_bv_const(bzla_node_get_by_id(bzla, id))
             || !bzla_bv_is_zero(
                 bzla_model_get_bv(bzla, bzla_node_get_by_id(bzla, id))));
      assert(bzla_hashint_map_contains(slv->weights, id));
      d = bzla_hashint_map_get(slv->weights, id)->as_ptr;
      assert(d);
      assert(bzla_hashint_map_contains(slv->score, id));
      score = bzla_hashint_map_get(slv->score, id)->as_dbl;
      assert(score < 1.0);
      value = score + BZLA_SLS_SELECT_CFACT * sqrt(log(d->selected) / nmoves);
      if (!res || value > max_value)
      {
        res       = bzla_node_get_by_id(bzla, id);
        max_value = value;
        d->selected += 1;
      }
    }
  }
  else
  {
    uint32_t r;
    BzlaNode *cur;
    BzlaNodePtrStack stack;

    BZLA_INIT_STACK(bzla->mm, stack);
    bzla_iter_hashint_init(&it, slv->roots);
    while (bzla_iter_hashint_has_next(&it))
    {
      id  = bzla_iter_hashint_next(&it);
      cur = bzla_node_get_by_id(bzla, id);
      assert(!bzla_node_is_bv_const(cur)
             || !bzla_bv_is_zero(bzla_model_get_bv(bzla, cur)));
      assert(bzla_hashint_map_contains(slv->score, id));
      score = bzla_hashint_map_get(slv->score, id)->as_dbl;
      assert(score < 1.0);
      BZLA_PUSH_STACK(stack, cur);
    }
    assert(BZLA_COUNT_STACK(stack));
    r   = bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(stack) - 1);
    res = stack.start[r];
    BZLA_RELEASE_STACK(stack);
  }

  assert(res);

  BZLALOG(1, "");
  BZLALOG(1, "*** select candidate constraint: %s", bzla_util_node2string(res));

  return res;
}

static void
select_candidates(Bzla *bzla, BzlaNode *root, BzlaNodePtrStack *candidates)
{
  assert(bzla);
  assert(root);
  assert(candidates);

  uint32_t i;
  BzlaNode *cur, *real_cur, *e;
  BzlaNodePtrStack stack, controlling;
  const BzlaBitVector *bv;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;

  BZLALOG(1, "");
  BZLALOG(1, "*** select candidates");

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, controlling);

  BZLA_RESET_STACK(*candidates);
  mark = bzla_hashint_table_new(mm);

  BZLA_PUSH_STACK(stack, root);
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = bzla_node_real_addr(cur);
    if (bzla_hashint_table_contains(mark, real_cur->id)) continue;
    bzla_hashint_table_add(mark, real_cur->id);

    if (bzla_lsutils_is_leaf_node(real_cur))
    {
      BZLA_PUSH_STACK(*candidates, real_cur);
      BZLALOG(1, "  %s", bzla_util_node2string(real_cur));
      continue;
    }

    /* push children */
    if (bzla_opt_get(bzla, BZLA_OPT_SLS_JUST) && bzla_node_is_bv_and(real_cur)
        && bzla_node_bv_get_width(bzla, real_cur) == 1)
    {
      bv = bzla_model_get_bv(bzla, real_cur);
      if (!bzla_bv_is_zero(bv)) /* push all */
        goto PUSH_CHILDREN;
      else /* push one controlling input */
      {
        BZLA_RESET_STACK(controlling);
        for (i = 0; i < real_cur->arity; i++)
        {
          e = real_cur->e[i];
          if (bzla_bv_is_zero(bzla_model_get_bv(bzla, e)))
            BZLA_PUSH_STACK(controlling, real_cur->e[i]);
        }
        assert(BZLA_COUNT_STACK(controlling));
        BZLA_PUSH_STACK(
            stack,
            BZLA_PEEK_STACK(
                controlling,
                bzla_rng_pick_rand(
                    bzla->rng, 0, BZLA_COUNT_STACK(controlling) - 1)));
      }
    }
    else
    {
    PUSH_CHILDREN:
      for (i = 0; i < real_cur->arity; i++)
        BZLA_PUSH_STACK(stack, real_cur->e[i]);
    }
  }

  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(controlling);
  bzla_hashint_table_delete(mark);
}

#if 0
static void *
same_node (BzlaMemMgr * mm, const void * map, const void * key)
{
  assert (mm);
  assert (key);

  (void) mm;
  (void) map;
  return (BzlaNode *) key;
}
#endif

static inline void
update_assertion_weights(Bzla *bzla)
{
  assert(bzla);

  int32_t id;
  BzlaSLSConstrData *d;
  BzlaIntHashTableIterator it;
  BzlaSLSSolver *slv;

  slv = BZLA_SLS_SOLVER(bzla);

  if (bzla_rng_pick_with_prob(bzla->rng, BZLA_SLS_PROB_SCORE_F))
  {
    /* decrease the weight of all satisfied assertions */
    bzla_iter_hashint_init(&it, slv->weights);
    while (bzla_iter_hashint_has_next(&it))
    {
      d  = (BzlaSLSConstrData *) slv->weights->data[it.cur_pos].as_ptr;
      id = bzla_iter_hashint_next(&it);
      assert(bzla_hashint_table_contains(slv->score, id));
      if (bzla_hashint_map_get(slv->score, id)->as_dbl == 0.0) continue;
      if (d->weight > 1) d->weight -= 1;
    }
  }
  else
  {
    /* increase the weight of all unsatisfied assertions */
    bzla_iter_hashint_init(&it, slv->weights);
    while (bzla_iter_hashint_has_next(&it))
    {
      d  = (BzlaSLSConstrData *) slv->weights->data[it.cur_pos].as_ptr;
      id = bzla_iter_hashint_next(&it);
      assert(bzla_hashint_table_contains(slv->score, id));
      if (bzla_hashint_map_get(slv->score, id)->as_dbl == 1.0) continue;
      d->weight += 1;
    }
  }
}

static inline double
try_move(Bzla *bzla,
         BzlaIntHashTable *bv_model,
         BzlaIntHashTable *score,
         BzlaIntHashTable *cans,
         bool *done)
{
  assert(bzla);
  assert(bv_model);
  assert(score);
  assert(cans);
  assert(cans->count);
  assert(done);

  BzlaSLSSolver *slv;

  slv = BZLA_SLS_SOLVER(bzla);
  assert(slv);
  if (slv->nflips && slv->stats.flips >= slv->nflips)
  {
    slv->terminate = true;
    return 0.0;
  }
  slv->stats.flips += 1;

#ifndef NBZLALOG
  char *a;
  BzlaNode *can;
  BzlaBitVector *prev_ass, *new_ass;
  BzlaIntHashTableIterator iit;

  BZLALOG(2, "");
  BZLALOG(2, "  * try move:");
  bzla_iter_hashint_init(&iit, cans);
  while (bzla_iter_hashint_has_next(&iit))
  {
    new_ass  = (BzlaBitVector *) cans->data[iit.cur_pos].as_ptr;
    can      = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&iit));
    prev_ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
    BZLALOG(2,
            "      candidate: %s%s",
            bzla_node_is_regular(can) ? "" : "-",
            bzla_util_node2string(can));
    a = bzla_bv_to_char(bzla->mm, prev_ass);
    BZLALOG(2, "        prev. assignment: %s", a);
    bzla_mem_freestr(bzla->mm, a);
    a = bzla_bv_to_char(bzla->mm, new_ass);
    BZLALOG(2, "        new   assignment: %s", a);
    bzla_mem_freestr(bzla->mm, a);
  }
#endif

  bzla_lsutils_update_cone(bzla,
                           bv_model,
                           slv->roots,
                           score,
                           cans,
                           false,
                           &slv->stats.updates,
                           &slv->time.update_cone,
                           &slv->time.update_cone_reset,
                           &slv->time.update_cone_model_gen,
                           &slv->time.update_cone_compute_score);

  return compute_sls_score_formula(bzla, score, done);
}

static int32_t
cmp_sls_moves_qsort(const void *move1, const void *move2)
{
  BzlaSLSMove *m1, *m2;

  m1 = *((BzlaSLSMove **) move1);
  m2 = *((BzlaSLSMove **) move2);
  if (m1->sc > m2->sc) return 1;
  if (m1->sc < m2->sc) return -1;
  return 0;
}

#define BZLA_SLS_DELETE_CANS(cans)                                       \
  do                                                                     \
  {                                                                      \
    bzla_iter_hashint_init(&iit, cans);                                  \
    while (bzla_iter_hashint_has_next(&iit))                             \
    {                                                                    \
      assert(cans->data[iit.cur_pos].as_ptr);                            \
      bzla_bv_free(bzla->mm, bzla_iter_hashint_next_data(&iit)->as_ptr); \
    }                                                                    \
    bzla_hashint_map_delete(cans);                                       \
  } while (0)

#define BZLA_SLS_SELECT_MOVE_CHECK_SCORE(sc)                                 \
  do                                                                         \
  {                                                                          \
    if (done                                                                 \
        || (sls_strat != BZLA_SLS_STRAT_RAND_WALK                            \
            && ((sc) > slv->max_score                                        \
                || (sls_strat == BZLA_SLS_STRAT_BEST_SAME_MOVE               \
                    && (sc) == slv->max_score))))                            \
    {                                                                        \
      slv->max_score = (sc);                                                 \
      slv->max_move  = mk;                                                   \
      slv->max_gw    = gw;                                                   \
      if (slv->max_cans->count)                                              \
      {                                                                      \
        bzla_iter_hashint_init(&iit, slv->max_cans);                         \
        while (bzla_iter_hashint_has_next(&iit))                             \
        {                                                                    \
          assert(slv->max_cans->data[iit.cur_pos].as_ptr);                   \
          bzla_bv_free(bzla->mm, bzla_iter_hashint_next_data(&iit)->as_ptr); \
        }                                                                    \
      }                                                                      \
      bzla_hashint_map_delete(slv->max_cans);                                \
      slv->max_cans = cans;                                                  \
      if (done || sls_strat == BZLA_SLS_STRAT_FIRST_BEST_MOVE) goto DONE;    \
    }                                                                        \
    else if (sls_strat == BZLA_SLS_STRAT_RAND_WALK)                          \
    {                                                                        \
      BZLA_NEW(bzla->mm, m);                                                 \
      m->cans = cans;                                                        \
      m->sc   = (sc);                                                        \
      BZLA_PUSH_STACK(slv->moves, m);                                        \
      slv->sum_score += m->sc;                                               \
    }                                                                        \
    else                                                                     \
    {                                                                        \
      BZLA_SLS_DELETE_CANS(cans);                                            \
    }                                                                        \
  } while (0)

static inline bool
select_inc_dec_not_move(Bzla *bzla,
                        BzlaBitVector *(*fun)(BzlaMemMgr *,
                                              const BzlaBitVector *),
                        BzlaNodePtrStack *candidates,
                        int32_t gw)
{
  size_t i;
  uint32_t sls_strat;
  bool done;
  double sc;
  BzlaSLSMove *m;
  BzlaSLSMoveKind mk;
  BzlaBitVector *ass, *max_neigh;
  BzlaNode *can;
  BzlaIntHashTable *cans, *bv_model, *score;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;

  done      = false;
  slv       = BZLA_SLS_SOLVER(bzla);
  sls_strat = bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY);

  if (fun == bzla_bv_inc)
    mk = BZLA_SLS_MOVE_INC;
  else if (fun == bzla_bv_dec)
    mk = BZLA_SLS_MOVE_DEC;
  else
  {
    assert(fun == bzla_bv_not);
    mk = BZLA_SLS_MOVE_NOT;
  }

  bv_model = bzla_model_clone_bv(bzla, bzla->bv_model, true);
  score =
      bzla_hashint_map_clone(bzla->mm, slv->score, bzla_clone_data_as_dbl, 0);

  cans = bzla_hashint_map_new(bzla->mm);

  for (i = 0; i < BZLA_COUNT_STACK(*candidates); i++)
  {
    can = BZLA_PEEK_STACK(*candidates, i);
    assert(can);
    assert(bzla_node_is_regular(can));

    ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
    assert(ass);

    max_neigh = bzla_hashint_map_contains(slv->max_cans, can->id)
                    ? bzla_hashint_map_get(slv->max_cans, can->id)->as_ptr
                    : 0;

    bzla_hashint_map_add(cans, can->id)->as_ptr =
        bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
            ? fun(bzla->mm, max_neigh)
            : fun(bzla->mm, ass);
  }

  sc = try_move(bzla, bv_model, score, cans, &done);
  if (slv->terminate)
  {
    BZLA_SLS_DELETE_CANS(cans);
    goto DONE;
  }
  BZLA_SLS_SELECT_MOVE_CHECK_SCORE(sc);

DONE:
  bzla_model_delete_bv(bzla, &bv_model);
  bzla_hashint_map_delete(score);
  return done;
}

static inline bool
select_flip_move(Bzla *bzla, BzlaNodePtrStack *candidates, int32_t gw)
{
  size_t i, n_endpos;
  uint32_t pos, cpos, sls_strat;
  bool done = false;
  double sc;
  BzlaSLSMove *m;
  BzlaSLSMoveKind mk;
  BzlaBitVector *ass, *max_neigh;
  BzlaNode *can;
  BzlaIntHashTable *cans, *bv_model, *score;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;

  slv       = BZLA_SLS_SOLVER(bzla);
  sls_strat = bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY);

  mk = BZLA_SLS_MOVE_FLIP;

  bv_model = bzla_model_clone_bv(bzla, bzla->bv_model, true);
  score =
      bzla_hashint_map_clone(bzla->mm, slv->score, bzla_clone_data_as_dbl, 0);

  for (pos = 0, n_endpos = 0; n_endpos < BZLA_COUNT_STACK(*candidates); pos++)
  {
    cans = bzla_hashint_map_new(bzla->mm);

    for (i = 0; i < BZLA_COUNT_STACK(*candidates); i++)
    {
      can = BZLA_PEEK_STACK(*candidates, i);
      assert(bzla_node_is_regular(can));
      assert(can);

      ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
      assert(ass);

      max_neigh = bzla_hashint_map_contains(slv->max_cans, can->id)
                      ? bzla_hashint_map_get(slv->max_cans, can->id)->as_ptr
                      : 0;

      if (pos == bzla_bv_get_width(ass) - 1) n_endpos += 1;
      cpos = pos % bzla_bv_get_width(ass);

      bzla_hashint_map_add(cans, can->id)->as_ptr =
          bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
              ? bzla_bv_flipped_bit(bzla->mm, max_neigh, cpos)
              : bzla_bv_flipped_bit(bzla->mm, ass, cpos);
    }

    sc = try_move(bzla, bv_model, score, cans, &done);
    if (slv->terminate)
    {
      BZLA_SLS_DELETE_CANS(cans);
      goto DONE;
    }
    BZLA_SLS_SELECT_MOVE_CHECK_SCORE(sc);
  }

DONE:
  bzla_model_delete_bv(bzla, &bv_model);
  bzla_hashint_map_delete(score);
  return done;
}

static inline bool
select_flip_range_move(Bzla *bzla, BzlaNodePtrStack *candidates, int32_t gw)
{
  size_t i, n_endpos;
  uint32_t up, cup, clo, sls_strat, bw;
  bool done = false;
  double sc;
  BzlaSLSMove *m;
  BzlaSLSMoveKind mk;
  BzlaBitVector *ass, *max_neigh;
  BzlaNode *can;
  BzlaIntHashTable *cans, *bv_model, *score;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;

  slv       = BZLA_SLS_SOLVER(bzla);
  sls_strat = bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY);

  mk = BZLA_SLS_MOVE_FLIP_RANGE;

  bv_model = bzla_model_clone_bv(bzla, bzla->bv_model, true);
  score =
      bzla_hashint_map_clone(bzla->mm, slv->score, bzla_clone_data_as_dbl, 0);

  for (up = 1, n_endpos = 0; n_endpos < BZLA_COUNT_STACK(*candidates);
       up = 2 * up + 1)
  {
    cans = bzla_hashint_map_new(bzla->mm);

    for (i = 0; i < BZLA_COUNT_STACK(*candidates); i++)
    {
      can = BZLA_PEEK_STACK(*candidates, i);
      assert(can);
      assert(bzla_node_is_regular(can));

      ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
      assert(ass);

      max_neigh = bzla_hashint_map_contains(slv->max_cans, can->id)
                      ? bzla_hashint_map_get(slv->max_cans, can->id)->as_ptr
                      : 0;

      clo = 0;
      cup = up;
      bw  = bzla_bv_get_width(ass);

      if (up >= bw)
      {
        if ((up - 1) / 2 < bw) n_endpos += 1;
        cup = bw - 1;
      }

      /* range from MSB rather than LSB with given prob */
      if (bzla_rng_pick_with_prob(bzla->rng, BZLA_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = bw - 1 - cup;
        cup = bw - 1;
      }

      bzla_hashint_map_add(cans, can->id)->as_ptr =
          bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
              ? bzla_bv_flipped_bit_range(bzla->mm, max_neigh, cup, clo)
              : bzla_bv_flipped_bit_range(bzla->mm, ass, cup, clo);
    }

    sc = try_move(bzla, bv_model, score, cans, &done);
    if (slv->terminate)
    {
      BZLA_SLS_DELETE_CANS(cans);
      goto DONE;
    }
    BZLA_SLS_SELECT_MOVE_CHECK_SCORE(sc);
  }

DONE:
  bzla_model_delete_bv(bzla, &bv_model);
  bzla_hashint_map_delete(score);
  return done;
}

static inline bool
select_flip_segment_move(Bzla *bzla, BzlaNodePtrStack *candidates, int32_t gw)
{
  size_t i, n_endpos;
  int32_t ctmp;
  uint32_t lo, clo, up, cup, seg, sls_strat, bw;
  bool done = false;
  double sc;
  BzlaSLSMove *m;
  BzlaSLSMoveKind mk;
  BzlaBitVector *ass, *max_neigh;
  BzlaNode *can;
  BzlaIntHashTable *cans, *bv_model, *score;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;

  slv       = BZLA_SLS_SOLVER(bzla);
  sls_strat = bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY);

  mk = BZLA_SLS_MOVE_FLIP_SEGMENT;

  bv_model = bzla_model_clone_bv(bzla, bzla->bv_model, true);
  score =
      bzla_hashint_map_clone(bzla->mm, slv->score, bzla_clone_data_as_dbl, 0);

  for (seg = 2; seg <= 8; seg <<= 1)
  {
    for (lo = 0, up = seg - 1, n_endpos = 0;
         n_endpos < BZLA_COUNT_STACK(*candidates);
         lo += seg, up += seg)
    {
      cans = bzla_hashint_map_new(bzla->mm);

      for (i = 0; i < BZLA_COUNT_STACK(*candidates); i++)
      {
        can = BZLA_PEEK_STACK(*candidates, i);
        assert(can);
        assert(bzla_node_is_regular(can));

        ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
        assert(ass);

        max_neigh = bzla_hashint_map_contains(slv->max_cans, can->id)
                        ? bzla_hashint_map_get(slv->max_cans, can->id)->as_ptr
                        : 0;

        clo = lo;
        cup = up;
        bw  = bzla_bv_get_width(ass);

        if (up >= bw)
        {
          if (up - seg < bw) n_endpos += 1;
          cup = bw - 1;
        }

        if (lo >= bw - 1) clo = bw < seg ? 0 : bw - seg;

        /* range from MSB rather than LSB with given prob */
        if (bzla_rng_pick_with_prob(bzla->rng, BZLA_SLS_PROB_SEG_MSB_VS_LSB))
        {
          ctmp = clo;
          clo  = bw - 1 - cup;
          cup  = bw - 1 - ctmp;
        }

        bzla_hashint_map_add(cans, can->id)->as_ptr =
            bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
                ? bzla_bv_flipped_bit_range(bzla->mm, max_neigh, cup, clo)
                : bzla_bv_flipped_bit_range(bzla->mm, ass, cup, clo);
      }

      sc = try_move(bzla, bv_model, score, cans, &done);
      if (slv->terminate)
      {
        BZLA_SLS_DELETE_CANS(cans);
        goto DONE;
      }
      BZLA_SLS_SELECT_MOVE_CHECK_SCORE(sc);
    }
  }

DONE:
  bzla_model_delete_bv(bzla, &bv_model);
  bzla_hashint_map_delete(score);
  return done;
}

static inline bool
select_rand_range_move(Bzla *bzla, BzlaNodePtrStack *candidates, int32_t gw)
{
  double sc, rand_max_score = -1.0;
  size_t i, n_endpos;
  uint32_t up, cup, clo, sls_strat, bw;
  bool done;
  BzlaSLSMove *m;
  BzlaSLSMoveKind mk;
  BzlaBitVector *ass;
  BzlaNode *can;
  BzlaIntHashTable *cans, *bv_model, *score;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;

  done      = false;
  slv       = BZLA_SLS_SOLVER(bzla);
  sls_strat = bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY);

  mk = BZLA_SLS_MOVE_RAND;

  bv_model = bzla_model_clone_bv(bzla, bzla->bv_model, true);
  score =
      bzla_hashint_map_clone(bzla->mm, slv->score, bzla_clone_data_as_dbl, 0);

  for (up = 1, n_endpos = 0; n_endpos < BZLA_COUNT_STACK(*candidates);
       up = 2 * up + 1)
  {
    cans = bzla_hashint_map_new(bzla->mm);

    for (i = 0; i < BZLA_COUNT_STACK(*candidates); i++)
    {
      can = BZLA_PEEK_STACK(*candidates, i);
      assert(can);
      assert(bzla_node_is_regular(can));

      ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
      assert(ass);

      clo = 0;
      cup = up;
      bw  = bzla_bv_get_width(ass);
      if (up >= bw)
      {
        if ((up - 1) / 2 < bw) n_endpos += 1;
        cup = bw - 1;
      }

      /* range from MSB rather than LSB with given prob */
      if (bzla_rng_pick_with_prob(bzla->rng, BZLA_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = bw - 1 - cup;
        cup = bw - 1;
      }
      bzla_hashint_map_add(cans, can->id)->as_ptr =
          bzla_bv_new_random_bit_range(bzla->mm, bzla->rng, bw, cup, clo);
    }

    sc = try_move(bzla, bv_model, score, cans, &done);
    if (slv->terminate)
    {
      BZLA_SLS_DELETE_CANS(cans);
      goto DONE;
    }
    if (rand_max_score == -1.0 || sc > rand_max_score)
    {
      /* reset, use current */
      slv->max_score = -1.0;
      rand_max_score = sc;
    }
    BZLA_SLS_SELECT_MOVE_CHECK_SCORE(sc);
  }

DONE:
  bzla_model_delete_bv(bzla, &bv_model);
  bzla_hashint_map_delete(score);
  return done;
}

static inline bool
select_move_aux(Bzla *bzla, BzlaNodePtrStack *candidates, int32_t gw)
{
  assert(bzla);
  assert(candidates);
  assert(gw >= 0);

  BzlaSLSMoveKind mk;
  BzlaSLSSolver *slv;
  bool done = false;

  slv = BZLA_SLS_SOLVER(bzla);

  for (mk = 0; mk < BZLA_SLS_MOVE_DONE; mk++)
  {
    if (slv->nflips && slv->stats.flips >= slv->nflips)
    {
      slv->terminate = true;
      break;
    }

    switch (mk)
    {
      case BZLA_SLS_MOVE_INC:
        if ((done = select_inc_dec_not_move(bzla, bzla_bv_inc, candidates, gw)))
          return done;
        break;

      case BZLA_SLS_MOVE_DEC:
        if ((done = select_inc_dec_not_move(bzla, bzla_bv_dec, candidates, gw)))
          return done;
        break;

      case BZLA_SLS_MOVE_NOT:
        if ((done = select_inc_dec_not_move(bzla, bzla_bv_not, candidates, gw)))
          return done;
        break;

      case BZLA_SLS_MOVE_FLIP_RANGE:
        if (!bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_RANGE)) continue;
        if ((done = select_flip_range_move(bzla, candidates, gw))) return done;
        break;

      case BZLA_SLS_MOVE_FLIP_SEGMENT:
        if (!bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_SEGMENT)) continue;
        if ((done = select_flip_segment_move(bzla, candidates, gw)))
          return done;
        break;

      default:
        assert(mk == BZLA_SLS_MOVE_FLIP);
        if ((done = select_flip_move(bzla, candidates, gw))) return done;
    }
  }

  return done;
}

static inline void
select_move(Bzla *bzla, BzlaNodePtrStack *candidates)
{
  assert(bzla);
  assert(candidates);

  size_t i, r;
  bool randomizeall;
  bool done;
  double rd, sum;
  BzlaNode *can;
  BzlaBitVector *neigh;
  BzlaNodePtrStack cans;
  BzlaSLSMove *m;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;

  slv = BZLA_SLS_SOLVER(bzla);
  assert(slv->max_cans);
  assert(!slv->max_cans->count);

  BZLA_INIT_STACK(bzla->mm, cans);
  /* one after another */
  for (i = 0; i < BZLA_COUNT_STACK(*candidates); i++)
  {
    can = BZLA_PEEK_STACK(*candidates, i);
    assert(can);
    BZLA_PUSH_STACK(cans, can);

    if ((done = select_move_aux(bzla, &cans, 0))) goto DONE;
    if (slv->terminate) goto DONE;

    BZLA_RESET_STACK(cans);
  }

  /* groupwise */
  if (bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_GW)
      && BZLA_COUNT_STACK(*candidates) > 1)
  {
    if ((done = select_move_aux(bzla, candidates, 1))) goto DONE;
    if (slv->terminate) goto DONE;
  }

  /* select probabilistic random walk move
   * (weighted by score; the higher the score, the higher the probability
   * that a move gets chosen) */
  if (bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY) == BZLA_SLS_STRAT_RAND_WALK)
  {
    assert(slv->max_cans->count == 0);
    assert(BZLA_COUNT_STACK(slv->moves));

    qsort(slv->moves.start,
          BZLA_COUNT_STACK(slv->moves),
          sizeof(BzlaSLSMove *),
          cmp_sls_moves_qsort);

    rd = bzla_rng_pick_rand_dbl(bzla->rng, 0, slv->sum_score);
    m  = BZLA_PEEK_STACK(slv->moves, 0);
    for (i = 0, sum = 0; i < BZLA_COUNT_STACK(slv->moves); i++)
    {
      sum += m->sc;
      if (sum > rd) break;
      m = BZLA_PEEK_STACK(slv->moves, i);
    }

    slv->max_gw   = m->cans->count > 1;
    slv->max_move = BZLA_SLS_MOVE_RAND_WALK;
    bzla_iter_hashint_init(&iit, m->cans);
    while (bzla_iter_hashint_has_next(&iit))
    {
      neigh = bzla_bv_copy(bzla->mm, m->cans->data[iit.cur_pos].as_ptr);
      can   = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&iit));
      assert(bzla_node_is_regular(can));
      assert(neigh);
      bzla_hashint_map_add(slv->max_cans, can->id)->as_ptr = neigh;
    }
  }

  if (slv->max_cans->count == 0)
  {
    assert(slv->max_move == BZLA_SLS_MOVE_DONE);

    /* randomize if no best move was found */
    randomizeall =
        bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_RAND_ALL)
            ? bzla_rng_pick_with_prob(bzla->rng, BZLA_SLS_PROB_RAND_ALL_VS_ONE)
            : false;

    if (randomizeall)
    {
      slv->max_gw   = 1;
      slv->max_move = BZLA_SLS_MOVE_RAND;

      for (r = 0; r <= BZLA_COUNT_STACK(*candidates) - 1; r++)
      {
        can = BZLA_PEEK_STACK(*candidates, r);
        assert(bzla_node_is_regular(can));
        if (bzla_node_bv_get_width(bzla, can) == 1)
          neigh = bzla_bv_flipped_bit(
              bzla->mm, (BzlaBitVector *) bzla_model_get_bv(bzla, can), 0);
        else
          neigh = bzla_bv_new_random(
              bzla->mm, bzla->rng, bzla_node_bv_get_width(bzla, can));

        bzla_hashint_map_add(slv->max_cans, can->id)->as_ptr = neigh;
      }
    }
    else
    {
      slv->max_gw   = 0;
      slv->max_move = BZLA_SLS_MOVE_RAND;

      can = BZLA_PEEK_STACK(
          *candidates,
          bzla_rng_pick_rand(bzla->rng, 0, BZLA_COUNT_STACK(*candidates) - 1));
      assert(bzla_node_is_regular(can));

      if (bzla_node_bv_get_width(bzla, can) == 1)
      {
        neigh = bzla_bv_flipped_bit(
            bzla->mm, (BzlaBitVector *) bzla_model_get_bv(bzla, can), 0);
        bzla_hashint_map_add(slv->max_cans, can->id)->as_ptr = neigh;
      }
      /* pick neighbor with randomized bit range (best guess) */
      else if (bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_RAND_RANGE))
      {
        assert(!BZLA_COUNT_STACK(cans));
        BZLA_PUSH_STACK(cans, can);
        select_rand_range_move(bzla, &cans, 0);
        BZLA_RESET_STACK(cans);
        assert(slv->max_cans->count == 1);
      }
      else
      {
        neigh = bzla_bv_new_random(
            bzla->mm, bzla->rng, bzla_node_bv_get_width(bzla, can));
        bzla_hashint_map_add(slv->max_cans, can->id)->as_ptr = neigh;
      }

      assert(!slv->max_gw);
      assert(slv->max_move == BZLA_SLS_MOVE_RAND);
    }
    assert(slv->max_cans->count);
  }

DONE:
  BZLA_RELEASE_STACK(cans);
  while (!BZLA_EMPTY_STACK(slv->moves))
  {
    m = BZLA_POP_STACK(slv->moves);
    bzla_iter_hashint_init(&iit, m->cans);
    while (bzla_iter_hashint_has_next(&iit))
      bzla_bv_free(bzla->mm, bzla_iter_hashint_next_data(&iit)->as_ptr);
    bzla_hashint_map_delete(m->cans);
    BZLA_DELETE(bzla->mm, m);
  }
}

static inline void
select_random_move(Bzla *bzla, BzlaNodePtrStack *candidates)
{
  assert(bzla);
  assert(candidates);

  uint32_t i, r, up, lo, bw;
  BzlaSLSMoveKind mk;
  BzlaNodePtrStack cans, *pcans;
  BzlaNode *can;
  BzlaBitVector *ass, *neigh;
  BzlaSLSSolver *slv;

  slv = BZLA_SLS_SOLVER(bzla);
  assert(slv->max_cans);
  assert(!slv->max_cans->count);

  BZLA_INIT_STACK(bzla->mm, cans);

  slv->max_move = BZLA_SLS_MOVE_RAND_WALK;

  /* select candidate(s) */
  if (bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_GW)
      && bzla_rng_pick_with_prob(bzla->rng, BZLA_SLS_PROB_SINGLE_VS_GW))
  {
    pcans       = candidates;
    slv->max_gw = 1;
  }
  else
  {
    BZLA_PUSH_STACK(
        cans,
        BZLA_PEEK_STACK(*candidates,
                        bzla_rng_pick_rand(
                            bzla->rng, 0, BZLA_COUNT_STACK(*candidates) - 1)));
    pcans       = &cans;
    slv->max_gw = 0;
  }

  /* select neighbor(s) */
  for (i = 0; i < BZLA_COUNT_STACK(*pcans); i++)
  {
    can = BZLA_PEEK_STACK((*pcans), i);
    assert(bzla_node_is_regular(can));
    ass = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
    assert(ass);

    bw = bzla_bv_get_width(ass);
    r  = bzla_rng_pick_rand(bzla->rng, 0, BZLA_SLS_MOVE_DONE - 1 + bw - 1);

    if (r < bw)
      mk = BZLA_SLS_MOVE_FLIP;
    else
      mk = (BzlaSLSMoveKind) r - bw + 1;
    assert(mk >= 0);

    if ((!bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_SEGMENT)
         && mk == BZLA_SLS_MOVE_FLIP_SEGMENT)
        || (!bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_RANGE)
            && mk == BZLA_SLS_MOVE_FLIP_RANGE))
    {
      mk = BZLA_SLS_MOVE_FLIP;
    }

    switch (mk)
    {
      case BZLA_SLS_MOVE_INC: neigh = bzla_bv_inc(bzla->mm, ass); break;
      case BZLA_SLS_MOVE_DEC: neigh = bzla_bv_dec(bzla->mm, ass); break;
      case BZLA_SLS_MOVE_NOT: neigh = bzla_bv_not(bzla->mm, ass); break;
      case BZLA_SLS_MOVE_FLIP_RANGE:
        up    = bzla_rng_pick_rand(bzla->rng, bw > 1 ? 1 : 0, bw - 1);
        neigh = bzla_bv_flipped_bit_range(bzla->mm, ass, up, 0);
        break;
      case BZLA_SLS_MOVE_FLIP_SEGMENT:
        lo = bzla_rng_pick_rand(bzla->rng, 0, bw - 1);
        up = bzla_rng_pick_rand(bzla->rng, lo < bw - 1 ? lo + 1 : lo, bw - 1);
        neigh = bzla_bv_flipped_bit_range(bzla->mm, ass, up, lo);
        break;
      default:
        assert(mk == BZLA_SLS_MOVE_FLIP);
        neigh = bzla_bv_flipped_bit(
            bzla->mm, ass, bzla_rng_pick_rand(bzla->rng, 0, bw - 1));
        break;
    }

    bzla_hashint_map_add(slv->max_cans, can->id)->as_ptr = neigh;
  }

  BZLA_RELEASE_STACK(cans);
}

/*------------------------------------------------------------------------*/

static bool
move(Bzla *bzla, uint32_t nmoves)
{
  assert(bzla);

  uint32_t nprops, nsls;
  bool res;
  BzlaNode *constr, *can;
  BzlaNodePtrStack candidates;
  BzlaIntHashTableIterator iit;
  BzlaSLSSolver *slv;
  BzlaBitVector *neigh, *one;

  BZLALOG(1, "");
  BZLALOG(1, "*** move");

  BZLA_INIT_STACK(bzla->mm, candidates);

  slv = BZLA_SLS_SOLVER(bzla);
  assert(!slv->max_cans);
  assert(slv->roots->count);

  constr = select_candidate_constraint(bzla, nmoves);

  slv->max_cans = bzla_hashint_map_new(bzla->mm);

  res = true;

  nprops = bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_PROP_NPROPS);
  nsls   = bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_PROP_NSLSS);

  /* Always perform propagation moves first, i.e. perform moves
   * with ratio nprops:nsls of propagation to sls moves */
  if (bzla_opt_get(bzla, BZLA_OPT_SLS_STRATEGY) == BZLA_SLS_STRAT_ALWAYS_PROP
      || (bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_PROP)
          && slv->npropmoves < nprops))
  {
    slv->npropmoves += 1;
    /* Select neighbor by propagating assignments from a given candidate
     * constraint (which is forced to be true) downwards. A downward path
     * is chosen via justification. If a non-recoverable conflict is
     * encountered, no move is performed. */
    slv->max_move = BZLA_SLS_MOVE_PROP;
    one           = bzla_bv_one(bzla->mm, 1);
    slv->stats.props +=
        bzla_proputils_select_move_prop(bzla, constr, one, -1, &can, &neigh);
    bzla_bv_free(bzla->mm, one);
    if (can)
    {
      assert(neigh);
      bzla_hashint_map_add(slv->max_cans, bzla_node_real_addr(can)->id)
          ->as_ptr = neigh;
    }
    else /* recovery move */
    {
      slv->stats.move_prop_non_rec_conf += 1;
      /* force random walk if prop move fails */
      if (bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_PROP_FORCE_RW))
      {
        select_candidates(bzla, constr, &candidates);
        /* root is const false -> unsat */
        if (!BZLA_COUNT_STACK(candidates))
        {
          res = false;
          goto DONE;
        }

        goto SLS_MOVE_RAND_WALK;
      }

      goto SLS_MOVE;
    }
  }
  else
  {
    slv->nslsmoves += 1;
  SLS_MOVE:
    select_candidates(bzla, constr, &candidates);
    /* root is const false -> unsat */
    if (!BZLA_COUNT_STACK(candidates))
    {
      res = false;
      goto DONE;
    }

    slv->max_score = compute_sls_score_formula(bzla, slv->score, 0);
    slv->max_move  = BZLA_SLS_MOVE_DONE;
    slv->max_gw    = -1;

    if (bzla_opt_get(bzla, BZLA_OPT_SLS_MOVE_RAND_WALK)
        && bzla_rng_pick_with_prob(
            bzla->rng, bzla_opt_get(bzla, BZLA_OPT_SLS_PROB_MOVE_RAND_WALK)))
    {
    SLS_MOVE_RAND_WALK:
      select_random_move(bzla, &candidates);
    }
    else
    {
      select_move(bzla, &candidates);
      if (slv->terminate) goto DONE;
    }

    assert(slv->max_cans->count);
  }
  assert(slv->max_move != BZLA_SLS_MOVE_DONE);

  if (nprops == slv->npropmoves && nsls == slv->nslsmoves)
  {
    slv->npropmoves = slv->nslsmoves = 0;
  }

#ifndef NBZLALOG
  BZLALOG(1, "");
  BZLALOG(1, " * move");
  char *a;
  BzlaBitVector *ass;
  bzla_iter_hashint_init(&iit, slv->max_cans);
  while (bzla_iter_hashint_has_next(&iit))
  {
    neigh = (BzlaBitVector *) slv->max_cans->data[iit.cur_pos].as_ptr;
    can   = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&iit));
    ass   = (BzlaBitVector *) bzla_model_get_bv(bzla, can);
    a     = bzla_bv_to_char(bzla->mm, ass);
    BZLALOG(1,
            "  candidate: %s%s",
            bzla_node_is_regular(can) ? "" : "-",
            bzla_util_node2string(can));
    BZLALOG(1, "  prev. assignment: %s", a);
    bzla_mem_freestr(bzla->mm, a);
    a = bzla_bv_to_char(bzla->mm, neigh);
    BZLALOG(1, "  new   assignment: %s", a);
    bzla_mem_freestr(bzla->mm, a);
  }
#endif

  bzla_lsutils_update_cone(bzla,
                           bzla->bv_model,
                           slv->roots,
                           slv->score,
                           slv->max_cans,
                           true,
                           &slv->stats.updates,
                           &slv->time.update_cone,
                           &slv->time.update_cone_reset,
                           &slv->time.update_cone_model_gen,
                           &slv->time.update_cone_compute_score);

  slv->stats.moves += 1;

  assert(slv->max_move != BZLA_SLS_MOVE_DONE);
  assert(slv->max_gw >= 0);

  switch (slv->max_move)
  {
    case BZLA_SLS_MOVE_FLIP:
      if (!slv->max_gw)
        slv->stats.move_flip += 1;
      else
        slv->stats.move_gw_flip += 1;
      break;
    case BZLA_SLS_MOVE_INC:
      if (!slv->max_gw)
        slv->stats.move_inc += 1;
      else
        slv->stats.move_gw_inc += 1;
      break;
    case BZLA_SLS_MOVE_DEC:
      if (!slv->max_gw)
        slv->stats.move_dec += 1;
      else
        slv->stats.move_gw_dec += 1;
      break;
    case BZLA_SLS_MOVE_NOT:
      if (!slv->max_gw)
        slv->stats.move_not += 1;
      else
        slv->stats.move_gw_not += 1;
      break;
    case BZLA_SLS_MOVE_FLIP_RANGE:
      if (!slv->max_gw)
        slv->stats.move_range += 1;
      else
        slv->stats.move_gw_range += 1;
      break;
    case BZLA_SLS_MOVE_FLIP_SEGMENT:
      if (!slv->max_gw)
        slv->stats.move_seg += 1;
      else
        slv->stats.move_gw_seg += 1;
      break;
    case BZLA_SLS_MOVE_RAND:
      if (!slv->max_gw)
        slv->stats.move_rand += 1;
      else
        slv->stats.move_gw_rand += 1;
      break;
    case BZLA_SLS_MOVE_RAND_WALK:
      if (!slv->max_gw)
        slv->stats.move_rand_walk += 1;
      else
        slv->stats.move_gw_rand_walk += 1;
      break;
    default:
      assert(slv->max_move == BZLA_SLS_MOVE_PROP);
      slv->stats.move_prop += 1;
  }

  if (slv->max_move == BZLA_SLS_MOVE_RAND) update_assertion_weights(bzla);

  /** cleanup **/
DONE:
  bzla_iter_hashint_init(&iit, slv->max_cans);
  while (bzla_iter_hashint_has_next(&iit))
  {
    assert(slv->max_cans->data[iit.cur_pos].as_ptr);
    bzla_bv_free(bzla->mm, bzla_iter_hashint_next_data(&iit)->as_ptr);
  }
  bzla_hashint_map_delete(slv->max_cans);
  slv->max_cans = 0;
  BZLA_RELEASE_STACK(candidates);
  return res;
}

/*------------------------------------------------------------------------*/

static BzlaSLSSolver *
clone_sls_solver(Bzla *clone, BzlaSLSSolver *slv, BzlaNodeMap *exp_map)
{
  assert(clone);
  assert(slv);
  assert(slv->kind == BZLA_SLS_SOLVER_KIND);

  uint32_t i;
  BzlaSLSSolver *res;
  BzlaSLSMove *m, *cm;

  (void) exp_map;

  BZLA_NEW(clone->mm, res);
  memcpy(res, slv, sizeof(BzlaSLSSolver));

  res->bzla  = clone;
  res->roots = bzla_hashint_map_clone(clone->mm, slv->roots, 0, 0);
  res->score =
      bzla_hashint_map_clone(clone->mm, slv->score, bzla_clone_data_as_dbl, 0);

  BZLA_INIT_STACK(clone->mm, res->moves);
  assert(BZLA_SIZE_STACK(slv->moves) || !BZLA_COUNT_STACK(slv->moves));
  if (BZLA_SIZE_STACK(slv->moves))
  {
    BZLA_NEWN(clone->mm, res->moves.start, BZLA_SIZE_STACK(slv->moves));
    res->moves.top = res->moves.start;
    res->moves.end = res->moves.start + BZLA_SIZE_STACK(slv->moves);

    for (i = 0; i < BZLA_COUNT_STACK(slv->moves); i++)
    {
      m = BZLA_PEEK_STACK(slv->moves, i);
      assert(m);
      BZLA_NEW(clone->mm, cm);
      cm->cans = bzla_hashint_map_clone(
          clone->mm, m->cans, bzla_clone_data_as_bv_ptr, 0);
      cm->sc = m->sc;
      BZLA_PUSH_STACK(res->moves, m);
    }
  }
  assert(BZLA_COUNT_STACK(slv->moves) == BZLA_COUNT_STACK(res->moves));
  assert(BZLA_SIZE_STACK(slv->moves) == BZLA_SIZE_STACK(res->moves));

  res->max_cans = bzla_hashint_map_clone(
      clone->mm, slv->max_cans, bzla_clone_data_as_bv_ptr, 0);

  return res;
}

static void
delete_sls_solver(BzlaSLSSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla;
  BzlaIntHashTableIterator it;
  BzlaSLSConstrData *d;
  BzlaSLSMove *m;

  bzla = slv->bzla;

  if (slv->score) bzla_hashint_map_delete(slv->score);
  if (slv->roots) bzla_hashint_map_delete(slv->roots);
  bzla_iter_hashint_init(&it, slv->domains);
  while (bzla_iter_hashint_has_next(&it))
  {
    bzla_bvdomain_free(slv->bzla->mm, bzla_iter_hashint_next_data(&it)->as_ptr);
  }
  bzla_hashint_map_delete(slv->domains);
  if (slv->weights)
  {
    bzla_iter_hashint_init(&it, slv->weights);
    while (bzla_iter_hashint_has_next(&it))
    {
      d = bzla_iter_hashint_next_data(&it)->as_ptr;
      BZLA_DELETE(bzla->mm, d);
    }
    bzla_hashint_map_delete(slv->weights);
  }
  while (!BZLA_EMPTY_STACK(slv->moves))
  {
    m = BZLA_POP_STACK(slv->moves);
    bzla_iter_hashint_init(&it, m->cans);
    while (bzla_iter_hashint_has_next(&it))
      bzla_bv_free(bzla->mm, bzla_iter_hashint_next_data(&it)->as_ptr);
    bzla_hashint_map_delete(m->cans);
  }
  BZLA_RELEASE_STACK(slv->moves);
  if (slv->max_cans)
  {
    bzla_iter_hashint_init(&it, slv->max_cans);
    while (bzla_iter_hashint_has_next(&it))
    {
      assert(slv->max_cans->data[it.cur_pos].as_ptr);
      bzla_bv_free(bzla->mm, bzla_iter_hashint_next_data(&it)->as_ptr);
    }
    bzla_hashint_map_delete(slv->max_cans);
  }
  BZLA_DELETE(bzla->mm, slv);
}

/* Note: failed assumptions -> no handling necessary, sls only works for SAT
 * Note: limits are currently unused */
static BzlaSolverResult
sat_sls_solver(BzlaSLSSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(slv->bzla);

  int32_t j, max_steps, id, nmoves;
  uint32_t nprops;
  BzlaSolverResult sat_result;
  BzlaNode *root;
  BzlaSLSConstrData *d;
  BzlaPtrHashTableIterator pit;
  BzlaIntHashTableIterator iit;
  Bzla *bzla;

  bzla = slv->bzla;
  assert(!bzla->inconsistent);
  nmoves      = 0;
  nprops      = bzla_opt_get(bzla, BZLA_OPT_PROP_NPROPS);
  slv->nflips = bzla_opt_get(bzla, BZLA_OPT_SLS_NFLIPS);

  if (bzla_terminate(bzla))
  {
    sat_result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model((BzlaSolver *) slv, false, true);

  /* init assertion weights of ALL roots */
  assert(!slv->weights);
  slv->weights = bzla_hashint_map_new(bzla->mm);
  bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->synthesized_constraints);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    root = bzla_iter_hashptr_next(&pit);
    id   = bzla_node_get_id(root);
    if (!bzla_hashint_map_contains(slv->weights, id))
    {
      BZLA_CNEW(bzla->mm, d);
      d->weight = 1; /* initial assertion weight */
      bzla_hashint_map_add(slv->weights, id)->as_ptr = d;
    }
  }
  bzla_iter_hashptr_init(&pit, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    root = bzla_iter_hashptr_next(&pit);
    if (bzla_hashptr_table_get(bzla->unsynthesized_constraints,
                               bzla_node_invert(root)))
      goto UNSAT;
    if (bzla_hashptr_table_get(bzla->synthesized_constraints,
                               bzla_node_invert(root)))
      goto UNSAT;
    if (bzla_hashptr_table_get(bzla->assumptions, bzla_node_invert(root)))
      goto UNSAT;
    id = bzla_node_get_id(root);
    if (!bzla_hashint_map_contains(slv->weights, id))
    {
      BZLA_CNEW(bzla->mm, d);
      d->weight = 1; /* initial assertion weight */
      bzla_hashint_map_add(slv->weights, id)->as_ptr = d;
    }
  }

  if (!slv->score) slv->score = bzla_hashint_map_new(bzla->mm);

  for (;;)
  {
    if (bzla_terminate(bzla))
    {
      sat_result = BZLA_RESULT_UNKNOWN;
      goto DONE;
    }

    /* init */
    slv->prop_flip_cond_const_prob =
        bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND_CONST);
    slv->prop_flip_cond_const_prob_delta =
        slv->prop_flip_cond_const_prob > (BZLA_PROB_50)
            ? -BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA
            : BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA;

    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert(!slv->roots);
    slv->roots = bzla_hashint_map_new(bzla->mm);
    bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&pit, bzla->synthesized_constraints);
    bzla_iter_hashptr_queue(&pit, bzla->assumptions);
    while (bzla_iter_hashptr_has_next(&pit))
    {
      root = bzla_iter_hashptr_next(&pit);
      if (!bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root))
          && bzla_bv_is_zero(bzla_model_get_bv(bzla, root)))
      {
        if (bzla_node_is_bv_const(root))
          goto UNSAT; /* contains false constraint -> unsat */
        bzla_hashint_map_add(slv->roots, bzla_node_get_id(root));
      }
    }

    /* compute initial sls score */
    bzla_slsutils_compute_sls_scores(
        bzla, bzla->bv_model, bzla->fun_model, slv->score);

    if (!slv->roots->count) goto SAT;

    for (j = 0, max_steps = BZLA_SLS_MAXSTEPS(slv->stats.restarts + 1);
         !bzla_opt_get(bzla, BZLA_OPT_SLS_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (bzla_terminate(bzla)
          || (slv->nflips && slv->stats.flips >= slv->nflips)
          || (nprops && slv->stats.props >= nprops))
      {
        sat_result = BZLA_RESULT_UNKNOWN;
        goto DONE;
      }

      if (!move(bzla, nmoves)) goto UNSAT;
      nmoves += 1;

      if (!slv->roots->count) goto SAT;
    }

    /* restart */
    slv->api.generate_model((BzlaSolver *) slv, false, true);
    bzla_hashint_map_delete(slv->score);
    bzla_hashint_map_delete(slv->roots);
    slv->roots = 0;
    slv->score = bzla_hashint_map_new(bzla->mm);
    slv->stats.restarts += 1;
  }

SAT:
  sat_result = BZLA_RESULT_SAT;
  goto DONE;

UNSAT:
  sat_result = BZLA_RESULT_UNSAT;

DONE:
  if (slv->roots)
  {
    bzla_hashint_map_delete(slv->roots);
    slv->roots = 0;
  }
  if (slv->weights)
  {
    bzla_iter_hashint_init(&iit, slv->weights);
    while (bzla_iter_hashint_has_next(&iit))
      BZLA_DELETE(
          bzla->mm,
          (BzlaSLSConstrData *) bzla_iter_hashint_next_data(&iit)->as_ptr);
    bzla_hashint_map_delete(slv->weights);
    slv->weights = 0;
  }
  if (slv->score)
  {
    bzla_hashint_map_delete(slv->score);
    slv->score = 0;
  }
  return sat_result;
}

static void
generate_model_sls_solver(BzlaSLSSolver *slv,
                          bool model_for_all_nodes,
                          bool reset)
{
  assert(slv);
  assert(slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla;

  bzla = slv->bzla;

  if (!reset && bzla->bv_model) return;
  bzla_lsutils_initialize_bv_model((BzlaSolver *) slv);
  bzla_model_init_fun(bzla, &bzla->fun_model);
  bzla_model_generate(
      bzla, bzla->bv_model, bzla->fun_model, model_for_all_nodes);
}

static void
print_stats_sls_solver(BzlaSLSSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla;

  bzla = slv->bzla;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "sls restarts: %d", slv->stats.restarts);
  BZLA_MSG(bzla->msg, 1, "sls moves: %d", slv->stats.moves);
  BZLA_MSG(bzla->msg, 1, "sls flips: %d", slv->stats.flips);
  BZLA_MSG(bzla->msg, 1, "sls propagation steps: %u", slv->stats.props);
  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg,
           1,
           "sls propagation move conflicts (recoverable): %d",
           slv->stats.move_prop_rec_conf);
  BZLA_MSG(bzla->msg,
           1,
           "sls propagation move conflicts (non-recoverable): %d",
           slv->stats.move_prop_non_rec_conf);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "sls flip        moves: %d", slv->stats.move_flip);
  BZLA_MSG(bzla->msg, 1, "sls inc         moves: %d", slv->stats.move_inc);
  BZLA_MSG(bzla->msg, 1, "sls dec         moves: %d", slv->stats.move_dec);
  BZLA_MSG(bzla->msg, 1, "sls not         moves: %d", slv->stats.move_not);
  BZLA_MSG(bzla->msg, 1, "sls range       moves: %d", slv->stats.move_range);
  BZLA_MSG(bzla->msg, 1, "sls segment     moves: %d", slv->stats.move_seg);
  BZLA_MSG(bzla->msg, 1, "sls random      moves: %d", slv->stats.move_rand);
  BZLA_MSG(
      bzla->msg, 1, "sls random walk moves: %d", slv->stats.move_rand_walk);
  BZLA_MSG(bzla->msg, 1, "sls propagation moves: %d", slv->stats.move_prop);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(
      bzla->msg, 1, "sls gw flip        moves: %d", slv->stats.move_gw_flip);
  BZLA_MSG(
      bzla->msg, 1, "sls gw inc         moves: %d", slv->stats.move_gw_inc);
  BZLA_MSG(
      bzla->msg, 1, "sls gw dec         moves: %d", slv->stats.move_gw_dec);
  BZLA_MSG(
      bzla->msg, 1, "sls gw not         moves: %d", slv->stats.move_gw_not);
  BZLA_MSG(
      bzla->msg, 1, "sls gw range       moves: %d", slv->stats.move_gw_range);
  BZLA_MSG(
      bzla->msg, 1, "sls gw segment     moves: %d", slv->stats.move_gw_seg);
  BZLA_MSG(
      bzla->msg, 1, "sls gw random      moves: %d", slv->stats.move_gw_rand);
  BZLA_MSG(bzla->msg,
           1,
           "sls gw random walk moves: %d",
           slv->stats.move_gw_rand_walk);
}

static void
print_time_stats_sls_solver(BzlaSLSSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla = slv->bzla;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (total)",
           slv->time.update_cone);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (reset)",
           slv->time.update_cone_reset);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (model gen)",
           slv->time.update_cone_model_gen);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (compute score)",
           slv->time.update_cone_compute_score);
  BZLA_MSG(bzla->msg, 1, "");
}

static void
print_model_sls_solver(BzlaSLSSolver *slv, const char *format, FILE *file)
{
  bzla_print_model_aufbvfp(slv->bzla, format, file);
}

BzlaSolver *
bzla_new_sls_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaSLSSolver *slv;

  BZLA_CNEW(bzla->mm, slv);

  slv->bzla    = bzla;
  slv->kind    = BZLA_SLS_SOLVER_KIND;
  slv->domains = bzla_hashint_map_new(bzla->mm);

  BZLA_INIT_STACK(bzla->mm, slv->moves);

  slv->api.clone          = (BzlaSolverClone) clone_sls_solver;
  slv->api.delet          = (BzlaSolverDelete) delete_sls_solver;
  slv->api.sat            = (BzlaSolverSat) sat_sls_solver;
  slv->api.generate_model = (BzlaSolverGenerateModel) generate_model_sls_solver;
  slv->api.print_stats    = (BzlaSolverPrintStats) print_stats_sls_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_sls_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_sls_solver;

  BZLA_MSG(bzla->msg, 1, "enabled sls engine");

  return (BzlaSolver *) slv;
}

/*------------------------------------------------------------------------*/
