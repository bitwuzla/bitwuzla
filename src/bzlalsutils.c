/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlalsutils.h"

#include "bzlabv.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlaslsutils.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static void
update_roots_table(Bzla *bzla,
                   BzlaIntHashTable *roots,
                   BzlaNode *exp,
                   BzlaBitVector *bv)
{
  assert(bzla);
  assert(roots);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bv);
  assert(bzla_bv_compare(bzla_model_get_bv(bzla, exp), bv));

  (void) bzla;

  /* exp: old assignment = 0, new assignment = 1 (bv = 1)
   *      -> satisfied, remove */
  if (bzla_hashint_map_get(roots, exp->id))
  {
    bzla_hashint_map_remove(roots, exp->id, 0);
    assert(bzla_bv_is_false(bzla_model_get_bv(bzla, exp)));
    assert(bzla_bv_is_true(bv));
  }
  /* -exp: old assignment = 0, new assignment = 1 (bv = 0)
   * -> satisfied, remove */
  else if (bzla_hashint_map_get(roots, -exp->id))
  {
    bzla_hashint_map_remove(roots, -exp->id, 0);
    assert(bzla_bv_is_false(bzla_model_get_bv(bzla, bzla_node_invert(exp))));
    assert(bzla_bv_is_false(bv));
  }
  /* exp: old assignment = 1, new assignment = 0 (bv = 0)
   * -> unsatisfied, add */
  else if (bzla_bv_is_false(bv))
  {
    bzla_hashint_map_add(roots, exp->id);
    assert(bzla_bv_is_true(bzla_model_get_bv(bzla, exp)));
  }
  /* -exp: old assignment = 1, new assignment = 0 (bv = 1)
   * -> unsatisfied, add */
  else
  {
    assert(bzla_bv_is_true(bv));
    bzla_hashint_map_add(roots, -exp->id);
    assert(bzla_bv_is_true(bzla_model_get_bv(bzla, bzla_node_invert(exp))));
  }
}

/**
 * Update cone of influence.
 *
 * Note: 'roots' will only be updated if 'update_roots' is true.
 *         + PROP engine: always
 *         + SLS  engine: only if an actual move is performed
 *                        (not during neighborhood exploration, 'try_move')
 *       -> assertion code guarded with '#ifndef NDEBUG' is therefore
 *          always valid since 'roots' always maintains a valid state
 *          ('try_move' of the SLS engine is the only case where 'roots'
 *           might become globally invalid, i.e., when a tried move
 *           is not actually performed, however in that particular case
 *           we do not update 'roots')
 */
void
bzla_lsutils_update_cone(Bzla *bzla,
                         BzlaIntHashTable *bv_model,
                         BzlaIntHashTable *roots,
                         BzlaIntHashTable *score,
                         BzlaIntHashTable *exps,
                         bool update_roots,
                         uint64_t *stats_updates,
                         double *time_update_cone,
                         double *time_update_cone_reset,
                         double *time_update_cone_model_gen,
                         double *time_update_cone_compute_score)
{
  assert(bzla);
  assert(bzla->slv->kind == BZLA_PROP_SOLVER_KIND
         || bzla->slv->kind == BZLA_SLS_SOLVER_KIND);
  assert(bv_model);
  assert(roots);
  assert(exps);
  assert(exps->count);
  assert(bzla->slv->kind != BZLA_PROP_SOLVER_KIND || update_roots);
  assert(time_update_cone);
  assert(time_update_cone_reset);
  assert(time_update_cone_model_gen);

  double start, delta;
  uint32_t i, j;
  int32_t id;
  BzlaNode *exp, *cur;
  BzlaNodeIterator nit;
  BzlaIntHashTableIterator iit;
  BzlaHashTableData *d;
  BzlaNodePtrStack stack, cone;
  BzlaIntHashTable *cache;
  BzlaBitVector *bv, *e[BZLA_NODE_MAX_CHILDREN], *ass;
  BzlaMemMgr *mm;

  start = delta = bzla_util_time_stamp();

  mm = bzla->mm;

#ifndef NDEBUG
  BzlaPtrHashTableIterator pit;
  BzlaNode *root;
  bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    root = bzla_iter_hashptr_next(&pit);
    assert(!bzla_hashptr_table_get(bzla->unsynthesized_constraints,
                                   bzla_node_invert(root)));
    assert(!bzla_hashptr_table_get(bzla->assumptions, bzla_node_invert(root)));
    if (bzla_bv_is_false(bzla_model_get_bv(bzla, root)))
      assert(bzla_hashint_map_contains(roots, bzla_node_get_id(root)));
    else
      assert(!bzla_hashint_map_contains(roots, bzla_node_get_id(root)));
  }
#endif

  /* reset cone ----------------------------------------------------------- */

  BZLA_INIT_STACK(mm, cone);
  BZLA_INIT_STACK(mm, stack);
  bzla_iter_hashint_init(&iit, exps);
  while (bzla_iter_hashint_has_next(&iit))
  {
    exp = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&iit));
    assert(bzla_node_is_regular(exp));
    assert(bzla_lsutils_is_leaf_node(exp));
    BZLA_PUSH_STACK(stack, exp);
  }
  cache = bzla_hashint_table_new(mm);
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur = BZLA_POP_STACK(stack);
    assert(bzla_node_is_regular(cur));

    if (bzla_node_is_fun(cur) || bzla_node_is_args(cur) || cur->parameterized)
      continue;

    if (bzla_hashint_table_contains(cache, cur->id)) continue;
    bzla_hashint_table_add(cache, cur->id);
    if (!bzla_hashint_table_contains(exps, cur->id)) BZLA_PUSH_STACK(cone, cur);
    *stats_updates += 1;

    /* push parents */
    bzla_iter_parent_init(&nit, cur);
    while (bzla_iter_parent_has_next(&nit))
      BZLA_PUSH_STACK(stack, bzla_iter_parent_next(&nit));
  }
  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(cache);

  *time_update_cone_reset += bzla_util_time_stamp() - delta;

  /* update assignment and score of exps ----------------------------------- */

  bzla_iter_hashint_init(&iit, exps);
  while (bzla_iter_hashint_has_next(&iit))
  {
    ass = (BzlaBitVector *) exps->data[iit.cur_pos].as_ptr;
    exp = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&iit));

    /* update model */
    d = bzla_hashint_map_get(bv_model, exp->id);
    assert(d);
    if (update_roots
        && (exp->constraint || bzla_hashptr_table_get(bzla->assumptions, exp)
            || bzla_hashptr_table_get(bzla->assumptions, bzla_node_invert(exp)))
        && bzla_bv_compare(d->as_ptr, ass))
    {
      /* old assignment != new assignment */
      update_roots_table(bzla, roots, exp, ass);
    }
    bzla_bv_free(mm, d->as_ptr);
    d->as_ptr = bzla_bv_copy(mm, ass);
    if ((d = bzla_hashint_map_get(bv_model, -exp->id)))
    {
      bzla_bv_free(mm, d->as_ptr);
      d->as_ptr = bzla_bv_not(mm, ass);
    }

    /* update score */
    if (score && bzla_node_bv_get_width(bzla, exp) == 1)
    {
      assert(bzla_hashint_map_contains(score, bzla_node_get_id(exp)));
      bzla_hashint_map_get(score, bzla_node_get_id(exp))->as_dbl =
          bzla_slsutils_compute_score_node(
              bzla, bv_model, bzla->fun_model, score, exp);

      assert(bzla_hashint_map_contains(score, -bzla_node_get_id(exp)));
      bzla_hashint_map_get(score, -bzla_node_get_id(exp))->as_dbl =
          bzla_slsutils_compute_score_node(
              bzla, bv_model, bzla->fun_model, score, bzla_node_invert(exp));
    }
  }

  qsort(cone.start,
        BZLA_COUNT_STACK(cone),
        sizeof(BzlaNode *),
        bzla_node_compare_by_id_qsort_asc);

  /* update model of cone ------------------------------------------------- */

  delta = bzla_util_time_stamp();

  for (i = 0; i < BZLA_COUNT_STACK(cone); i++)
  {
    cur = BZLA_PEEK_STACK(cone, i);

    assert(bzla_node_is_regular(cur));
    for (j = 0; j < cur->arity; j++)
    {
      if (bzla_node_is_bv_const(cur->e[j]))
      {
        e[j] = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(cur->e[j]));
      }
      else
      {
        d = bzla_hashint_map_get(bv_model, bzla_node_real_addr(cur->e[j])->id);
        /* Note: generate model enabled branch for ite (and does not
         * generate model for nodes in the branch, hence !b may happen */
        if (!d)
          e[j] = bzla_model_recursively_compute_assignment(
              bzla, bv_model, bzla->fun_model, cur->e[j]);
        else
          e[j] = bzla_node_is_inverted(cur->e[j]) ? bzla_bv_not(mm, d->as_ptr)
                                                  : bzla_bv_copy(mm, d->as_ptr);
      }
    }
    switch (cur->kind)
    {
      case BZLA_BV_ADD_NODE: bv = bzla_bv_add(mm, e[0], e[1]); break;
      case BZLA_BV_AND_NODE: bv = bzla_bv_and(mm, e[0], e[1]); break;
      case BZLA_BV_EQ_NODE: bv = bzla_bv_eq(mm, e[0], e[1]); break;
      case BZLA_BV_ULT_NODE: bv = bzla_bv_ult(mm, e[0], e[1]); break;
      case BZLA_BV_SLL_NODE: bv = bzla_bv_sll(mm, e[0], e[1]); break;
      case BZLA_BV_SLT_NODE: bv = bzla_bv_slt(mm, e[0], e[1]); break;
      case BZLA_BV_SRL_NODE: bv = bzla_bv_srl(mm, e[0], e[1]); break;
      case BZLA_BV_MUL_NODE: bv = bzla_bv_mul(mm, e[0], e[1]); break;
      case BZLA_BV_UDIV_NODE: bv = bzla_bv_udiv(mm, e[0], e[1]); break;
      case BZLA_BV_UREM_NODE: bv = bzla_bv_urem(mm, e[0], e[1]); break;
      case BZLA_BV_CONCAT_NODE: bv = bzla_bv_concat(mm, e[0], e[1]); break;
      case BZLA_BV_SLICE_NODE:
        bv = bzla_bv_slice(mm,
                           e[0],
                           bzla_node_bv_slice_get_upper(cur),
                           bzla_node_bv_slice_get_lower(cur));
        break;
      default:
        assert(bzla_node_is_cond(cur));
        bv = bzla_bv_is_true(e[0]) ? bzla_bv_copy(mm, e[1])
                                   : bzla_bv_copy(mm, e[2]);
    }

    /* update assignment */

    d = bzla_hashint_map_get(bv_model, cur->id);

    /* update roots table */
    if (update_roots
        && (cur->constraint || bzla_hashptr_table_get(bzla->assumptions, cur)
            || bzla_hashptr_table_get(bzla->assumptions,
                                      bzla_node_invert(cur))))
    {
      assert(d); /* must be contained, is root */
      /* old assignment != new assignment */
      if (bzla_bv_compare(d->as_ptr, bv))
        update_roots_table(bzla, roots, cur, bv);
    }

    /* update assignments */
    /* Note: generate model enabled branch for ite (and does not generate
     *       model for nodes in the branch, hence !b may happen */
    if (!d)
    {
      bzla_node_copy(bzla, cur);
      bzla_hashint_map_add(bv_model, cur->id)->as_ptr = bv;
    }
    else
    {
      bzla_bv_free(mm, d->as_ptr);
      d->as_ptr = bv;
    }

    if ((d = bzla_hashint_map_get(bv_model, -cur->id)))
    {
      bzla_bv_free(mm, d->as_ptr);
      d->as_ptr = bzla_bv_not(mm, bv);
    }
    /* cleanup */
    for (j = 0; j < cur->arity; j++) bzla_bv_free(mm, e[j]);
  }
  *time_update_cone_model_gen += bzla_util_time_stamp() - delta;

  /* update score of cone ------------------------------------------------- */

  if (score)
  {
    delta = bzla_util_time_stamp();
    for (i = 0; i < BZLA_COUNT_STACK(cone); i++)
    {
      cur = BZLA_PEEK_STACK(cone, i);
      assert(bzla_node_is_regular(cur));

      if (bzla_node_bv_get_width(bzla, cur) != 1) continue;

      id = bzla_node_get_id(cur);
      if (!bzla_hashint_map_contains(score, id))
      {
        /* not reachable from the roots */
        assert(!bzla_hashint_map_contains(score, -id));
        continue;
      }
      bzla_hashint_map_get(score, id)->as_dbl =
          bzla_slsutils_compute_score_node(
              bzla, bv_model, bzla->fun_model, score, cur);
      assert(bzla_hashint_map_contains(score, -id));
      bzla_hashint_map_get(score, -id)->as_dbl =
          bzla_slsutils_compute_score_node(
              bzla, bv_model, bzla->fun_model, score, bzla_node_invert(cur));
    }
    *time_update_cone_compute_score += bzla_util_time_stamp() - delta;
  }

  BZLA_RELEASE_STACK(cone);

#ifndef NDEBUG
  bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    root = bzla_iter_hashptr_next(&pit);
    if (bzla_bv_is_false(bzla_model_get_bv(bzla, root)))
      assert(bzla_hashint_map_contains(roots, bzla_node_get_id(root)));
    else
      assert(!bzla_hashint_map_contains(roots, bzla_node_get_id(root)));
  }
#endif
  *time_update_cone += bzla_util_time_stamp() - start;
}

bool
bzla_lsutils_is_leaf_node(BzlaNode *n)
{
  assert(n);
  return bzla_node_is_bv_var(n) || bzla_node_is_apply(n)
         || bzla_node_is_fun_eq(n) || bzla_node_is_quantifier(n);
}

/**
 * Initialize model values for inputs (var, apply, feq) based on previous
 * model or zero-initialize if no previous model exists.
 */
void
bzla_lsutils_initialize_bv_model(BzlaSolver *slv)
{
  size_t i;
  Bzla *bzla;
  BzlaMemMgr *mm;
  BzlaNode *cur;
  BzlaIntHashTable *bv_model = 0, *cur_bv_model;
  BzlaBitVector *cur_value;

  bzla         = slv->bzla;
  mm           = bzla->mm;
  cur_bv_model = slv->bzla->bv_model;

  bzla_model_init_bv(bzla, &bv_model);

  for (i = 1; i < BZLA_COUNT_STACK(bzla->nodes_id_table); ++i)
  {
    cur = BZLA_PEEK_STACK(bzla->nodes_id_table, i);
    if (!cur) continue;
    if (bzla_lsutils_is_leaf_node(cur))
    {
      if (cur_bv_model && bzla_hashint_map_contains(cur_bv_model, cur->id))
      {
        cur_value = bzla_bv_copy(
            mm, bzla_hashint_map_get(cur_bv_model, cur->id)->as_ptr);
      }
      else
      {
        cur_value = bzla_bv_zero(mm, bzla_node_bv_get_width(bzla, cur));
      }
#ifndef NBZLALOG
      char *bits = bzla_bv_to_char(mm, cur_value);
      BZLALOG(
          2, "initialize model for %s to %s", bzla_util_node2string(cur), bits);
      bzla_mem_freestr(mm, bits);
#endif
      bzla_model_add_to_bv(bzla, bv_model, cur, cur_value);
      bzla_bv_free(mm, cur_value);
    }
  }
  bzla_model_delete_bv(bzla, &bzla->bv_model);
  bzla->bv_model = bv_model;
}
