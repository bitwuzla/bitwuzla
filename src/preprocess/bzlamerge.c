/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlamerge.h"

#include "bzlabeta.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlasubst.h"
#include "preprocess/bzlapputils.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

//#ifndef NDEBUG
// static bool
// bzla_check_static_rho_equal_dbg (BzlaPtrHashTable * t0, BzlaPtrHashTable *
// t1)
//{
//  assert (t0);
//  assert (t1);
//  assert (t0->count == t1->count);
//
//  BzlaPtrHashTableIterator it;
//  BzlaPtrHashBucket *b;
//  BzlaNode *value, *args;
//
//  bzla_iter_hashptr_init (&it, t0);
//  while (bzla_iter_hashptr_has_next (&it))
//    {
//      value = it.bucket->data.as_ptr;
//      args = bzla_iter_hashptr_next (&it);
//      assert (args->arity == 1);
//      b = bzla_hashptr_table_get (t1, args);
//      assert (b);
//      assert (b->data.as_ptr == value);
//    }
//  return true;
//}
//#endif

static void
delete_static_rho(Bzla *bzla, BzlaPtrHashTable *static_rho)
{
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, static_rho);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(bzla, it.bucket->data.as_ptr);
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(static_rho);
}

static void
add_to_static_rho(Bzla *bzla, BzlaPtrHashTable *to, BzlaPtrHashTable *from)
{
  BzlaNode *data, *key;
  BzlaPtrHashTableIterator it;

  if (!from) return;

  bzla_iter_hashptr_init(&it, from);
  while (bzla_iter_hashptr_has_next(&it))
  {
    data = it.bucket->data.as_ptr;
    key  = bzla_iter_hashptr_next(&it);
    if (bzla_hashptr_table_get(to, key)) continue;
    bzla_hashptr_table_add(to, bzla_node_copy(bzla, key))->data.as_ptr =
        bzla_node_copy(bzla, data);
  }
}

void
bzla_merge_lambdas(Bzla *bzla)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  uint32_t i, num_merged_lambdas = 0;
  double start, delta;
  BzlaNode *cur, *lambda, *subst, *parent, *param, *body;
  BzlaMemMgr *mm;
  BzlaPtrHashTableIterator it;
  BzlaNodeIterator nit;
  BzlaNodePtrStack stack, visit, params, lambdas;
  BzlaPtrHashTable *merge_lambdas, *static_rho;
  BzlaIntHashTable *mark, *mark_lambda;

  if (bzla->lambdas->count == 0) return;

  start = bzla_util_time_stamp();
  mm    = bzla->mm;

  mark        = bzla_hashint_table_new(mm);
  mark_lambda = bzla_hashint_table_new(mm);
  bzla_init_substitutions(bzla);
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, params);
  BZLA_INIT_STACK(mm, lambdas);

  bzla_pputils_collect_lambdas(bzla, &lambdas);

  /* collect candidates for merging */
  while (!BZLA_EMPTY_STACK(lambdas))
  {
    lambda = BZLA_POP_STACK(lambdas);
    assert(!bzla_node_is_simplified(lambda)
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
    lambda = bzla_node_get_simplified(bzla, lambda);
    assert(bzla_node_is_regular(lambda));
    assert(bzla_node_is_lambda(lambda));

    if (!bzla_node_is_lambda(lambda))
    {
      assert(bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
      continue;
    }

    /* found top lambda */
    parent = bzla_node_real_addr(lambda->first_parent);
    if (lambda->parents > 1
        || lambda->parents == 0
        /* case lambda->parents == 1 */
        || (!parent->parameterized
            && (bzla_node_is_apply(parent) || bzla_node_is_fun_eq(parent))))
    {
      BZLA_PUSH_STACK(stack, lambda);
      continue;
    }
  }

  while (!BZLA_EMPTY_STACK(stack))
  {
    lambda = BZLA_POP_STACK(stack);
    assert(bzla_node_is_regular(lambda));
    assert(!bzla_node_is_simplified(lambda)
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
    lambda = bzla_node_get_simplified(bzla, lambda);

    if (bzla_hashint_table_contains(mark_lambda, lambda->id)) continue;

    bzla_hashint_table_add(mark_lambda, lambda->id);
    /* search downwards and look for lambdas that can be merged */
    BZLA_RESET_STACK(visit);
    BZLA_PUSH_STACK(visit, bzla_node_binder_get_body(lambda));
    merge_lambdas =
        bzla_hashptr_table_new(mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    bzla_hashptr_table_add(merge_lambdas, lambda);
    while (!BZLA_EMPTY_STACK(visit))
    {
      cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

      if (bzla_hashint_table_contains(mark, cur->id)
          || (!bzla_node_is_lambda(cur) && !cur->parameterized)
          || !cur->lambda_below)
        continue;

      if (bzla_node_is_lambda(cur))
      {
        /* lambdas with more than one parents cannot be merged */
        if (cur->parents > 1)
        {
          /* try to merge lambdas starting from 'cur' */
          BZLA_PUSH_STACK(stack, cur);
          continue;
        }

        /* we can only merge lambdas that have all a static_rho or
         * none of them has one */
        if (!bzla_node_lambda_get_static_rho(cur)
                != !bzla_node_lambda_get_static_rho(lambda)
            /* we can only merge lambdas that either represent arrays
             * or not */
            || cur->is_array != lambda->is_array)
        {
          /* try to merge lambdas starting from 'cur' */
          BZLA_PUSH_STACK(stack, cur);
          continue;
        }

        if (!bzla_hashptr_table_get(merge_lambdas, cur))
          bzla_hashptr_table_add(merge_lambdas, cur);
        BZLA_PUSH_STACK(visit, bzla_node_binder_get_body(cur));
      }
      else
      {
        for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
      }
      bzla_hashint_table_add(mark, cur->id);
    }

    /* no lambdas to merge found */
    if (merge_lambdas->count <= 1)
    {
      bzla_hashptr_table_delete(merge_lambdas);
      continue;
    }

    /* assign parameters of top-most lambda with fresh parameters */
    bzla_iter_lambda_init(&nit, lambda);
    while (bzla_iter_lambda_has_next(&nit))
    {
      cur   = bzla_iter_lambda_next(&nit);
      param = bzla_exp_param(bzla, bzla_node_get_sort_id(cur->e[0]), 0);
      BZLA_PUSH_STACK(params, param);
      bzla_beta_assign_param(bzla, cur, param);
    }
    /* merge lambdas that are in 'merge_lambdas' table */
    body = bzla_beta_reduce_merge(
        bzla, bzla_node_binder_get_body(lambda), merge_lambdas);
    bzla_beta_unassign_params(bzla, lambda);
    subst = bzla_exp_fun(bzla, params.start, BZLA_COUNT_STACK(params), body);
    if (lambda->is_array) subst->is_array = 1;
    bzla_node_release(bzla, body);

    /* generate static_rho from merged lambdas' static_rhos */
    assert(merge_lambdas->count > 0);
    num_merged_lambdas += merge_lambdas->count;
    static_rho = bzla_hashptr_table_new(mm,
                                        (BzlaHashPtr) bzla_node_hash_by_id,
                                        (BzlaCmpPtr) bzla_node_compare_by_id);
    if (bzla_node_lambda_get_static_rho(lambda))
    {
      bzla_iter_hashptr_init(&it, merge_lambdas);
      while (bzla_iter_hashptr_has_next(&it))
      {
        cur = bzla_iter_hashptr_next(&it);
        add_to_static_rho(
            bzla, static_rho, bzla_node_lambda_get_static_rho(cur));
        assert(!bzla_node_lambda_get_static_rho(lambda)
               == !bzla_node_lambda_get_static_rho(cur));
      }
    }
    BZLALOG(2,
            "merged %u lambdas (%u static_rho entries)",
            merge_lambdas->count,
            static_rho->count);
    bzla_hashptr_table_delete(merge_lambdas);

    if (static_rho->count > 0)
    {
      /* 'subst' is already an existing lambda with a 'static_rho', if
       * this is the case we have to check that subst->static_rho constains
       * the same elements as static_rho */
      if (bzla_node_lambda_get_static_rho(subst))
      {
        //	      assert (bzla_check_static_rho_equal_dbg (
        //			   bzla_node_lambda_get_static_rho (subst),
        // static_rho));
        /* 'static_rho' contains elements so we have to release them
         * properly */
        delete_static_rho(bzla, static_rho);
      }
      else
        bzla_node_lambda_set_static_rho(subst, static_rho);
    }
    else
      bzla_hashptr_table_delete(static_rho);

    bzla_insert_substitution(bzla, lambda, subst, false);
    bzla_node_release(bzla, subst);
    while (!BZLA_EMPTY_STACK(params))
      bzla_node_release(bzla, BZLA_POP_STACK(params));
  }

  bzla_substitute_and_rebuild(bzla, bzla->substitutions);
  bzla_delete_substitutions(bzla);
  bzla->stats.lambdas_merged += num_merged_lambdas;

  bzla_hashint_table_delete(mark);
  bzla_hashint_table_delete(mark_lambda);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(params);
  BZLA_RELEASE_STACK(lambdas);
  delta = bzla_util_time_stamp() - start;
  BZLA_MSG(bzla->msg,
           1,
           "merged %d lambdas in %.2f seconds",
           num_merged_lambdas,
           delta);
  bzla->time.merge += delta;
}
