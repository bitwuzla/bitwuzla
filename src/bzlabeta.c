/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2020 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2013 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlabeta.h"

#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlarewrite.h"
#include "bzlaslvfun.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

#define BETA_RED_LAMBDA_MERGE -2
#define BETA_RED_FULL 0
#define BETA_RED_BOUNDED 1

static void
cache_beta_result(Bzla *bzla,
                  BzlaPtrHashTable *cache,
                  BzlaNode *lambda,
                  BzlaNode *exp,
                  BzlaNode *result)
{
  assert(bzla);
  assert(cache);
  assert(lambda);
  assert(exp);
  assert(result);
  assert(!bzla_node_is_proxy(lambda));
  assert(!bzla_node_is_proxy(exp));
  assert(!bzla_node_is_proxy(result));
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));

  BzlaNodePair *pair;
  BzlaPtrHashBucket *bucket;

  pair   = bzla_node_pair_new(bzla, lambda, exp);
  bucket = bzla_hashptr_table_get(cache, pair);
  if (bucket)
  {
    bzla_node_pair_delete(bzla, pair);
    assert((BzlaNode *) bucket->data.as_ptr == result);
  }
  else
    bzla_hashptr_table_add(cache, pair)->data.as_ptr =
        bzla_node_copy(bzla, result);
  BZLALOG(3,
          "%s: (%s, %s) -> %s",
          __FUNCTION__,
          bzla_util_node2string(lambda),
          bzla_util_node2string(exp),
          bzla_util_node2string(result));
}

static BzlaNode *
cached_beta_result(Bzla *bzla,
                   BzlaPtrHashTable *cache,
                   BzlaNode *lambda,
                   BzlaNode *exp)
{
  assert(bzla);
  assert(lambda);
  assert(exp);
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));

  BzlaNodePair *pair;
  BzlaPtrHashBucket *bucket;

  pair   = bzla_node_pair_new(bzla, lambda, exp);
  bucket = bzla_hashptr_table_get(cache, pair);
  bzla_node_pair_delete(bzla, pair);

  if (bucket)
  {
    BZLALOG(3,
            "%s: (%s, %s) -> %s",
            __FUNCTION__,
            bzla_util_node2string(lambda),
            bzla_util_node2string(exp),
            bzla_util_node2string(bucket->data.as_ptr));
    return (BzlaNode *) bucket->data.as_ptr;
  }

  return 0;
}

void
bzla_beta_assign_args(Bzla *bzla, BzlaNode *fun, BzlaNode *args)
{
  assert(bzla);
  assert(fun);
  assert(args);
  assert(bzla_node_is_regular(fun));
  assert(bzla_node_is_regular(args));
  assert(bzla_node_is_lambda(fun));
  assert(bzla_node_is_args(args));

  //  BZLALOG ("%s: %s (%d params, %d args)", __FUNCTION__,
  //  bzla_util_node2string (fun),
  //	   ((BzlaLambdaNode *) fun)->num_params,
  //	   ((BzlaArgsNode *) args)->num_args);

  BzlaNode *cur_lambda, *cur_arg;
  BzlaNodeIterator it;
  BzlaArgsIterator ait;

  bzla_iter_args_init(&ait, args);
  bzla_iter_lambda_init(&it, fun);

  while (bzla_iter_args_has_next(&ait))
  {
    assert(bzla_iter_lambda_has_next(&it));
    cur_arg    = bzla_iter_args_next(&ait);
    cur_lambda = bzla_iter_lambda_next(&it);
    bzla_beta_assign_param(bzla, cur_lambda, cur_arg);
  }
}

void
bzla_beta_assign_param(Bzla *bzla, BzlaNode *lambda, BzlaNode *arg)
{
  (void) bzla;
  assert(bzla);
  assert(lambda);
  assert(arg);
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));
  assert(!bzla_node_param_get_assigned_exp(lambda->e[0]));
  bzla_node_param_set_assigned_exp(lambda->e[0], arg);
}

void
bzla_beta_unassign_params(Bzla *bzla, BzlaNode *lambda)
{
  (void) bzla;
  assert(lambda);
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));
  assert(bzla_node_is_param(lambda->e[0]));

  do
  {
    if (!bzla_node_param_get_assigned_exp(lambda->e[0])) break;

    bzla_node_param_set_assigned_exp(lambda->e[0], 0);
    lambda = bzla_node_real_addr(lambda->e[1]);
  } while (bzla_node_is_lambda(lambda));
}

/* We distinguish the following options for (un)bounded reduction:
 *
 *   BETA_RED_LAMBDA_MERGE: merge lambda chains
 *
 *   BETA_RED_FULL:   full reduction,
 *		      do not evaluate conditionals
 *
 *   BETA_RED_BOUNDED (bound): bounded reduction, stop reduction at 'bound'
 *			       lambdas
 */
static BzlaNode *
beta_reduce(Bzla *bzla,
            BzlaNode *exp,
            int32_t mode,
            int32_t bound,
            BzlaPtrHashTable *merge_lambdas,
            BzlaPtrHashTable *cache)
{
  assert(bzla);
  assert(exp);
  assert(mode == BETA_RED_LAMBDA_MERGE || mode == BETA_RED_FULL
         || mode == BETA_RED_BOUNDED);
  assert(bound >= 0);
  assert(bound == 0 || mode == BETA_RED_BOUNDED);
  assert(mode != BETA_RED_LAMBDA_MERGE || merge_lambdas);

  uint32_t i;
  int32_t cur_lambda_depth = 0;
  double start;
  BzlaMemMgr *mm;
  BzlaNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args;
  BzlaNode *cached;
  BzlaNodePtrStack stack, arg_stack, cleanup_stack, reset;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d, md;
#ifndef NDEBUG
  BzlaNodePtrStack unassign_stack;
  BZLA_INIT_STACK(bzla->mm, unassign_stack);
#endif

  start = bzla_util_time_stamp();
  bzla->stats.beta_reduce_calls++;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, arg_stack);
  BZLA_INIT_STACK(mm, cleanup_stack);
  BZLA_INIT_STACK(mm, reset);
  mark = bzla_hashint_map_new(mm);

  BZLA_PUSH_STACK(stack, exp);
  BZLA_PUSH_STACK(stack, 0);

  while (!BZLA_EMPTY_STACK(stack))
  {
    cur_parent = BZLA_POP_STACK(stack);
    cur        = BZLA_POP_STACK(stack);
    assert(!bzla_node_is_proxy(cur));

    /* we do not want the simplification of top level apply constraints */
    if (bzla_node_real_addr(cur)->constraint && bzla_node_is_apply(cur))
      cur = bzla_node_get_simplified(bzla, cur);
    else
      cur = bzla_simplify_exp(bzla, cur);
    real_cur = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(mark, real_cur->id);

    BZLALOG(1, "  visit: %s", bzla_util_node2string(cur));

    if (!d)
    {
      assert(!bzla_node_is_lambda(real_cur)
             || !bzla_node_is_simplified(real_cur->e[0])
             || bzla_opt_get(bzla, BZLA_OPT_NONDESTR_SUBST));

      if (bzla_node_is_lambda(real_cur)
          && !real_cur->parameterized
          /* only count head lambdas (in case of curried lambdas) */
          && (!cur_parent || !bzla_node_is_lambda(cur_parent)))
        cur_lambda_depth++;

      /* stop at given bound */
      if (bound > 0 && bzla_node_is_lambda(real_cur)
          && cur_lambda_depth == bound)
      {
        assert(!real_cur->parameterized);
        assert(!cur_parent || !bzla_node_is_lambda(cur_parent));
        cur_lambda_depth--;
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cur));
        continue;
      }
      /* skip all lambdas that are not marked for merge */
      else if (mode == BETA_RED_LAMBDA_MERGE && bzla_node_is_lambda(real_cur)
               && !bzla_hashptr_table_get(merge_lambdas, real_cur)
               /* do not stop at parameterized lambdas, otherwise the
                * result may contain parameters that are not bound by any
                * lambda anymore */
               && !real_cur->parameterized
               /* do not stop at non-parameterized curried lambdas */
               && (!cur_parent || !bzla_node_is_lambda(cur_parent)))
      {
        cur_lambda_depth--;
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cur));
        continue;
      }
      /* stop at nodes that do not need to be rebuilt */
      else if ((!real_cur->lambda_below && !real_cur->parameterized)
               || bzla_node_is_update(real_cur))
      {
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (bzla_node_is_param(real_cur))
      {
        next = bzla_node_param_get_assigned_exp(real_cur);
        if (!next) next = real_cur;
        if (bzla_node_is_inverted(cur)) next = bzla_node_invert(next);
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, next));
        continue;
      }
      /* assign params of lambda expression */
      else if (bzla_node_is_lambda(real_cur) && cur_parent
               && bzla_node_is_apply(cur_parent)
               /* check if we have arguments on the stack */
               && !BZLA_EMPTY_STACK(arg_stack)
               /* if it is nested, its parameter is already assigned */
               && !bzla_node_param_get_assigned_exp(real_cur->e[0]))
      {
        args = BZLA_TOP_STACK(arg_stack);
        assert(bzla_node_is_regular(args));
        assert(bzla_node_is_args(args));

        if (cache)
        {
          cached = cached_beta_result(bzla, cache, real_cur, args);
          if (cached)
          {
            assert(!real_cur->parameterized);
            if (bzla_node_is_inverted(cur)) cached = bzla_node_invert(cached);
            BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cached));
            cur_lambda_depth--;
            continue;
          }
        }

#ifndef NDEBUG
        BZLA_PUSH_STACK(unassign_stack, real_cur);
#endif
        bzla_beta_assign_args(bzla, real_cur, args);
        BZLA_PUSH_STACK(reset, real_cur);
      }
      /* do not try to reduce lambdas below equalities as lambdas cannot
       * be eliminated. further, it may produce lambdas that break lemma
       * generation for extensionality */
      else if (bzla_node_is_lambda(real_cur) && cur_parent
               && (bzla_node_is_fun_eq(cur_parent)
                   || bzla_node_is_fun_cond(cur_parent)))
      {
        assert(!bzla_node_param_get_assigned_exp(real_cur->e[0]));
        cur_lambda_depth--;
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cur));
        continue;
      }
      /* do not try to reduce conditionals on functions below equalities
       * as they cannot be eliminated. */
      else if (bzla_node_is_fun_cond(real_cur)
               && bzla_node_is_fun_eq(cur_parent))
      {
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cur));
        continue;
      }

      bzla_hashint_map_add(mark, real_cur->id);
      BZLA_PUSH_STACK(stack, cur);
      BZLA_PUSH_STACK(stack, cur_parent);
      BZLA_PUSH_STACK(cleanup_stack, real_cur);
      for (i = 0; i < real_cur->arity; i++)
      {
        BZLA_PUSH_STACK(stack, bzla_simplify_exp(bzla, real_cur->e[i]));
        BZLA_PUSH_STACK(stack, real_cur);
      }
    }
    else if (!d->as_ptr)
    {
      assert(real_cur->arity >= 1);
      assert(BZLA_COUNT_STACK(arg_stack) >= real_cur->arity);

      arg_stack.top -= real_cur->arity;
      e = arg_stack.top; /* arguments in reverse order */

#ifndef NDEBUG
      for (i = 0; i < real_cur->arity; i++)
        assert(!bzla_node_is_simplified(e[i]));
#endif

      switch (real_cur->kind)
      {
        case BZLA_BV_SLICE_NODE:
          result = bzla_exp_bv_slice(bzla,
                                     e[0],
                                     bzla_node_bv_slice_get_upper(real_cur),
                                     bzla_node_bv_slice_get_lower(real_cur));
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_BV_AND_NODE:
          result = bzla_exp_bv_and(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_EQ_NODE:
        case BZLA_FP_EQ_NODE:
        case BZLA_FUN_EQ_NODE:
        case BZLA_RM_EQ_NODE:
          result = bzla_exp_eq(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_ADD_NODE:
          result = bzla_exp_bv_add(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_MUL_NODE:
          result = bzla_exp_bv_mul(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_ULT_NODE:
          result = bzla_exp_bv_ult(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_SLL_NODE:
          result = bzla_exp_bv_sll(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_SLT_NODE:
          result = bzla_exp_bv_slt(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_SRL_NODE:
          result = bzla_exp_bv_srl(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_UDIV_NODE:
          result = bzla_exp_bv_udiv(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_UREM_NODE:
          result = bzla_exp_bv_urem(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_CONCAT_NODE:
          result = bzla_exp_bv_concat(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_ABS_NODE:
          result = bzla_exp_fp_abs(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_INF_NODE:
          result = bzla_exp_fp_is_inf(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_NAN_NODE:
          result = bzla_exp_fp_is_nan(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_NEG_NODE:
          result = bzla_exp_fp_is_nan(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_NORM_NODE:
          result = bzla_exp_fp_is_normal(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_POS_NODE:
          result = bzla_exp_fp_is_pos(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_SUBNORM_NODE:
          result = bzla_exp_fp_is_subnormal(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_IS_ZERO_NODE:
          result = bzla_exp_fp_is_zero(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_NEG_NODE:
          result = bzla_exp_fp_is_neg(bzla, e[0]);
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_LTE_NODE:
          result = bzla_exp_fp_lte(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_LT_NODE:
          result = bzla_exp_fp_lt(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_MIN_NODE:
          result = bzla_exp_fp_min(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_MAX_NODE:
          result = bzla_exp_fp_max(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_SQRT_NODE:
          result = bzla_exp_fp_sqrt(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_REM_NODE:
          result = bzla_exp_fp_rem(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_RTI_NODE:
          result = bzla_exp_fp_rti(bzla, e[0], e[1]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_TO_SBV_NODE:
          assert(bzla_sort_is_fp(bzla, bzla_node_get_sort_id(cur)));
          result =
              bzla_exp_fp_to_sbv(bzla, e[0], e[1], bzla_node_get_sort_id(cur));
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_TO_UBV_NODE:
          assert(bzla_sort_is_fp(bzla, bzla_node_get_sort_id(cur)));
          result =
              bzla_exp_fp_to_ubv(bzla, e[0], e[1], bzla_node_get_sort_id(cur));
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_TO_FP_BV_NODE:
          assert(bzla_sort_is_fp(bzla, bzla_node_get_sort_id(cur)));
          result =
              bzla_exp_fp_to_fp_from_bv(bzla, e[0], bzla_node_get_sort_id(cur));
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_FP_TO_FP_FP_NODE:
          assert(bzla_sort_is_fp(bzla, bzla_node_get_sort_id(cur)));
          result = bzla_exp_fp_to_fp_from_fp(
              bzla, e[0], e[1], bzla_node_get_sort_id(cur));
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_TO_FP_INT_NODE:
          assert(bzla_sort_is_fp(bzla, bzla_node_get_sort_id(cur)));
          result = bzla_exp_fp_to_fp_from_int(
              bzla, e[0], e[1], bzla_node_get_sort_id(cur));
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_TO_FP_UINT_NODE:
          assert(bzla_sort_is_fp(bzla, bzla_node_get_sort_id(cur)));
          result = bzla_exp_fp_to_fp_from_uint(
              bzla, e[0], e[1], bzla_node_get_sort_id(cur));
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_FP_ADD_NODE:
          result = bzla_exp_fp_add(bzla, e[0], e[1], e[2]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          bzla_node_release(bzla, e[2]);
          break;
        case BZLA_FP_MUL_NODE:
          result = bzla_exp_fp_mul(bzla, e[0], e[1], e[2]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          bzla_node_release(bzla, e[2]);
          break;
        case BZLA_FP_DIV_NODE:
          result = bzla_exp_fp_div(bzla, e[0], e[1], e[2]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          bzla_node_release(bzla, e[2]);
          break;
        case BZLA_FP_FMA_NODE:
          result = bzla_exp_fp_fma(bzla, e[0], e[1], e[2], e[3]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          bzla_node_release(bzla, e[2]);
          bzla_node_release(bzla, e[3]);
          break;
        case BZLA_ARGS_NODE:
          assert(real_cur->arity >= 1);
          assert(real_cur->arity <= 3);
          if (real_cur->arity == 2)
          {
            next = e[0];
            e[0] = e[1];
            e[1] = next;
          }
          else if (real_cur->arity == 3)
          {
            next = e[0];
            e[0] = e[2];
            e[2] = next;
          }
          result = bzla_exp_args(bzla, e, real_cur->arity);
          bzla_node_release(bzla, e[0]);
          if (real_cur->arity >= 2) bzla_node_release(bzla, e[1]);
          if (real_cur->arity >= 3) bzla_node_release(bzla, e[2]);
          break;
        case BZLA_APPLY_NODE:
          if (bzla_node_is_fun(e[1]))
          {
            assert(bzla_node_is_args(e[0]));
            /* NOTE: do not use bzla_exp_apply here since
             * beta reduction is used in bzla_rewrite_apply_exp. */
            result = bzla_node_create_apply(bzla, e[1], e[0]);
          }
          else
          {
            result = bzla_node_copy(bzla, e[1]);
          }

          if (cache && mode == BETA_RED_FULL
              && bzla_node_is_lambda(real_cur->e[0]))
            cache_beta_result(bzla, cache, real_cur->e[0], e[0], result);

          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_LAMBDA_NODE:
          /* function equalities and conditionals always expect a lambda
           * as argument */
          if (cur_parent
              && (bzla_node_is_fun_eq(cur_parent)
                  || (bzla_node_is_fun_cond(cur_parent)
                      && !bzla_node_param_get_assigned_exp(real_cur->e[0]))))
          {
            assert(bzla_node_is_param(e[1]));
            result = bzla_exp_lambda(bzla, e[1], e[0]);
            if (real_cur->is_array) result->is_array = 1;
            if (bzla_node_lambda_get_static_rho(real_cur)
                && !bzla_node_lambda_get_static_rho(result))
              bzla_node_lambda_set_static_rho(
                  result, bzla_node_lambda_copy_static_rho(bzla, real_cur));
          }
          /* special case: lambda not reduced (not instantiated)
           *		 and is not constant */
          else if (real_cur->e[0] == e[1] && real_cur->e[1] == e[0]
                   && bzla_node_real_addr(e[0])->parameterized)
          {
            result = bzla_node_copy(bzla, real_cur);
          }
          /* main case: lambda reduced to some term without e[1] */
          else
          {
            result = bzla_node_copy(bzla, e[0]);
          }
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_UPDATE_NODE:
          result = bzla_exp_update(bzla, e[2], e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          bzla_node_release(bzla, e[2]);
          break;
        default:
          assert(bzla_node_is_cond(real_cur));
          result = bzla_exp_cond(bzla, e[2], e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          bzla_node_release(bzla, e[2]);
      }
      assert(!bzla_node_is_simplified(result));

      d->as_ptr = bzla_node_copy(bzla, result);
      if (real_cur->parameterized || bzla_node_is_lambda(real_cur))
        BZLA_PUSH_STACK(reset, real_cur);

      if (bzla_node_is_lambda(real_cur) && cur_parent
          && bzla_node_is_apply(cur_parent)
          && bzla_node_param_get_assigned_exp(real_cur->e[0]))
      {
        bzla_beta_unassign_params(bzla, real_cur);
#ifndef NDEBUG
        (void) BZLA_POP_STACK(unassign_stack);
#endif
        next = BZLA_POP_STACK(reset);
        do
        {
          bzla_hashint_map_remove(mark, next->id, &md);
          bzla_node_release(bzla, md.as_ptr);
          next = BZLA_POP_STACK(reset);
        } while (next != real_cur);
      }

      if (bzla_node_is_lambda(real_cur)
          && !real_cur->parameterized
          /* only count head lambdas (in case of curried lambdas) */
          && (!cur_parent || !bzla_node_is_lambda(cur_parent)))
        cur_lambda_depth--;

    BETA_REDUCE_PUSH_RESULT:
      if (bzla_node_is_inverted(cur)) result = bzla_node_invert(result);

      assert(!bzla_node_is_simplified(result));
      BZLA_PUSH_STACK(arg_stack, result);
    }
    else
    {
      assert(d->as_ptr);
      result = bzla_node_copy(bzla, d->as_ptr);
      goto BETA_REDUCE_PUSH_RESULT;
    }
  }
  assert(BZLA_EMPTY_STACK(unassign_stack));
  assert(cur_lambda_depth == 0);
  assert(BZLA_COUNT_STACK(arg_stack) == 1);
  result = BZLA_POP_STACK(arg_stack);
  assert(result);

  while (!BZLA_EMPTY_STACK(cleanup_stack))
  {
    cur = BZLA_POP_STACK(cleanup_stack);
    assert(bzla_node_is_regular(cur));
  }

  /* cleanup cache */
  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    bzla_node_release(bzla, mark->data[i].as_ptr);
  }

  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(arg_stack);
  BZLA_RELEASE_STACK(cleanup_stack);
  BZLA_RELEASE_STACK(reset);
#ifndef NDEBUG
  BZLA_RELEASE_STACK(unassign_stack);
#endif
  bzla_hashint_map_delete(mark);

  BZLALOG(2,
          "%s: result %s (%d)",
          __FUNCTION__,
          bzla_util_node2string(result),
          bzla_node_is_inverted(result));
  bzla->time.beta += bzla_util_time_stamp() - start;
  return result;
}

static BzlaNode *
beta_reduce_partial_aux(Bzla *bzla,
                        BzlaNode *exp,
                        BzlaPtrHashTable *cond_sel_if,
                        BzlaPtrHashTable *cond_sel_else,
                        BzlaPtrHashTable *conds,
                        BzlaNodePtrStack *conds_stack,
                        BzlaIntHashTable *conds_cache)
{
  assert(bzla);
  assert(exp);
  assert(!cond_sel_if || cond_sel_else);
  assert(!cond_sel_else || cond_sel_if);

  uint32_t i;
  double start;
  BzlaBitVector *eval_res;
  BzlaMemMgr *mm;
  BzlaNode *cur, *real_cur, *cur_parent, *next, *result, **e, *args, *tmp;
  BzlaNodePtrStack stack, arg_stack, reset;
  BzlaPtrHashTable *t;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d, md;

  if (!bzla_node_real_addr(exp)->parameterized && !bzla_node_is_lambda(exp))
    return bzla_node_copy(bzla, exp);

  start = bzla_util_time_stamp();
  bzla->stats.betap_reduce_calls++;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, arg_stack);
  BZLA_INIT_STACK(mm, reset);
  mark = bzla_hashint_map_new(mm);

  real_cur = bzla_node_real_addr(exp);

  /* skip all curried lambdas */
  if (bzla_node_is_lambda(real_cur)) exp = bzla_node_binder_get_body(real_cur);

  BZLA_PUSH_STACK(stack, exp);
  BZLA_PUSH_STACK(stack, 0);

  while (!BZLA_EMPTY_STACK(stack))
  {
    cur_parent = BZLA_POP_STACK(stack);
    cur        = BZLA_POP_STACK(stack);
    real_cur   = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(mark, real_cur->id);

    if (!d)
    {
      /* stop at non-parameterized nodes */
      if (!real_cur->parameterized)
      {
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, cur));
        continue;
      }
      /* push assigned argument of parameter on argument stack */
      else if (bzla_node_is_param(real_cur))
      {
        next = bzla_node_param_get_assigned_exp(real_cur);
        assert(next);
        next = bzla_node_cond_invert(cur, next);
        BZLA_PUSH_STACK(arg_stack, bzla_node_copy(bzla, next));
        continue;
      }
      /* assign params of lambda expression */
      else if (bzla_node_is_lambda(real_cur)
               && bzla_node_is_apply(cur_parent)
               /* check if we have arguments on the stack */
               && !BZLA_EMPTY_STACK(arg_stack)
               /* if it is nested, its parameter is already assigned */
               && !bzla_node_param_get_assigned_exp(real_cur->e[0]))
      {
        // TODO: there are no nested lambdas anymore is this still possible?
        args = BZLA_TOP_STACK(arg_stack);
        assert(bzla_node_is_args(args));
        bzla_beta_assign_args(bzla, real_cur, args);
        BZLA_PUSH_STACK(reset, real_cur);
      }

      bzla_hashint_map_add(mark, real_cur->id);
      BZLA_PUSH_STACK(stack, cur);
      BZLA_PUSH_STACK(stack, cur_parent);

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (bzla_node_is_cond(real_cur))
      {
        BZLA_PUSH_STACK(stack, real_cur->e[0]);
        BZLA_PUSH_STACK(stack, real_cur);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BZLA_PUSH_STACK(stack, real_cur->e[i]);
          BZLA_PUSH_STACK(stack, real_cur);
        }
      }
    }
    else if (!d->as_ptr)
    {
      assert(real_cur->parameterized);
      assert(real_cur->arity >= 1);

      if (bzla_node_is_cond(real_cur))
        arg_stack.top -= 1;
      else
      {
        assert(BZLA_COUNT_STACK(arg_stack) >= real_cur->arity);
        arg_stack.top -= real_cur->arity;
      }

      e = arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BZLA_BV_SLICE_NODE:
          result = bzla_exp_bv_slice(bzla,
                                     e[0],
                                     bzla_node_bv_slice_get_upper(real_cur),
                                     bzla_node_bv_slice_get_lower(real_cur));
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_BV_AND_NODE:
          result = bzla_exp_bv_and(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_EQ_NODE:
        case BZLA_FUN_EQ_NODE:
          result = bzla_exp_eq(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_ADD_NODE:
          result = bzla_exp_bv_add(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_MUL_NODE:
          result = bzla_exp_bv_mul(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_ULT_NODE:
          result = bzla_exp_bv_ult(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_SLL_NODE:
          result = bzla_exp_bv_sll(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_SLT_NODE:
          result = bzla_exp_bv_slt(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_SRL_NODE:
          result = bzla_exp_bv_srl(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_UDIV_NODE:
          result = bzla_exp_bv_udiv(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_UREM_NODE:
          result = bzla_exp_bv_urem(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_BV_CONCAT_NODE:
          result = bzla_exp_bv_concat(bzla, e[1], e[0]);
          bzla_node_release(bzla, e[0]);
          bzla_node_release(bzla, e[1]);
          break;
        case BZLA_ARGS_NODE:
          assert(real_cur->arity >= 1);
          assert(real_cur->arity <= 3);
          if (real_cur->arity == 2)
          {
            next = e[0];
            e[0] = e[1];
            e[1] = next;
          }
          else if (real_cur->arity == 3)
          {
            next = e[0];
            e[0] = e[2];
            e[2] = next;
          }
          result = bzla_exp_args(bzla, e, real_cur->arity);
          bzla_node_release(bzla, e[0]);
          if (real_cur->arity >= 2) bzla_node_release(bzla, e[1]);
          if (real_cur->arity >= 3) bzla_node_release(bzla, e[2]);
          break;
        case BZLA_APPLY_NODE:
          if (bzla_node_is_fun(e[1]))
          {
            result = bzla_node_create_apply(bzla, e[1], e[0]);
            bzla_node_release(bzla, e[1]);
          }
          else
            result = e[1];
          bzla_node_release(bzla, e[0]);
          break;
        case BZLA_LAMBDA_NODE:
          /* lambdas are always reduced to some term without e[1] */
          assert(!bzla_node_real_addr(e[0])->parameterized);
          result = e[0];
          bzla_node_release(bzla, e[1]);
          break;
        default:
          assert(bzla_node_is_cond(real_cur));
          /* only condition rebuilt, evaluate and choose branch */
          assert(!bzla_node_real_addr(e[0])->parameterized);
          eval_res = bzla_eval_exp(bzla, e[0]);
          assert(eval_res);

          /* save condition for consistency checking */
          if (conds
              && !bzla_hashptr_table_get(conds, bzla_node_real_addr(e[0])))
          {
            bzla_hashptr_table_add(
                conds, bzla_node_copy(bzla, bzla_node_real_addr(e[0])));
          }

          t = 0;
          if (bzla_bv_is_true(eval_res))
          {
            if (cond_sel_if) t = cond_sel_if;
            next = real_cur->e[1];
            tmp  = e[0];
          }
          else
          {
            assert(bzla_bv_is_false(eval_res));
            if (cond_sel_else) t = cond_sel_else;
            next = real_cur->e[2];
            tmp  = bzla_node_invert(e[0]);
          }

          if (conds_cache
              && !bzla_hashint_table_contains(conds_cache,
                                              bzla_node_get_id(tmp)))
          {
            assert(conds_stack);
            BZLA_PUSH_STACK(*conds_stack, bzla_node_copy(bzla, tmp));
          }

          if (t && !bzla_hashptr_table_get(t, e[0]))
            bzla_hashptr_table_add(t, bzla_node_copy(bzla, e[0]));

          bzla_bv_free(bzla->mm, eval_res);
          bzla_node_release(bzla, e[0]);

          assert(next);
          next = bzla_node_cond_invert(cur, next);
          BZLA_PUSH_STACK(stack, next);
          BZLA_PUSH_STACK(stack, real_cur);
          /* conditionals are not cached (e[0] is cached, and thus, the
           * resp. branch can always be selected without further
           * overhead. */
          bzla_hashint_map_remove(mark, real_cur->id, 0);
          continue;
      }

      d->as_ptr = bzla_node_copy(bzla, result);
      if (real_cur->parameterized || bzla_node_is_lambda(real_cur))
        BZLA_PUSH_STACK(reset, real_cur);

      if (bzla_node_is_lambda(real_cur))
      {
        bzla_beta_unassign_params(bzla, real_cur);
        next = BZLA_POP_STACK(reset);
        do
        {
          bzla_hashint_map_remove(mark, next->id, &md);
          bzla_node_release(bzla, md.as_ptr);
          next = BZLA_POP_STACK(reset);
        } while (next != real_cur);
      }

    BETA_REDUCE_PARTIAL_PUSH_RESULT:
      if (bzla_node_is_inverted(cur)) result = bzla_node_invert(result);

      BZLA_PUSH_STACK(arg_stack, result);
    }
    else
    {
      assert(real_cur->parameterized);
      assert(d->as_ptr);
      result = bzla_node_copy(bzla, d->as_ptr);
      assert(!bzla_node_is_lambda(result));
      goto BETA_REDUCE_PARTIAL_PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(arg_stack) == 1);
  result = BZLA_POP_STACK(arg_stack);
  assert(result);

  /* cleanup cache */
  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    bzla_node_release(bzla, mark->data[i].as_ptr);
  }

  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(arg_stack);
  BZLA_RELEASE_STACK(reset);
  bzla_hashint_map_delete(mark);

  BZLALOG(2,
          "%s: result %s (%d)",
          __FUNCTION__,
          bzla_util_node2string(result),
          bzla_node_is_inverted(result));
  bzla->time.betap += bzla_util_time_stamp() - start;

  return result;
}

BzlaNode *
bzla_beta_reduce_full(Bzla *bzla, BzlaNode *exp, BzlaPtrHashTable *cache)
{
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));
  return beta_reduce(bzla, exp, BETA_RED_FULL, 0, 0, cache);
}

BzlaNode *
bzla_beta_reduce_merge(Bzla *bzla,
                       BzlaNode *exp,
                       BzlaPtrHashTable *merge_lambdas)
{
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));
  return beta_reduce(bzla, exp, BETA_RED_LAMBDA_MERGE, 0, merge_lambdas, 0);
}

BzlaNode *
bzla_beta_reduce_bounded(Bzla *bzla, BzlaNode *exp, int32_t bound)
{
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));
  return beta_reduce(bzla, exp, BETA_RED_BOUNDED, bound, 0, 0);
}

BzlaNode *
bzla_beta_reduce_partial(Bzla *bzla, BzlaNode *exp, BzlaPtrHashTable *conds)
{
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));
  return beta_reduce_partial_aux(bzla, exp, 0, 0, conds, 0, 0);
}

BzlaNode *
bzla_beta_reduce_partial_collect(Bzla *bzla,
                                 BzlaNode *exp,
                                 BzlaPtrHashTable *cond_sel_if,
                                 BzlaPtrHashTable *cond_sel_else)
{
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));
  return beta_reduce_partial_aux(
      bzla, exp, cond_sel_if, cond_sel_else, 0, 0, 0);
}

BzlaNode *
bzla_beta_reduce_partial_collect_new(Bzla *bzla,
                                     BzlaNode *exp,
                                     BzlaNodePtrStack *exps,
                                     BzlaIntHashTable *cache)
{
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));
  return beta_reduce_partial_aux(bzla, exp, 0, 0, 0, exps, cache);
}
