/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlachkmodel.h"

#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlaopt.h"
#include "bzlarm.h"
#include "bzlasubst.h"
#include "preprocess/bzlapreprocess.h"
#include "preprocess/bzlavarsubst.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

struct BzlaCheckModelContext
{
  Bzla *bzla;
  Bzla *clone;
  BzlaPtrHashTable *inputs;
};

static BzlaPtrHashTable *
map_inputs(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);

  BzlaNode *cur;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *inputs;

  inputs = bzla_hashptr_table_new(clone->mm,
                                  (BzlaHashPtr) bzla_node_hash_by_id,
                                  (BzlaCmpPtr) bzla_node_compare_by_id);

  bzla_iter_hashptr_init(&it, clone->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    b   = bzla_hashptr_table_get(bzla->inputs, cur);
    assert(b);

    assert(!bzla_hashptr_table_get(inputs, cur));
    bzla_hashptr_table_add(inputs, bzla_node_copy(clone, cur))->data.as_ptr =
        bzla_node_copy(bzla, (BzlaNode *) b->key);
  }

  return inputs;
}

void
bzla_check_model(BzlaCheckModelContext *ctx)
{
  assert(ctx);

  uint32_t i;
  int32_t sat_res;
  Bzla *bzla, *clone;
  BzlaNode *cur, *exp, *simp_clone, *model, *eq;
  BzlaNode *args, *apply;
  BzlaPtrHashTableIterator it;
  const BzlaPtrHashTable *fmodel;
  const BzlaBitVector *value;
  BzlaBitVectorTuple *args_tuple;
  BzlaNodePtrStack consts;

  bzla = ctx->bzla;

  BZLALOG(1, "start check model");

  assert(bzla->last_sat_result == BZLA_RESULT_SAT);
  clone = ctx->clone;

  if (!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS))
  {
    switch (bzla_opt_get(bzla, BZLA_OPT_ENGINE))
    {
      case BZLA_ENGINE_SLS:
      case BZLA_ENGINE_PROP:
      case BZLA_ENGINE_AIGPROP:
        bzla->slv->api.generate_model(bzla->slv, false, false);
        break;
      default: bzla->slv->api.generate_model(bzla->slv, false, true);
    }
  }

  /* Reset terminate callbacks. */
  clone->cbs.term.fun   = 0;
  clone->cbs.term.state = 0;

  /* formula did not change since last sat call, we have to reset assumptions
   * from the previous run */
  if (clone->valid_assignments) bzla_reset_incremental_usage(clone);

  /* add assumptions as assertions */
  bzla_fixate_assumptions(clone);

  /* add bit vector variable models */
  BZLA_INIT_STACK(clone->mm, consts);
  bzla_iter_hashptr_init(&it, ctx->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    exp = (BzlaNode *) it.bucket->data.as_ptr;
    assert(exp);
    assert(bzla_node_is_regular(exp));
    assert(exp->bzla == bzla);

    cur  = bzla_iter_hashptr_next(&it);
    assert(bzla_node_is_regular(cur));
    assert(cur->bzla == clone);
    simp_clone      = bzla_simplify_exp(clone, cur);

    if (bzla_node_is_fun(simp_clone))
    {
      fmodel = bzla_model_get_fun(bzla, exp);
      if (!fmodel) continue;

      BzlaSortId domain_sort =
          bzla_sort_fun_get_domain(clone, bzla_node_get_sort_id(simp_clone));
      assert(bzla_sort_is_tuple(clone, domain_sort));
      BzlaTupleSortIterator sit;

      BZLALOG(2, "assert model for %s", bzla_util_node2string(simp_clone));
      bzla_iter_hashptr_init(&it, (BzlaPtrHashTable *) fmodel);
      while (bzla_iter_hashptr_has_next(&it))
      {
        value      = (BzlaBitVector *) it.bucket->data.as_ptr;
        args_tuple = bzla_iter_hashptr_next(&it);

        /* Ignore default values of constant arrays */
        if (!args_tuple->arity) continue;

        /* create condition */
        assert(BZLA_EMPTY_STACK(consts));
        bzla_iter_tuple_sort_init(&sit, clone, domain_sort);
        for (i = 0; i < args_tuple->arity; i++)
        {
          assert(bzla_iter_tuple_sort_has_next(&sit));
          model = bzla_node_mk_value(
              clone, bzla_iter_tuple_sort_next(&sit), args_tuple->bv[i]);
          BZLA_PUSH_STACK(consts, model);
          BZLALOG(2, "  arg%u: %s", i, bzla_util_node2string(model));
        }

        args  = bzla_exp_args(clone, consts.start, BZLA_COUNT_STACK(consts));
        apply = bzla_exp_apply(clone, simp_clone, args);
        model = bzla_node_mk_value(clone, bzla_node_get_sort_id(apply), value);
        eq = bzla_exp_eq(clone, apply, model);

        BZLALOG(2, "  value: %s", bzla_util_node2string(model));

        bzla_assert_exp(clone, eq);
        bzla_node_release(clone, eq);
        bzla_node_release(clone, model);
        bzla_node_release(clone, apply);
        bzla_node_release(clone, args);

        while (!BZLA_EMPTY_STACK(consts))
          bzla_node_release(clone, BZLA_POP_STACK(consts));
      }
    }
    else
    {
      value = bzla_model_get_bv(bzla, exp);
      model =
          bzla_node_mk_value(clone, bzla_node_get_sort_id(simp_clone), value);

      BZLALOG(2,
              "assert model for %s (%s) [%s]",
              bzla_util_node2string(simp_clone),
              bzla_node_get_symbol(clone, cur),
              bzla_util_node2string(model));

      eq = bzla_exp_eq(clone, simp_clone, model);
      bzla_assert_exp(clone, eq);
      bzla_node_release(clone, eq);
      bzla_node_release(clone, model);
    }
  }
  BZLA_RELEASE_STACK(consts);

  sat_res = bzla_check_sat(clone, -1, -1);
  BZLA_ABORT(sat_res == BZLA_RESULT_UNSAT, "invalid model");
  BZLALOG(1, "end check model");
}

BzlaCheckModelContext *
bzla_check_model_init(Bzla *bzla)
{
  BzlaCheckModelContext *ctx;

  BZLA_CNEW(bzla->mm, ctx);

  ctx->bzla  = bzla;
  ctx->clone = bzla_clone_exp_layer(bzla, 0, true);
  bzla_set_msg_prefix(ctx->clone, "chkm");
  bzla_opt_set(ctx->clone, BZLA_OPT_FUN_DUAL_PROP, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_CHECK_UNCONSTRAINED, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_CHECK_MODEL, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_PRINT_DIMACS, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_PP_EXTRACT_LAMBDAS, 0);
  bzla_set_term(ctx->clone, 0, 0);

  bzla_opt_set(ctx->clone, BZLA_OPT_ENGINE, BZLA_ENGINE_FUN);
  if (ctx->clone->slv)
  {
    ctx->clone->slv->api.delet(ctx->clone->slv);
    ctx->clone->slv = 0;
  }

  ctx->inputs = map_inputs(bzla, ctx->clone);

  return ctx;
}

void
bzla_check_model_delete(BzlaCheckModelContext *ctx)
{
  BzlaPtrHashTableIterator it;
  bzla_iter_hashptr_init(&it, ctx->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(ctx->bzla, (BzlaNode *) it.bucket->data.as_ptr);
    bzla_node_release(ctx->clone, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(ctx->inputs);
  bzla_delete(ctx->clone);
  BZLA_DELETE(ctx->bzla->mm, ctx);
}
