/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2020 Mathias Preiner.
 *  Copyright (C) 2012-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlachkmodel.h"

#include "bzlaabort.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlaopt.h"
#include "bzlasubst.h"
#include "preprocess/bzlapreprocess.h"
#include "preprocess/bzlavarsubst.h"
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

  bzla_iter_hashptr_init(&it, clone->bv_vars);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    b   = bzla_hashptr_table_get(bzla->bv_vars, cur);
    assert(b);

    assert(!bzla_hashptr_table_get(inputs, cur));
    bzla_hashptr_table_add(inputs, bzla_node_copy(clone, cur))->data.as_ptr =
        bzla_node_copy(bzla, (BzlaNode *) b->key);
  }

  bzla_iter_hashptr_init(&it, clone->ufs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    b   = bzla_hashptr_table_get(bzla->ufs, cur);
    assert(b);

    assert(!bzla_hashptr_table_get(inputs, cur));
    bzla_hashptr_table_add(inputs, bzla_node_copy(clone, cur))->data.as_ptr =
        bzla_node_copy(bzla, (BzlaNode *) b->key);
  }

  return inputs;
}

static void
rebuild_formula(Bzla *bzla, uint32_t rewrite_level)
{
  assert(bzla);

  uint32_t i, cnt;
  BzlaNode *cur;
  BzlaPtrHashTable *t;

  BZLALOG(1, "rebuild formula with rewrite level %u", rewrite_level);

  /* set new rewrite level */
  bzla_opt_set(bzla, BZLA_OPT_REWRITE_LEVEL, rewrite_level);

  t = bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = 1, cnt = BZLA_COUNT_STACK(bzla->nodes_id_table); i <= cnt; i++)
  {
    if (!(cur = BZLA_PEEK_STACK(bzla->nodes_id_table, cnt - i))) continue;

    if (bzla_node_is_simplified(cur)) continue;

    if (cur->arity == 0)
    {
      assert(bzla_node_is_var(cur) || bzla_node_is_bv_const(cur)
             || bzla_node_is_rm_const(cur) || bzla_node_is_fp_const(cur)
             || bzla_node_is_param(cur) || bzla_node_is_uf(cur));
      bzla_hashptr_table_add(t, cur);
    }
  }

  bzla_substitute_and_rebuild(bzla, t);
  bzla_hashptr_table_delete(t);

  BZLALOG(1, "rebuild formula done");
}

void
bzla_check_model(BzlaCheckModelContext *ctx)
{
  assert(ctx);

  uint32_t i;
  int32_t sat_res;
  Bzla *bzla, *clone;
  BzlaNode *cur, *exp, *simp, *simp_clone, *real_simp_clone, *model, *eq;
  BzlaNode *args, *apply, *wb;
  BzlaPtrHashTableIterator it;
  const BzlaPtrHashTable *fmodel;
  BzlaBitVector *value;
  BzlaBitVectorTuple *args_tuple;
  BzlaNodePtrStack consts;

  bzla = ctx->bzla;

  BZLALOG(1, "start check model");

  assert(bzla->last_sat_result == BZLA_RESULT_SAT);
  clone = ctx->clone;

  if (!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN))
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
  clone->cbs.term.done  = 0;

  /* formula did not change since last sat call, we have to reset assumptions
   * from the previous run */
  if (clone->valid_assignments) bzla_reset_incremental_usage(clone);

  /* add assumptions as assertions */
  bzla_iter_hashptr_init(&it, clone->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_assert_exp(clone, bzla_iter_hashptr_next(&it));
  bzla_reset_assumptions(clone);

  /* clone->assertions have been already added at this point. */
  while (!BZLA_EMPTY_STACK(clone->assertions))
  {
    cur = BZLA_POP_STACK(clone->assertions);
    bzla_node_release(clone, cur);
  }

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0)
  {
    bzla_substitute_var_exps(clone);
  }

  /* rebuild formula with new rewriting level */
  rebuild_formula(clone, 3);

  /* add bit vector variable models */
  BZLA_INIT_STACK(clone->mm, consts);
  bzla_iter_hashptr_init(&it, ctx->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    exp = (BzlaNode *) it.bucket->data.as_ptr;
    assert(exp);
    assert(bzla_node_is_regular(exp));
    assert(exp->bzla == bzla);
    /* Note: we do not want simplified constraints here */
    simp = bzla_node_get_simplified(bzla, exp);
    cur  = bzla_iter_hashptr_next(&it);
    assert(bzla_node_is_regular(cur));
    assert(cur->bzla == clone);
    simp_clone      = bzla_simplify_exp(clone, cur);
    real_simp_clone = bzla_node_real_addr(simp_clone);

    if (bzla_node_is_fun(real_simp_clone))
    {
      fmodel = bzla_model_get_fun(bzla, simp);
      if (!fmodel) continue;

      BZLALOG(2, "assert model for %s", bzla_util_node2string(real_simp_clone));
      bzla_iter_hashptr_init(&it, (BzlaPtrHashTable *) fmodel);
      while (bzla_iter_hashptr_has_next(&it))
      {
        value      = (BzlaBitVector *) it.bucket->data.as_ptr;
        args_tuple = bzla_iter_hashptr_next(&it);

        /* Ignore default values of constant arrays */
        if (!args_tuple->arity) continue;

        /* create condition */
        assert(BZLA_EMPTY_STACK(consts));
        for (i = 0; i < args_tuple->arity; i++)
        {
          model = bzla_exp_bv_const(clone, args_tuple->bv[i]);
          BZLA_PUSH_STACK(consts, model);
          BZLALOG(2, "  arg%u: %s", i, bzla_util_node2string(model));
        }

        args  = bzla_exp_args(clone, consts.start, BZLA_COUNT_STACK(consts));
        apply = bzla_exp_apply(clone, real_simp_clone, args);
        model = bzla_exp_bv_const(clone, value);
        eq    = bzla_exp_eq(clone, apply, model);

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
      /* we need to invert the assignment if simplified is inverted */
      model =
          bzla_exp_bv_const(clone,
                            (BzlaBitVector *) bzla_model_get_bv(
                                bzla, bzla_node_cond_invert(simp_clone, simp)));
      BZLALOG(2,
              "assert model for %s (%s) [%s]",
              bzla_util_node2string(real_simp_clone),
              bzla_node_get_symbol(clone, cur),
              bzla_util_node2string(model));

      if (bzla_node_is_fp(clone, real_simp_clone)
          || bzla_node_is_rm(clone, real_simp_clone))
      {
        wb = bzla_fp_word_blast(clone, real_simp_clone);
        eq = bzla_exp_eq(clone, wb, model);
      }
      else
      {
        eq = bzla_exp_eq(clone, real_simp_clone, model);
      }
      bzla_assert_exp(clone, eq);
      bzla_node_release(clone, eq);
      bzla_node_release(clone, model);
    }
  }
  BZLA_RELEASE_STACK(consts);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0)
    bzla_substitute_var_exps(clone);

  bzla_opt_set(clone, BZLA_OPT_BETA_REDUCE, BZLA_BETA_REDUCE_ALL);

  // bzla_print_model (bzla, "btor", stdout);
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
  bzla_opt_set(ctx->clone, BZLA_OPT_CHK_UNCONSTRAINED, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_CHK_MODEL, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_CHK_FAILED_ASSUMPTIONS, 0);
  bzla_opt_set(ctx->clone, BZLA_OPT_PRINT_DIMACS, 0);
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
