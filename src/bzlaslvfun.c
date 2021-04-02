/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaslvfun.h"

#include "bzlabeta.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzladcr.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlalsutils.h"
#include "bzlamodel.h"
#include "bzlaopt.h"
#include "bzlaprintmodel.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahash.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlastack.h"
#include "utils/bzlaunionfind.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

static BzlaFunSolver *
clone_fun_solver(Bzla *clone, BzlaFunSolver *slv, BzlaNodeMap *exp_map)
{
  assert(clone);
  assert(slv);
  assert(slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(exp_map);

  uint32_t h;
  Bzla *bzla;
  BzlaFunSolver *res;

  bzla = slv->bzla;

  BZLA_NEW(clone->mm, res);
  memcpy(res, slv, sizeof(BzlaFunSolver));

  res->bzla   = clone;
  res->lemmas = bzla_hashptr_table_clone(
      clone->mm, slv->lemmas, bzla_clone_key_as_node, 0, exp_map, 0);

  bzla_clone_node_ptr_stack(
      clone->mm, &slv->cur_lemmas, &res->cur_lemmas, exp_map, false);

  bzla_clone_node_ptr_stack(
      clone->mm, &slv->constraints, &res->constraints, exp_map, false);

  if (slv->score)
  {
    h = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);
    if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP)
    {
      res->score = bzla_hashptr_table_clone(clone->mm,
                                            slv->score,
                                            bzla_clone_key_as_node,
                                            bzla_clone_data_as_ptr_htable,
                                            exp_map,
                                            exp_map);
    }
    else
    {
      assert(h == BZLA_JUST_HEUR_BRANCH_MIN_DEP);
      res->score = bzla_hashptr_table_clone(clone->mm,
                                            slv->score,
                                            bzla_clone_key_as_node,
                                            bzla_clone_data_as_int,
                                            exp_map,
                                            0);
    }
  }

  BZLA_INIT_STACK(clone->mm, res->stats.lemmas_size);
  if (BZLA_SIZE_STACK(slv->stats.lemmas_size) > 0)
  {
    BZLA_CNEWN(clone->mm,
               res->stats.lemmas_size.start,
               BZLA_SIZE_STACK(slv->stats.lemmas_size));

    res->stats.lemmas_size.end =
        res->stats.lemmas_size.start + BZLA_SIZE_STACK(slv->stats.lemmas_size);
    res->stats.lemmas_size.top =
        res->stats.lemmas_size.start + BZLA_COUNT_STACK(slv->stats.lemmas_size);
    memcpy(res->stats.lemmas_size.start,
           slv->stats.lemmas_size.start,
           BZLA_SIZE_STACK(slv->stats.lemmas_size) * sizeof(uint32_t));
  }

  return res;
}

static void
delete_fun_solver(BzlaFunSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  BzlaPtrHashTable *t;
  BzlaPtrHashTableIterator it, iit;
  BzlaNode *exp;
  Bzla *bzla;

  bzla = slv->bzla;

  bzla_iter_hashptr_init(&it, slv->lemmas);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(slv->lemmas);

  if (slv->score)
  {
    bzla_iter_hashptr_init(&it, slv->score);
    while (bzla_iter_hashptr_has_next(&it))
    {
      if (bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC)
          == BZLA_JUST_HEUR_BRANCH_MIN_APP)
      {
        t   = (BzlaPtrHashTable *) it.bucket->data.as_ptr;
        exp = bzla_iter_hashptr_next(&it);
        bzla_node_release(bzla, exp);

        bzla_iter_hashptr_init(&iit, t);
        while (bzla_iter_hashptr_has_next(&iit))
          bzla_node_release(bzla, bzla_iter_hashptr_next(&iit));
        bzla_hashptr_table_delete(t);
      }
      else
      {
        assert(bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC)
               == BZLA_JUST_HEUR_BRANCH_MIN_DEP);
        bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
      }
    }
    bzla_hashptr_table_delete(slv->score);
  }

  BZLA_RELEASE_STACK(slv->cur_lemmas);
  while (!BZLA_EMPTY_STACK(slv->constraints))
  {
    bzla_node_release(bzla, BZLA_POP_STACK(slv->constraints));
  }
  BZLA_RELEASE_STACK(slv->constraints);
  BZLA_RELEASE_STACK(slv->stats.lemmas_size);
  BZLA_DELETE(bzla->mm, slv);
  bzla->slv = 0;
}

/*------------------------------------------------------------------------*/

static bool
incremental_required(Bzla *bzla)
{
  bool res = false;
  uint32_t i;
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack stack;
  BzlaIntHashTable *cache;

  /* If model generation is enabled for all nodes, we don't have to traverse
   * the formula, but check if functions have been created. */
  if (bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS) > 1)
  {
    return bzla->ufs->count > 0 || bzla->lambdas->count > 0;
  }

  BZLA_INIT_STACK(bzla->mm, stack);
  cache = bzla_hashint_table_new(bzla->mm);
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(stack, cur);
  }

  bzla_iter_hashptr_init(&it, bzla->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_simplify_exp(bzla, bzla_iter_hashptr_next(&it));
    BZLA_PUSH_STACK(stack, cur);
  }

  while (!BZLA_EMPTY_STACK(stack))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(stack));

    if (bzla_hashint_table_contains(cache, cur->id)) continue;

    bzla_hashint_table_add(cache, cur->id);
    if (bzla_node_is_fun(cur) || cur->apply_below
        || cur->lambda_below
        // These FP operators introduce uninterpreted functions.
        || bzla_node_is_fp_to_sbv(cur) || bzla_node_is_fp_to_ubv(cur)
        || bzla_node_is_fp_min(cur) || bzla_node_is_fp_max(cur))
    {
      res = true;
      break;
    }

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
  }

  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(stack);
  return res;
}

static void
configure_sat_mgr(Bzla *bzla)
{
  BzlaSATMgr *smgr;

  smgr = bzla_get_sat_mgr(bzla);
  if (bzla_sat_is_initialized(smgr)) return;
  bzla_sat_enable_solver(smgr);
  bzla_sat_init(smgr);

  /* reset SAT solver to non-incremental if all functions have been
   * eliminated */
  if (!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL) && smgr->inc_required
      && !incremental_required(bzla))
  {
    smgr->inc_required = false;
    BZLA_MSG(bzla->msg,
             1,
             "no functions found, resetting SAT solver to non-incremental");

    if (bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP))
    {
      bzla_opt_set(bzla, BZLA_OPT_FUN_DUAL_PROP, 0);
      BZLA_MSG(bzla->msg, 1, "no functions found, disabling --fun:dual-prop");
    }
  }

  BZLA_ABORT(smgr->inc_required && !bzla_sat_mgr_has_incremental_support(smgr),
             "selected SAT solver '%s' does not support incremental mode",
             smgr->name);
}

static BzlaSolverResult
timed_sat_sat(Bzla *bzla, int32_t limit)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);

  double start, delta;
  BzlaSolverResult res;
  BzlaSATMgr *smgr;
  BzlaAIGMgr *amgr;

  amgr = bzla_get_aig_mgr(bzla);
  BZLA_MSG(bzla->msg,
           1,
           "%u AIG vars, %u AIG ands, %u CNF vars, %u CNF clauses",
           amgr->cur_num_aig_vars,
           amgr->cur_num_aigs,
           amgr->num_cnf_vars,
           amgr->num_cnf_clauses);
  smgr  = bzla_get_sat_mgr(bzla);
  start = bzla_util_time_stamp();
  res   = bzla_sat_check_sat(smgr, limit);
  delta = bzla_util_time_stamp() - start;
  BZLA_FUN_SOLVER(bzla)->time.sat += delta;

  BZLA_MSG(
      bzla->msg, 2, "SAT solver returns %d after %.1f seconds", res, delta);

  return res;
}

static bool
has_bv_assignment(Bzla *bzla, BzlaNode *exp)
{
  exp = bzla_node_real_addr(exp);
  return (bzla->bv_model && bzla_hashint_map_contains(bzla->bv_model, exp->id))
         || bzla_node_is_synth(exp) || bzla_node_is_bv_const(exp);
}

static BzlaBitVector *
get_bv_assignment(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla->bv_model);
  assert(!bzla_node_real_addr(exp)->parameterized);

  BzlaNode *real_exp;
  BzlaBitVector *bv, *result;
  BzlaHashTableData *d;

  exp = bzla_node_get_simplified(bzla, exp);

  real_exp = bzla_node_real_addr(exp);
  if ((d = bzla_hashint_map_get(bzla->bv_model, real_exp->id)))
    bv = bzla_bv_copy(bzla->mm, d->as_ptr);
  else /* cache assignment to avoid querying the sat solver multiple times */
  {
    /* synthesized nodes are always encoded and have an assignment */
    if (bzla_node_is_synth(real_exp))
      bv = bzla_model_get_bv_assignment(bzla, real_exp);
    else if (bzla_node_is_bv_const(real_exp))
      bv = bzla_bv_copy(bzla->mm, bzla_node_bv_const_get_bits(real_exp));
    /* initialize var, apply, and feq nodes if they are not yet synthesized
     * and encoded (not in the BV skeleton yet, and thus unconstrained). */
    else if (bzla_node_is_bv_var(real_exp) || bzla_node_is_apply(real_exp)
             || bzla_node_is_fun_eq(real_exp))
    {
      if (!bzla_node_is_synth(real_exp))
        BZLALOG(1, "zero-initialize: %s", bzla_util_node2string(real_exp));
      bv = bzla_model_get_bv_assignment(bzla, real_exp);
    }
    else
      bv = bzla_eval_exp(bzla, real_exp);
    bzla_model_add_to_bv(bzla, bzla->bv_model, real_exp, bv);
  }

  if (bzla_node_is_inverted(exp))
  {
    result = bzla_bv_not(bzla->mm, bv);
    bzla_bv_free(bzla->mm, bv);
  }
  else
    result = bv;

  return result;
}

/*------------------------------------------------------------------------*/

static Bzla *
new_exp_layer_clone_for_dual_prop(Bzla *bzla,
                                  BzlaNodeMap **exp_map,
                                  BzlaNode **root)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(exp_map);
  assert(root);

  double start;
  Bzla *clone;
  BzlaNode *cur, *and;
  BzlaPtrHashTableIterator it;

  /* empty formula */
  if (bzla->unsynthesized_constraints->count == 0) return 0;

  start = bzla_util_time_stamp();
  clone = bzla_clone_exp_layer(bzla, exp_map, true);
  assert(!clone->synthesized_constraints->count);
  assert(clone->embedded_constraints->count == 0);
  assert(clone->unsynthesized_constraints->count);

  bzla_opt_set(clone, BZLA_OPT_PRODUCE_MODELS, 0);
  bzla_opt_set(clone, BZLA_OPT_INCREMENTAL, 1);
  //  bzla_opt_set (clone, BZLA_OPT_LOGLEVEL, 0);
  //  bzla_opt_set (clone, BZLA_OPT_VERBOSITY, 0);
  bzla_opt_set(clone, BZLA_OPT_FUN_DUAL_PROP, 0);

  assert(!bzla_sat_is_initialized(bzla_get_sat_mgr(clone)));
  bzla_opt_set_str(clone, BZLA_OPT_SAT_ENGINE, "plain=1");
  configure_sat_mgr(clone);

  bzla_iter_hashptr_init(&it, clone->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, clone->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur                                  = bzla_iter_hashptr_next(&it);
    bzla_node_real_addr(cur)->constraint = 0;
    if (!*root)
    {
      *root = bzla_node_copy(clone, cur);
    }
    else
    {
      and = bzla_exp_bv_and(clone, *root, cur);
      bzla_node_release(clone, *root);
      *root = and;
    }
  }

  bzla_iter_hashptr_init(&it, clone->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, clone->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(clone, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(clone->unsynthesized_constraints);
  bzla_hashptr_table_delete(clone->assumptions);
  clone->unsynthesized_constraints =
      bzla_hashptr_table_new(clone->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  clone->assumptions =
      bzla_hashptr_table_new(clone->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);

  BZLA_FUN_SOLVER(bzla)->time.search_init_apps_cloning +=
      bzla_util_time_stamp() - start;
  return clone;
}

static void
assume_inputs(Bzla *bzla,
              Bzla *clone,
              BzlaNodePtrStack *inputs,
              BzlaNodeMap *exp_map,
              BzlaNodeMap *key_map,
              BzlaNodeMap *assumptions)
{
  assert(bzla);
  assert(clone);
  assert(inputs);
  assert(exp_map);
  assert(key_map);
  assert(key_map->table->count == 0);
  assert(assumptions);

  uint32_t i;
  BzlaNode *cur_bzla, *cur_clone, *bv_const, *bv_eq;
  BzlaBitVector *bv;

  for (i = 0; i < BZLA_COUNT_STACK(*inputs); i++)
  {
    cur_bzla  = BZLA_PEEK_STACK(*inputs, i);
    cur_clone = bzla_nodemap_mapped(exp_map, cur_bzla);
    assert(cur_clone);
    assert(bzla_node_is_regular(cur_clone));
    assert(!bzla_nodemap_mapped(key_map, cur_clone));
    bzla_nodemap_map(key_map, cur_clone, cur_bzla);

    assert(bzla_node_is_regular(cur_bzla));
    bv       = get_bv_assignment(bzla, cur_bzla);
    bv_const = bzla_exp_bv_const(clone, bv);
    bzla_bv_free(bzla->mm, bv);
    bv_eq = bzla_exp_eq(clone, cur_clone, bv_const);
    BZLALOG(1,
            "assume input: %s (%s = %s)",
            bzla_util_node2string(bv_eq),
            bzla_util_node2string(cur_bzla),
            bzla_util_node2string(bv_const));
    bzla_assume_exp(clone, bv_eq);
    bzla_nodemap_map(assumptions, bv_eq, cur_clone);
    bzla_node_release(clone, bv_const);
    bzla_node_release(clone, bv_eq);
  }
}

static BzlaNode *
create_function_disequality_witness(Bzla *bzla, BzlaNode *feq)
{
  assert(bzla_node_is_regular(feq));
  assert(bzla_node_is_fun_eq(feq));

  BzlaMemMgr *mm;
  BzlaNode *var, *app0, *app1, *eq, *arg;
  BzlaSortId funsort, sort;
  BzlaNodePtrStack args;
  BzlaTupleSortIterator it;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, args);
  funsort = bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(feq->e[0]));

  size_t len = bzla_util_num_digits(feq->id) + strlen("witness()_");

  uint32_t i = 0;
  bzla_iter_tuple_sort_init(&it, bzla, funsort);
  while (bzla_iter_tuple_sort_has_next(&it))
  {
    sort = bzla_iter_tuple_sort_next(&it);
    assert(!bzla_sort_is_fun(bzla, sort));
    size_t buf_len = len + bzla_util_num_digits(i) + 1;
    char buf[buf_len];
    snprintf(buf, buf_len, "witness(%u)_%u", feq->id, i);
    var = bzla_exp_var(bzla, sort, buf);
    BZLA_PUSH_STACK(args, var);
    ++i;
  }

  arg  = bzla_exp_args(bzla, args.start, BZLA_COUNT_STACK(args));
  app0 = bzla_node_create_apply(bzla, feq->e[0], arg);
  app1 = bzla_node_create_apply(bzla, feq->e[1], arg);
  eq   = bzla_exp_eq(bzla, app0, app1);

  bzla_node_release(bzla, arg);
  bzla_node_release(bzla, app0);
  bzla_node_release(bzla, app1);
  while (!BZLA_EMPTY_STACK(args)) bzla_node_release(bzla, BZLA_POP_STACK(args));
  BZLA_RELEASE_STACK(args);

  return bzla_node_invert(eq);
}

/* For every function equality f = g, add a witness for disequality:
 * f != g -> f(a) != g(a) */
static void
add_function_disequality_witnesses(Bzla *bzla)
{
  uint32_t i;
  BzlaNode *cur, *neq, *con;
  BzlaNodePtrStack feqs, visit;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashBucket *b;
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, visit);
  bzla_iter_hashptr_init(&it, bzla->inputs);
  bzla_iter_hashptr_queue(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  /* Note: We don't have to traverse synthesized_constraints as we already
   * created witnesses for them in a previous check-sat call. */
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    cur = bzla_node_get_simplified(bzla, cur);
    BZLA_PUSH_STACK(visit, cur);
  }

  /* collect all reachable function equalities */
  cache = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, feqs);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)) continue;

    bzla_hashint_table_add(cache, cur->id);
    if (bzla_node_is_fun_eq(cur))
    {
      b = bzla_hashptr_table_get(bzla->feqs, cur);
      /* already visited and created inequality constraint in a previous
       * sat call */
      if (b->data.as_int) continue;
      BZLA_PUSH_STACK(feqs, cur);
      /* if the lambdas are not arrays, we cannot handle equalities */
      // BZLA_ABORT(
      //    (bzla_node_is_lambda(cur->e[0]) && !bzla_node_is_array(cur->e[0]))
      //        || (bzla_node_is_lambda(cur->e[1])
      //            && !bzla_node_is_array(cur->e[1])),
      //    "equality over non-array lambdas not supported yet");
    }
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  /* add inequality constraint for every reachable function equality */
  while (!BZLA_EMPTY_STACK(feqs))
  {
    cur = BZLA_POP_STACK(feqs);
    assert(bzla_node_is_fun_eq(cur));
    assert(!cur->parameterized);
    b = bzla_hashptr_table_get(bzla->feqs, cur);
    assert(b);
    assert(b->data.as_int == 0);
    b->data.as_int = 1;
    neq            = create_function_disequality_witness(bzla, cur);
    con            = bzla_exp_implies(bzla, bzla_node_invert(cur), neq);
    bzla_assert_exp(bzla, con);
    bzla_node_release(bzla, con);
    bzla_node_release(bzla, neq);
    BZLALOG(2, "add inequality constraint for %s", bzla_util_node2string(cur));
  }
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(feqs);
  bzla_hashint_table_delete(cache);
}

static int32_t
sat_aux_bzla_dual_prop(Bzla *bzla)
{
  assert(bzla);

  BzlaSolverResult result;

  if (bzla->inconsistent) goto DONE;

  BZLA_MSG(bzla->msg, 1, "calling SAT");
  configure_sat_mgr(bzla);

  if (bzla->valid_assignments == 1) bzla_reset_incremental_usage(bzla);

  bzla_add_again_assumptions(bzla);

  assert(bzla->synthesized_constraints->count == 0);
  assert(bzla->unsynthesized_constraints->count == 0);
  assert(bzla->embedded_constraints->count == 0);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_assumptions_simp_free(bzla));

  result = timed_sat_sat(bzla, -1);

  assert(result == BZLA_RESULT_UNSAT
         || (bzla_terminate(bzla) && result == BZLA_RESULT_UNKNOWN));

DONE:
  result                  = BZLA_RESULT_UNSAT;
  bzla->valid_assignments = 1;

  bzla->last_sat_result = result;
  return result;
}

static void
collect_applies(Bzla *bzla,
                Bzla *clone,
                BzlaNodeMap *key_map,
                BzlaNodeMap *assumptions,
                BzlaIntHashTable *top_applies,
                BzlaNodePtrStack *top_applies_feq)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(clone);
  assert(key_map);
  assert(assumptions);
  assert(top_applies);
  assert(top_applies_feq);

  double start;
  uint32_t i;
  BzlaMemMgr *mm;
  BzlaFunSolver *slv;
  BzlaNode *cur_bzla, *cur_clone, *bv_eq;
  BzlaNodePtrStack failed_eqs;
  BzlaNodeMapIterator it;
  BzlaIntHashTable *mark;

  start = bzla_util_time_stamp();

  mm   = bzla->mm;
  slv  = BZLA_FUN_SOLVER(bzla);
  mark = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, failed_eqs);

  bzla_iter_nodemap_init(&it, assumptions);
  while (bzla_iter_nodemap_has_next(&it))
  {
    bv_eq     = bzla_iter_nodemap_next(&it);
    cur_clone = bzla_nodemap_mapped(assumptions, bv_eq);
    assert(cur_clone);
    /* Note: node mapping is normalized, revert */
    if (bzla_node_is_inverted(cur_clone))
    {
      bv_eq     = bzla_node_invert(bv_eq);
      cur_clone = bzla_node_invert(cur_clone);
    }
    cur_bzla = bzla_nodemap_mapped(key_map, cur_clone);
    assert(cur_bzla);
    assert(bzla_node_is_regular(cur_bzla));
    assert(bzla_node_is_bv_var(cur_bzla) || bzla_node_is_apply(cur_bzla)
           || bzla_node_is_fun_eq(cur_bzla));

    if (bzla_node_is_bv_var(cur_bzla))
      slv->stats.dp_assumed_vars += 1;
    else if (bzla_node_is_fun_eq(cur_bzla))
      slv->stats.dp_assumed_eqs += 1;
    else
    {
      assert(bzla_node_is_apply(cur_bzla));
      slv->stats.dp_assumed_applies += 1;
    }

    if (bzla_failed_exp(clone, bv_eq))
    {
      BZLALOG(1, "failed: %s", bzla_util_node2string(cur_bzla));
      if (bzla_node_is_bv_var(cur_bzla))
        slv->stats.dp_failed_vars += 1;
      else if (bzla_node_is_fun_eq(cur_bzla))
      {
        slv->stats.dp_failed_eqs += 1;
        BZLA_PUSH_STACK(failed_eqs, cur_bzla);
      }
      else
      {
        assert(bzla_node_is_apply(cur_bzla));
        if (bzla_hashint_table_contains(mark, cur_bzla->id)) continue;
        slv->stats.dp_failed_applies += 1;
        bzla_hashint_table_add(mark, cur_bzla->id);
        bzla_hashint_table_add(top_applies, cur_bzla->id);
      }
    }
  }

  bzla_hashint_table_delete(mark);
  mark = bzla_hashint_table_new(mm);

  /* collect applies below failed function equalities */
  while (!BZLA_EMPTY_STACK(failed_eqs))
  {
    cur_bzla = bzla_node_real_addr(BZLA_POP_STACK(failed_eqs));

    if (!cur_bzla->apply_below
        || bzla_hashint_table_contains(mark, cur_bzla->id))
      continue;

    bzla_hashint_table_add(mark, cur_bzla->id);

    /* we only need the "top applies" below a failed function equality */
    if (!cur_bzla->parameterized && bzla_node_is_apply(cur_bzla))
    {
      BZLALOG(1, "apply below eq: %s", bzla_util_node2string(cur_bzla));
      if (!bzla_hashint_table_contains(top_applies, cur_bzla->id))
      {
        BZLA_PUSH_STACK(*top_applies_feq, cur_bzla);
        bzla_hashint_table_add(top_applies, cur_bzla->id);
      }
      continue;
    }

    for (i = 0; i < cur_bzla->arity; i++)
      BZLA_PUSH_STACK(failed_eqs, cur_bzla->e[i]);
  }
  BZLA_RELEASE_STACK(failed_eqs);
  bzla_hashint_table_delete(mark);
  slv->time.search_init_apps_collect_fa += bzla_util_time_stamp() - start;
}

static void
set_up_dual_and_collect(Bzla *bzla,
                        Bzla *clone,
                        BzlaNode *clone_root,
                        BzlaNodeMap *exp_map,
                        BzlaNodePtrStack *inputs,
                        BzlaNodePtrStack *top_applies)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(clone);
  assert(clone_root);
  assert(exp_map);
  assert(inputs);
  assert(top_applies);

  double delta;
  uint32_t i;
  BzlaNode *cur;
  BzlaFunSolver *slv;
  BzlaNodeMap *assumptions, *key_map;
  BzlaNodePtrStack sorted, topapps_feq;
  BzlaIntHashTable *topapps;

  delta = bzla_util_time_stamp();
  slv   = BZLA_FUN_SOLVER(bzla);

  assumptions = bzla_nodemap_new(bzla);
  key_map     = bzla_nodemap_new(bzla);

  BZLA_INIT_STACK(bzla->mm, sorted);
  BZLA_FIT_STACK(sorted, BZLA_COUNT_STACK(*inputs));
  memcpy(sorted.start,
         inputs->start,
         sizeof(BzlaNode *) * BZLA_COUNT_STACK(*inputs));
  sorted.top = sorted.start + BZLA_COUNT_STACK(*inputs);

  BZLA_INIT_STACK(bzla->mm, topapps_feq);
  topapps = bzla_hashint_table_new(bzla->mm);

  /* assume root */
  bzla_assume_exp(clone, bzla_node_invert(clone_root));

  /* assume assignments of bv vars and applies, partial assignments are
   * assumed as partial assignment (as slice on resp. var/apply) */
  switch (bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP_QSORT))
  {
    case BZLA_DP_QSORT_ASC:
      qsort(sorted.start,
            BZLA_COUNT_STACK(sorted),
            sizeof(BzlaNode *),
            bzla_node_compare_by_id_qsort_asc);
      break;
    case BZLA_DP_QSORT_DESC:
      qsort(sorted.start,
            BZLA_COUNT_STACK(sorted),
            sizeof(BzlaNode *),
            bzla_node_compare_by_id_qsort_desc);
      break;
    default:
      assert(bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP_QSORT)
             == BZLA_DP_QSORT_JUST);
      bzla_dcr_compute_scores_dual_prop(bzla);
      qsort(sorted.start,
            BZLA_COUNT_STACK(sorted),
            sizeof(BzlaNode *),
            bzla_dcr_compare_scores_qsort);
  }
  assume_inputs(bzla, clone, &sorted, exp_map, key_map, assumptions);
  slv->time.search_init_apps_collect_var_apps += bzla_util_time_stamp() - delta;

  /* let solver determine failed assumptions */
  delta = bzla_util_time_stamp();
  sat_aux_bzla_dual_prop(clone);
  assert(clone->last_sat_result == BZLA_RESULT_UNSAT);
  slv->time.search_init_apps_sat += bzla_util_time_stamp() - delta;

  /* extract partial model via failed assumptions */
  collect_applies(bzla, clone, key_map, assumptions, topapps, &topapps_feq);

  for (i = 0; i < BZLA_COUNT_STACK(*inputs); i++)
  {
    cur = BZLA_PEEK_STACK(*inputs, i);
    if (bzla_hashint_table_contains(topapps, bzla_node_real_addr(cur)->id))
      BZLA_PUSH_STACK(*top_applies, cur);
  }
  for (i = 0; i < BZLA_COUNT_STACK(topapps_feq); i++)
    BZLA_PUSH_STACK(*top_applies, BZLA_PEEK_STACK(topapps_feq, i));

  BZLA_RELEASE_STACK(sorted);
  BZLA_RELEASE_STACK(topapps_feq);
  bzla_hashint_table_delete(topapps);
  bzla_nodemap_delete(assumptions);
  bzla_nodemap_delete(key_map);
}

static void
search_initial_applies_dual_prop(Bzla *bzla,
                                 Bzla *clone,
                                 BzlaNode *clone_root,
                                 BzlaNodeMap *exp_map,
                                 BzlaNodePtrStack *top_applies)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(clone);
  assert(clone_root);
  assert(exp_map);
  assert(top_applies);

  double start;
  uint32_t i;
  BzlaNode *cur;
  BzlaNodePtrStack stack, inputs;
  BzlaPtrHashTableIterator it;
  BzlaSATMgr *smgr;
  BzlaFunSolver *slv;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;

  start = bzla_util_time_stamp();

  BZLALOG(1, "");
  BZLALOG(1, "*** search initial applies");

  mm                            = bzla->mm;
  slv                           = BZLA_FUN_SOLVER(bzla);
  slv->stats.dp_failed_vars     = 0;
  slv->stats.dp_assumed_vars    = 0;
  slv->stats.dp_failed_applies  = 0;
  slv->stats.dp_assumed_applies = 0;

  smgr = bzla_get_sat_mgr(bzla);
  if (!smgr->inc_required) return;

  mark = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, inputs);

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
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
      if (bzla_node_is_bv_var(cur) || bzla_node_is_fun_eq(cur)
          || bzla_node_is_apply(cur))
      {
        assert(bzla_node_is_synth(cur));
        BZLA_PUSH_STACK(inputs, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
    }
  }

  (void) bzla_node_compare_by_id_qsort_asc;

  set_up_dual_and_collect(
      bzla, clone, clone_root, exp_map, &inputs, top_applies);

  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(inputs);
  bzla_hashint_table_delete(mark);

  slv->time.search_init_apps += bzla_util_time_stamp() - start;
}

static void
add_lemma_to_dual_prop_clone(Bzla *bzla,
                             Bzla *clone,
                             BzlaNode **root,
                             BzlaNode *lemma,
                             BzlaNodeMap *exp_map)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(clone);
  assert(lemma);

  BzlaNode *clemma, *and;

  /* clone and rebuild lemma with rewrite level 0 (as we want the exact
   * expression) */
  clemma = bzla_clone_recursively_rebuild_exp(bzla, clone, lemma, exp_map, 0);
  assert(clemma);
  and = bzla_exp_bv_and(clone, *root, clemma);
  bzla_node_release(clone, clemma);
  bzla_node_release(clone, *root);
  *root = and;
}

/*------------------------------------------------------------------------*/

static void
search_initial_applies_bv_skeleton(BzlaFunSolver *slv,
                                   BzlaNodePtrStack *applies,
                                   BzlaIntHashTable *cache)
{
  assert(slv);
  assert(applies);

  double start;
  uint32_t i;
  BzlaNode *cur;
  BzlaNodePtrStack stack;
  BzlaMemMgr *mm;
  Bzla *bzla = slv->bzla;

  start = bzla_util_time_stamp();

  BZLALOG(1, "");
  BZLALOG(1, "*** search initial applies");

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, stack);

  for (size_t j = 0; j < BZLA_COUNT_STACK(slv->constraints); ++j)
  {
    cur = BZLA_PEEK_STACK(slv->constraints, j);
    BZLA_PUSH_STACK(stack, cur);

    while (!BZLA_EMPTY_STACK(stack))
    {
      cur = BZLA_POP_STACK(stack);
      assert(!bzla_node_is_simplified(cur)
             || bzla_opt_get(bzla, BZLA_OPT_NONDESTR_SUBST));
      cur = bzla_node_real_addr(bzla_node_get_simplified(bzla, cur));

      if (bzla_hashint_table_contains(cache, cur->id)) continue;

      bzla_hashint_table_add(cache, cur->id);

      if (bzla_node_is_quantifier(cur)) continue;

      if (bzla_node_is_apply(cur) && !cur->parameterized)
      {
        //	      assert (bzla_node_is_synth (cur));
        BZLALOG(1, "initial apply: %s", bzla_util_node2string(cur));
        BZLA_PUSH_STACK(*applies, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
    }
    bzla_node_release(bzla, BZLA_PEEK_STACK(slv->constraints, j));
  }
  BZLA_RESET_STACK(slv->constraints);
  BZLA_RELEASE_STACK(stack);

  /* The UFs introduced while word-blasting min/max/to_sbv/to_ubv FP terms do
   * not occur in any formula reachable from the root constraints since they
   * only encode undefined values. However, for these UFs we still have to
   * check the consistency of the corresponding function applications.
   */
  BzlaNode *uf;
  BzlaNodePtrStack ufs;
  BZLA_INIT_STACK(bzla->mm, ufs);
  bzla_fp_word_blaster_get_introduced_ufs(bzla, &ufs);
  BzlaNodeIterator it;
  for (size_t i = 0; i < BZLA_COUNT_STACK(ufs); ++i)
  {
    uf = BZLA_PEEK_STACK(ufs, i);

    bzla_iter_parent_init(&it, uf);
    while (bzla_iter_parent_has_next(&it))
    {
      cur = bzla_iter_parent_next(&it);
      BZLALOG(1, "initial apply: %s", bzla_util_node2string(cur));
      BZLA_PUSH_STACK(*applies, cur);
    }
  }
  BZLA_RELEASE_STACK(ufs);

  BZLA_FUN_SOLVER(bzla)->time.search_init_apps +=
      bzla_util_time_stamp() - start;
}

static void
search_initial_applies_just(Bzla *bzla, BzlaNodePtrStack *top_applies)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(top_applies);
  assert(bzla->unsynthesized_constraints->count == 0);

  uint32_t i, h;
  int32_t a, a0, a1;
  double start;
  BzlaNode *cur, *e0, *e1;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack stack;
  BzlaAIGMgr *amgr;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;

  start = bzla_util_time_stamp();

  BZLALOG(1, "");
  BZLALOG(1, "*** search initial applies");

  mm   = bzla->mm;
  amgr = bzla_get_aig_mgr(bzla);
  h    = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);
  mark = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, stack);

  bzla_dcr_compute_scores(bzla);

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
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

      if (bzla_node_is_apply(cur) && !cur->parameterized)
      {
        BZLALOG(1, "initial apply: %s", bzla_util_node2string(cur));
        BZLA_PUSH_STACK(*top_applies, cur);
        continue;
      }

      if (!cur->parameterized && !bzla_node_is_fun(cur)
          && !bzla_node_is_args(cur) && bzla_node_bv_get_width(bzla, cur) == 1)
      {
        switch (cur->kind)
        {
          case BZLA_FUN_EQ_NODE:
            a = bzla_node_is_synth(cur)
                    ? bzla_aig_get_assignment(amgr, cur->av->aigs[0])
                    : 0;  // 'x';

            if (a == 1 || a == 0) goto PUSH_CHILDREN;
            /* if equality is false (-1), we do not need to check
             * applies below for consistency as it is sufficient to
             * check the witnesses of inequality */
            break;

          case BZLA_BV_AND_NODE:

            a = bzla_node_is_synth(cur)
                    ? bzla_aig_get_assignment(amgr, cur->av->aigs[0])
                    : 0;  // 'x'

            e0 = bzla_node_real_addr(cur->e[0]);
            e1 = bzla_node_real_addr(cur->e[1]);

            a0 = bzla_node_is_synth(e0)
                     ? bzla_aig_get_assignment(amgr, e0->av->aigs[0])
                     : 0;  // 'x'
            if (a0 && bzla_node_is_inverted(cur->e[0])) a0 *= -1;

            a1 = bzla_node_is_synth(e1)
                     ? bzla_aig_get_assignment(amgr, e1->av->aigs[0])
                     : 0;  // 'x'
            if (a1 && bzla_node_is_inverted(cur->e[1])) a1 *= -1;

            if (a != -1)  // and = 1 or x
            {
              BZLA_PUSH_STACK(stack, cur->e[0]);
              BZLA_PUSH_STACK(stack, cur->e[1]);
            }
            else  // and = 0
            {
              if (a0 == -1 && a1 == -1)  // both inputs 0
              {
                /* branch selection w.r.t selected heuristic */
                if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP
                    || h == BZLA_JUST_HEUR_BRANCH_MIN_DEP)
                {
                  if (bzla_dcr_compare_scores(bzla, cur->e[0], cur->e[1]))
                    BZLA_PUSH_STACK(stack, cur->e[0]);
                  else
                    BZLA_PUSH_STACK(stack, cur->e[1]);
                }
                else
                {
                  assert(h == BZLA_JUST_HEUR_BRANCH_LEFT);
                  BZLA_PUSH_STACK(stack, cur->e[0]);
                }
              }
              else if (a0 == -1)  // only one input 0
                BZLA_PUSH_STACK(stack, cur->e[0]);
              else if (a1 == -1)  // only one input 0
                BZLA_PUSH_STACK(stack, cur->e[1]);
              else if (a0 == 0 && a1 == 1)  // first input x, second 0
                BZLA_PUSH_STACK(stack, cur->e[0]);
              else if (a0 == 1 && a1 == 0)  // first input 0, second x
                BZLA_PUSH_STACK(stack, cur->e[1]);
              else  // both inputs x
              {
                assert(a0 == 0);
                assert(a1 == 0);
                BZLA_PUSH_STACK(stack, cur->e[0]);
                BZLA_PUSH_STACK(stack, cur->e[1]);
              }
            }
            break;

#if 0
		  case BZLA_BCOND_NODE:
		    BZLA_PUSH_STACK (stack, cur->e[0]);
		    a = bzla_node_is_synth (bzla_node_real_addr (cur->e[0]))
			? bzla_aig_get_assignment (
			    amgr, bzla_node_real_addr (cur->e[0])->av->aigs[0])
			: 0;  // 'x';
		    if (bzla_node_is_inverted (cur->e[0])) a *= -1;
		    if (a == 1)  // then
		      BZLA_PUSH_STACK (stack, cur->e[1]);
		    else if (a == -1)
		      BZLA_PUSH_STACK (stack, cur->e[2]);
		    else                   // else
		      {
			BZLA_PUSH_STACK (stack, cur->e[1]);
			BZLA_PUSH_STACK (stack, cur->e[2]);
		      }
		    break;
#endif

          default: goto PUSH_CHILDREN;
        }
      }
      else
      {
      PUSH_CHILDREN:
        for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
      }
    }
  }

  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(mark);

  BZLA_FUN_SOLVER(bzla)->time.search_init_apps +=
      bzla_util_time_stamp() - start;
}

static bool
equal_bv_assignments(BzlaNode *exp0, BzlaNode *exp1)
{
  assert(!bzla_node_is_proxy(exp0));
  assert(!bzla_node_is_proxy(exp1));

  bool equal;
  Bzla *bzla;
  BzlaBitVector *bv0, *bv1;

  bzla  = bzla_node_real_addr(exp0)->bzla;
  bv0   = get_bv_assignment(bzla, exp0);
  bv1   = get_bv_assignment(bzla, exp1);
  equal = bzla_bv_compare(bv0, bv1) == 0;
  bzla_bv_free(bzla->mm, bv0);
  bzla_bv_free(bzla->mm, bv1);
  return equal;
}

static int32_t
compare_args_assignments(BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));
  assert(bzla_node_is_args(e0));
  assert(bzla_node_is_args(e1));
  assert(!bzla_node_is_proxy(e0));
  assert(!bzla_node_is_proxy(e1));

  bool equal;
  BzlaBitVector *bv0, *bv1;
  BzlaNode *arg0, *arg1;
  Bzla *bzla;
  BzlaArgsIterator it0, it1;
  bzla = e0->bzla;

  if (bzla_node_get_sort_id(e0) != bzla_node_get_sort_id(e1)) return 1;

  if (e0 == e1) return 0;
  bzla_iter_args_init(&it0, e0);
  bzla_iter_args_init(&it1, e1);

  while (bzla_iter_args_has_next(&it0))
  {
    assert(bzla_iter_args_has_next(&it1));
    arg0 = bzla_iter_args_next(&it0);
    arg1 = bzla_iter_args_next(&it1);

    bv0 = get_bv_assignment(bzla, arg0);
    bv1 = get_bv_assignment(bzla, arg1);

    equal = bzla_bv_compare(bv0, bv1) == 0;
    bzla_bv_free(bzla->mm, bv0);
    bzla_bv_free(bzla->mm, bv1);

    if (!equal) return 1;
  }

  return 0;
}

static uint32_t
hash_args_assignment(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_args(exp));

  uint32_t hash;
  Bzla *bzla;
  BzlaNode *arg;
  BzlaArgsIterator it;
  BzlaBitVector *bv;

  bzla = exp->bzla;
  hash = 0;
  bzla_iter_args_init(&it, exp);
  while (bzla_iter_args_has_next(&it))
  {
    arg = bzla_iter_args_next(&it);
    bv  = get_bv_assignment(bzla, arg);
    hash += bzla_bv_hash(bv);
    bzla_bv_free(bzla->mm, bv);
  }
  return hash;
}

static void
collect_premisses(Bzla *bzla,
                  BzlaNode *from,
                  BzlaNode *to,
                  BzlaNode *args,
                  BzlaNodePtrStack *prem,
                  BzlaIntHashTable *cache)
{
  assert(bzla);
  assert(from);
  assert(to);
  assert(prem);
  assert(cache);
  assert(bzla_node_is_regular(from));
  assert(bzla_node_is_regular(args));
  assert(bzla_node_is_args(args));
  assert(bzla_node_is_regular(to));

  BZLALOG(1,
          "%s: %s, %s, %s",
          __FUNCTION__,
          bzla_util_node2string(from),
          bzla_util_node2string(to),
          bzla_util_node2string(args));

  BzlaMemMgr *mm;
  BzlaNode *cur, *result, *tmp;
  BzlaBitVector *bv_assignment;

  mm = bzla->mm;

  /* follow propagation path and collect all conditions that have been
   * evaluated during propagation */
  if (bzla_node_is_apply(from))
  {
    assert(bzla_node_is_regular(to));
    assert(bzla_node_is_fun(to));
    assert(!bzla_node_is_simplified(from->e[0])
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));

    cur = bzla_node_get_simplified(bzla, from->e[0]);

    for (;;)
    {
      assert(bzla_node_is_regular(cur));
      assert(bzla_node_is_fun(cur));
      assert(!bzla_node_is_simplified(cur));

      if (cur == to) break;

      if (bzla_node_is_fun_cond(cur))
      {
        bv_assignment = get_bv_assignment(bzla, cur->e[0]);

        /* propagate over function ite */
        if (bzla_bv_is_true(bv_assignment))
        {
          tmp = cur->e[0];
          cur = cur->e[1];
        }
        else
        {
          tmp = bzla_node_invert(cur->e[0]);
          cur = cur->e[2];
        }
        if (!bzla_hashint_table_contains(cache, bzla_node_get_id(tmp)))
          BZLA_PUSH_STACK(*prem, bzla_node_copy(bzla, tmp));
        bzla_bv_free(mm, bv_assignment);
        continue;
      }
      else if (bzla_node_is_update(cur))
      {
        tmp = cur->e[1];
        assert(compare_args_assignments(tmp, from->e[1]) != 0);
        if (!bzla_hashint_table_contains(cache, bzla_node_get_id(tmp)))
          BZLA_PUSH_STACK(*prem, bzla_node_copy(bzla, tmp));
        cur = cur->e[0];
      }
      else
      {
        assert(bzla_node_is_lambda(cur));

        bzla_beta_assign_args(bzla, cur, args);
        result = bzla_beta_reduce_partial_collect_new(bzla, cur, prem, cache);
        bzla_beta_unassign_params(bzla, cur);
        result = bzla_node_real_addr(result);

        assert(bzla_node_is_apply(result));
        assert(result->e[1] == args);

        cur = result->e[0];
        bzla_node_release(bzla, result);
      }
    }
  }
  else
  {
    // TODO: merge with above lambda case?
    assert(bzla_node_is_lambda(from));
    cur = from;

    bzla_beta_assign_args(bzla, cur, args);
    result = bzla_beta_reduce_partial_collect_new(bzla, cur, prem, cache);
    bzla_beta_unassign_params(bzla, cur);
    assert(bzla_node_real_addr(result) == to);
    bzla_node_release(bzla, result);
  }
}

static BzlaNode *
mk_equal_args(Bzla *bzla, BzlaNode *args1, BzlaNode *args2)
{
  BzlaNode *arg1, *arg2, *eq, *tmp, *res = 0;
  BzlaArgsIterator it1, it2;

  bzla_iter_args_init(&it1, args1);
  bzla_iter_args_init(&it2, args2);
  while (bzla_iter_args_has_next(&it1))
  {
    assert(bzla_iter_args_has_next(&it2));
    arg1 = bzla_iter_args_next(&it1);
    arg2 = bzla_iter_args_next(&it2);

    eq = bzla_exp_eq(bzla, arg1, arg2);
    if (res)
    {
      tmp = bzla_exp_bv_and(bzla, res, eq);
      bzla_node_release(bzla, res);
      bzla_node_release(bzla, eq);
      res = tmp;
    }
    else
      res = eq;
  }
  assert(!bzla_iter_args_has_next(&it2));
  return res;
}

static BzlaNode *
mk_premise(Bzla *bzla, BzlaNode *args, BzlaNode *prem[], uint32_t num_prem)
{
  uint32_t i;
  BzlaNode *cur, *res = 0, *tmp, *p;

  for (i = 0; i < num_prem; i++)
  {
    cur = prem[i];

    if (bzla_node_is_args(cur))
      p = bzla_node_invert(mk_equal_args(bzla, args, cur));
    else
      p = bzla_node_copy(bzla, cur);

    if (res)
    {
      tmp = bzla_exp_bv_and(bzla, res, p);
      bzla_node_release(bzla, res);
      bzla_node_release(bzla, p);
      res = tmp;
    }
    else
      res = p;
  }
  return res;
}

static void
add_lemma(Bzla *bzla, BzlaNode *fun, BzlaNode *app1, BzlaNode *app2)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(fun);
  assert(bzla_node_is_regular(fun));
  assert(bzla_node_is_fun(fun));
  assert(!fun->parameterized);
  assert(app1);
  assert(bzla_node_is_regular(app1));
  assert(bzla_node_is_apply(app1));
  assert(!app2 || bzla_node_is_regular(app2) || bzla_node_is_apply(app2));

  double start;
  uint32_t i, lemma_size = 1;
  BzlaIntHashTable *cache_app1, *cache_app2;
  BzlaNodePtrStack prem_app1, prem_app2, prem;
  BzlaNode *value, *tmp, *and, *con, *lemma;
  BzlaMemMgr *mm;
  BzlaFunSolver *slv;

  start      = bzla_util_time_stamp();
  mm         = bzla->mm;
  slv        = BZLA_FUN_SOLVER(bzla);
  cache_app1 = bzla_hashint_table_new(mm);
  cache_app2 = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, prem_app1);
  BZLA_INIT_STACK(mm, prem_app2);
  BZLA_INIT_STACK(mm, prem);

  /* collect premise and conclusion */

  collect_premisses(bzla, app1, fun, app1->e[1], &prem_app1, cache_app1);
  tmp = mk_premise(
      bzla, app1->e[1], prem_app1.start, BZLA_COUNT_STACK(prem_app1));

  BZLA_PUSH_STACK_IF(tmp != 0, prem, tmp);
  lemma_size += BZLA_COUNT_STACK(prem_app1);

  if (app2) /* function congruence axiom conflict */
  {
    collect_premisses(bzla, app2, fun, app2->e[1], &prem_app2, cache_app2);
    tmp = mk_premise(
        bzla, app2->e[1], prem_app2.start, BZLA_COUNT_STACK(prem_app2));

    BZLA_PUSH_STACK_IF(tmp != 0, prem, tmp);
    BZLA_PUSH_STACK(prem, mk_equal_args(bzla, app1->e[1], app2->e[1]));
    lemma_size += BZLA_COUNT_STACK(prem_app2);
    con = bzla_exp_eq(bzla, app1, app2);
  }
  else if (bzla_node_is_update(fun)) /* read over write conflict */
  {
    BZLA_PUSH_STACK(prem, mk_equal_args(bzla, app1->e[1], fun->e[1]));
    lemma_size += bzla_node_args_get_arity(bzla, app1->e[1]);
    con = bzla_exp_eq(bzla, app1, fun->e[2]);
  }
  else /* beta reduction conflict */
  {
    assert(bzla_node_is_lambda(fun));

    bzla_beta_assign_args(bzla, fun, app1->e[1]);
    value = bzla_beta_reduce_partial(bzla, fun, 0);
    bzla_beta_unassign_params(bzla, fun);
    assert(!bzla_node_is_lambda(value));

    /* path from conflicting fun to value */
    collect_premisses(bzla,
                      fun,
                      bzla_node_real_addr(value),
                      app1->e[1],
                      &prem_app2,
                      cache_app2);

    tmp = mk_premise(
        bzla, app1->e[1], prem_app2.start, BZLA_COUNT_STACK(prem_app2));

    BZLA_PUSH_STACK_IF(tmp != 0, prem, tmp);
    lemma_size += BZLA_COUNT_STACK(prem_app2);
    con = bzla_exp_eq(bzla, app1, value);
    bzla_node_release(bzla, value);
  }

  /* create lemma */
  if (BZLA_EMPTY_STACK(prem))
    lemma = con;
  else
  {
    and   = bzla_exp_bv_and_n(bzla, prem.start, BZLA_COUNT_STACK(prem));
    lemma = bzla_exp_implies(bzla, and, con);
    bzla_node_release(bzla, and);
    bzla_node_release(bzla, con);
  }

  assert(lemma != bzla->true_exp);
  if (!bzla_hashptr_table_get(slv->lemmas, lemma))
  {
    bzla_hashptr_table_add(slv->lemmas, bzla_node_copy(bzla, lemma));
    BZLA_PUSH_STACK(slv->cur_lemmas, lemma);
    slv->stats.lod_refinements++;
    slv->stats.lemmas_size_sum += lemma_size;
    if (lemma_size >= BZLA_SIZE_STACK(slv->stats.lemmas_size))
      BZLA_FIT_STACK(slv->stats.lemmas_size, lemma_size);
    slv->stats.lemmas_size.start[lemma_size] += 1;
  }
  bzla_node_release(bzla, lemma);

  /* cleanup */
  for (i = 0; i < BZLA_COUNT_STACK(prem); i++)
    bzla_node_release(bzla, BZLA_PEEK_STACK(prem, i));
  for (i = 0; i < BZLA_COUNT_STACK(prem_app1); i++)
    bzla_node_release(bzla, BZLA_PEEK_STACK(prem_app1, i));
  for (i = 0; i < BZLA_COUNT_STACK(prem_app2); i++)
    bzla_node_release(bzla, BZLA_PEEK_STACK(prem_app2, i));
  BZLA_RELEASE_STACK(prem_app1);
  BZLA_RELEASE_STACK(prem_app2);
  BZLA_RELEASE_STACK(prem);
  bzla_hashint_table_delete(cache_app1);
  bzla_hashint_table_delete(cache_app2);
  BZLA_FUN_SOLVER(bzla)->time.lemma_gen += bzla_util_time_stamp() - start;
}

static void
push_applies_for_propagation(Bzla *bzla,
                             BzlaNode *exp,
                             BzlaNodePtrStack *prop_stack,
                             BzlaIntHashTable *apply_search_cache)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(exp);
  assert(prop_stack);

  uint32_t i;
  double start;
  BzlaFunSolver *slv;
  BzlaNode *cur;
  BzlaNodePtrStack visit;
  BzlaMemMgr *mm;

  start = bzla_util_time_stamp();
  slv   = BZLA_FUN_SOLVER(bzla);
  mm    = bzla->mm;

  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, exp);
  do
  {
    cur = BZLA_POP_STACK(visit);
    assert(!bzla_node_is_simplified(cur)
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));

    cur = bzla_node_real_addr(bzla_node_get_simplified(bzla, cur));
    assert(!cur->parameterized);
    assert(!bzla_node_is_fun(cur));

    if (!cur->apply_below
        || bzla_hashint_table_contains(apply_search_cache, cur->id)
        || bzla_node_is_fun_eq(cur) || bzla_node_is_quantifier(cur))
      continue;

    bzla_hashint_table_add(apply_search_cache, cur->id);

    if (bzla_node_is_apply(cur))
    {
      BZLA_PUSH_STACK(*prop_stack, cur);
      BZLA_PUSH_STACK(*prop_stack, cur->e[0]);
      BZLALOG(2, "push apply: %s", bzla_util_node2string(cur));
      continue;
    }

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  } while (!BZLA_EMPTY_STACK(visit));
  BZLA_RELEASE_STACK(visit);
  slv->time.find_prop_app += bzla_util_time_stamp() - start;
}

static bool
find_conflict_app(Bzla *bzla, BzlaNode *app, BzlaIntHashTable *conf_apps)
{
  double start;
  bool res = false;
  uint32_t i;
  BzlaIntHashTable *cache;
  BzlaMemMgr *mm;
  BzlaNodePtrStack visit;
  BzlaNode *cur;

  start = bzla_util_time_stamp();
  mm    = bzla->mm;
  cache = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, app->e[1]);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (!cur->apply_below || bzla_node_is_fun(cur)
        || bzla_hashint_table_contains(cache, cur->id))
      continue;
    bzla_hashint_table_add(cache, cur->id);
    if (bzla_hashint_table_contains(conf_apps, cur->id))
    {
      res = true;
      break;
    }
    if (bzla_node_is_apply(cur)) continue;

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }
  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(visit);
  BZLA_FUN_SOLVER(bzla)->time.find_conf_app += bzla_util_time_stamp() - start;
  return res;
}

static void
propagate(Bzla *bzla,
          BzlaNodePtrStack *prop_stack,
          BzlaPtrHashTable *cleanup_table,
          BzlaIntHashTable *apply_search_cache)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(prop_stack);
  assert(cleanup_table);
  assert(apply_search_cache);

  double start;
  uint32_t opt_eager_lemmas;
  bool prop_down, conflict, restart;
  BzlaBitVector *bv;
  BzlaMemMgr *mm;
  BzlaFunSolver *slv;
  BzlaNode *fun, *app, *args, *fun_value, *cur;
  BzlaNode *hashed_app;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *conds;
  BzlaIntHashTable *conf_apps;

  start            = bzla_util_time_stamp();
  mm               = bzla->mm;
  slv              = BZLA_FUN_SOLVER(bzla);
  conf_apps        = bzla_hashint_table_new(mm);
  opt_eager_lemmas = bzla_opt_get(bzla, BZLA_OPT_FUN_EAGER_LEMMAS);

  BZLALOG(1, "");
  BZLALOG(1, "*** %s", __FUNCTION__);
  while (!BZLA_EMPTY_STACK(*prop_stack))
  {
    fun = bzla_node_get_simplified(bzla, BZLA_POP_STACK(*prop_stack));
    assert(bzla_node_is_regular(fun));
    assert(bzla_node_is_fun(fun));
    assert(!bzla_node_is_simplified(fun));
    assert(!BZLA_EMPTY_STACK(*prop_stack));
    app = BZLA_POP_STACK(*prop_stack);
    assert(bzla_node_is_regular(app));
    assert(bzla_node_is_apply(app));

    conflict = false;
    restart  = true;

    if (app->propagated) continue;

    app->propagated = 1;
    if (!bzla_hashptr_table_get(cleanup_table, app))
      bzla_hashptr_table_add(cleanup_table, app);
    slv->stats.propagations++;

    BZLALOG(1, "propagate");
    BZLALOG(1, "  app: %s", bzla_util_node2string(app));
    BZLALOG(1, "  fun: %s", bzla_util_node2string(fun));

    args = app->e[1];
    assert(bzla_node_is_regular(args));
    assert(bzla_node_is_args(args));
    assert(!bzla_node_is_simplified(args)
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
    args = bzla_node_get_simplified(bzla, args);
    assert(bzla_node_is_args(args));
    assert(bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(fun))
           == bzla_node_get_sort_id(args));

    push_applies_for_propagation(bzla, args, prop_stack, apply_search_cache);

    if (!fun->rho)
    {
      fun->rho = bzla_hashptr_table_new(mm,
                                        (BzlaHashPtr) hash_args_assignment,
                                        (BzlaCmpPtr) compare_args_assignments);
      if (!bzla_hashptr_table_get(cleanup_table, fun))
        bzla_hashptr_table_add(cleanup_table, fun);
    }
    else
    {
      b = bzla_hashptr_table_get(fun->rho, args);
      if (b)
      {
        hashed_app = (BzlaNode *) b->data.as_ptr;
        assert(bzla_node_is_regular(hashed_app));
        assert(bzla_node_is_apply(hashed_app));

        /* function congruence conflict */
        if (!equal_bv_assignments(hashed_app, app))
        {
          BZLALOG(1, "\e[1;31m");
          BZLALOG(1, "FC conflict at: %s", bzla_util_node2string(fun));
          BZLALOG(1, "add_lemma:");
          BZLALOG(1, "  fun: %s", bzla_util_node2string(fun));
          BZLALOG(1, "  app1: %s", bzla_util_node2string(hashed_app));
          BZLALOG(1, "  app2: %s", bzla_util_node2string(app));
          BZLALOG(1, "\e[0;39m");
          if (opt_eager_lemmas == BZLA_FUN_EAGER_LEMMAS_CONF)
          {
            bzla_hashint_table_add(conf_apps, app->id);
            restart = find_conflict_app(bzla, app, conf_apps);
          }
          else if (opt_eager_lemmas == BZLA_FUN_EAGER_LEMMAS_ALL)
            restart = false;
          slv->stats.function_congruence_conflicts++;
          add_lemma(bzla, fun, hashed_app, app);
          // conflict = true;
          /* stop at first conflict */
          if (restart) break;
        }
        continue;
      }
    }
    assert(fun->rho);
    assert(!bzla_hashptr_table_get(fun->rho, args));
    bzla_hashptr_table_add(fun->rho, args)->data.as_ptr = app;
    BZLALOG(1,
            "  save app: %s (%s)",
            bzla_util_node2string(args),
            bzla_util_node2string(app));

    /* skip array vars/uf */
    if (bzla_node_is_uf(fun)) continue;

    if (bzla_node_is_fun_cond(fun))
    {
      push_applies_for_propagation(
          bzla, fun->e[0], prop_stack, apply_search_cache);
      bv = get_bv_assignment(bzla, fun->e[0]);

      /* propagate over function ite */
      BZLALOG(1, "  propagate down: %s", bzla_util_node2string(app));
      app->propagated = 0;
      BZLA_PUSH_STACK(*prop_stack, app);
      if (bzla_bv_is_true(bv))
        BZLA_PUSH_STACK(*prop_stack, fun->e[1]);
      else
        BZLA_PUSH_STACK(*prop_stack, fun->e[2]);
      bzla_bv_free(mm, bv);
      continue;
    }
    else if (bzla_node_is_update(fun))
    {
      if (compare_args_assignments(fun->e[1], args) == 0)
      {
        if (!equal_bv_assignments(app, fun->e[2]))
        {
          BZLALOG(1, "\e[1;31m");
          BZLALOG(1, "update conflict at: %s", bzla_util_node2string(fun));
          BZLALOG(1, "add_lemma:");
          BZLALOG(1, "  fun: %s", bzla_util_node2string(fun));
          BZLALOG(1, "  app: %s", bzla_util_node2string(app));
          BZLALOG(1, "\e[0;39m");
#if 0
		  if (opt_eager_lemmas == BZLA_FUN_EAGER_LEMMAS_CONF)
		    {
		      bzla_hashint_table_add (conf_apps, app->id);
		      restart = find_conflict_app (bzla, app, conf_apps);
		    }
		  else if (opt_eager_lemmas == BZLA_FUN_EAGER_LEMMAS_ALL)
		    restart = false;
#endif

          slv->stats.beta_reduction_conflicts++;
          add_lemma(bzla, fun, app, 0);
          conflict = true;

#if 0
		  /* stop at first conflict */
		  if (restart)
		    break;
#endif
        }
      }
      else
      {
        app->propagated = 0;
        BZLA_PUSH_STACK(*prop_stack, app);
        BZLA_PUSH_STACK(*prop_stack, fun->e[0]);
        slv->stats.propagations_down++;
      }
      push_applies_for_propagation(
          bzla, fun->e[1], prop_stack, apply_search_cache);
      push_applies_for_propagation(
          bzla, fun->e[2], prop_stack, apply_search_cache);
      continue;
    }

    assert(bzla_node_is_lambda(fun));
    conds = bzla_hashptr_table_new(mm,
                                   (BzlaHashPtr) bzla_node_hash_by_id,
                                   (BzlaCmpPtr) bzla_node_compare_by_id);
    bzla_beta_assign_args(bzla, fun, args);
    fun_value = bzla_beta_reduce_partial(bzla, fun, conds);
    assert(!bzla_node_is_fun(fun_value));
    bzla_beta_unassign_params(bzla, fun);

    prop_down = false;
    if (!bzla_node_is_inverted(fun_value) && bzla_node_is_apply(fun_value))
      prop_down = fun_value->e[1] == args;

    if (prop_down)
    {
      assert(bzla_node_is_apply(fun_value));
      BZLA_PUSH_STACK(*prop_stack, app);
      BZLA_PUSH_STACK(*prop_stack, bzla_node_real_addr(fun_value)->e[0]);
      slv->stats.propagations_down++;
      app->propagated = 0;
      BZLALOG(1, "  propagate down: %s", bzla_util_node2string(app));
    }
    else if (!equal_bv_assignments(app, fun_value))
    {
      BZLALOG(1, "\e[1;31m");
      BZLALOG(1, "BR conflict at: %s", bzla_util_node2string(fun));
      BZLALOG(1, "add_lemma:");
      BZLALOG(1, "  fun: %s", bzla_util_node2string(fun));
      BZLALOG(1, "  app: %s", bzla_util_node2string(app));
      BZLALOG(1, "\e[0;39m");
      if (opt_eager_lemmas == BZLA_FUN_EAGER_LEMMAS_CONF)
      {
        bzla_hashint_table_add(conf_apps, app->id);
        restart = find_conflict_app(bzla, app, conf_apps);
      }
      else if (opt_eager_lemmas == BZLA_FUN_EAGER_LEMMAS_ALL)
        restart = false;
      slv->stats.beta_reduction_conflicts++;
      add_lemma(bzla, fun, app, 0);
      conflict = true;
    }

    /* we have a conflict and the values are inconsistent, we do not have
     * to push applies onto 'prop_stack' that produce this inconsistent
     * value */
    if (conflict)
    {
      bzla_iter_hashptr_init(&it, conds);
      while (bzla_iter_hashptr_has_next(&it))
        bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
    }
    /* push applies onto 'prop_stack' that are necesary to derive 'fun_value'
     */
    else
    {
      /* in case of down propagation 'fun_value' is a function application
       * and we can propagate 'app' instead. hence, we to not have to
       * push 'fun_value' onto 'prop_stack'. */
      if (!prop_down)
        push_applies_for_propagation(
            bzla, fun_value, prop_stack, apply_search_cache);

      /* push applies in evaluated conditions */
      bzla_iter_hashptr_init(&it, conds);
      while (bzla_iter_hashptr_has_next(&it))
      {
        cur = bzla_iter_hashptr_next(&it);
        push_applies_for_propagation(bzla, cur, prop_stack, apply_search_cache);
        bzla_node_release(bzla, cur);
      }
    }
    bzla_hashptr_table_delete(conds);
    bzla_node_release(bzla, fun_value);

    /* stop at first conflict */
    if (restart && conflict) break;
  }
  bzla_hashint_table_delete(conf_apps);
  slv->time.prop += bzla_util_time_stamp() - start;
}

/* generate hash table for function 'fun' consisting of all rho and static_rho
 * hash tables. */
static BzlaPtrHashTable *
generate_table(Bzla *bzla, BzlaNode *fun, BzlaNode **base_array)
{
  uint32_t i;
  BzlaMemMgr *mm;
  BzlaNode *cur, *value, *args, *cur_fun;
  BzlaPtrHashTable *table, *rho, *static_rho;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaPtrHashTableIterator it;
  BzlaBitVector *evalbv;

  mm    = bzla->mm;
  table = bzla_hashptr_table_new(mm,
                                 (BzlaHashPtr) hash_args_assignment,
                                 (BzlaCmpPtr) compare_args_assignments);
  cache = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, fun);

  cur_fun = 0;
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)
        || (!bzla_node_is_fun(cur) && !cur->parameterized))
      continue;

    bzla_hashint_table_add(cache, cur->id);

    /* NOTE: all encountered lambda nodes need to be arrays,
     *       in any other case we fully support equality over UFs and
     *       conditionals. */
    if (bzla_node_is_fun(cur))
    {
      rho        = cur->rho;
      static_rho = 0;
      cur_fun    = cur;

      if (bzla_node_is_lambda(cur) && bzla_node_is_array(cur))
      {
        assert(cur->is_array);
        static_rho = bzla_node_lambda_get_static_rho(cur);
        assert(!bzla_node_real_addr(cur->e[1])->parameterized || static_rho);
      }
      else if (bzla_node_is_fun_cond(cur))
      {
        evalbv = get_bv_assignment(bzla, cur->e[0]);
        if (bzla_bv_is_true(evalbv))
          BZLA_PUSH_STACK(visit, cur->e[1]);
        else
          BZLA_PUSH_STACK(visit, cur->e[2]);
        bzla_bv_free(mm, evalbv);
      }
      else if (bzla_node_is_update(cur))
      {
        if (!bzla_hashptr_table_get(table, cur->e[1]))
          bzla_hashptr_table_add(table, cur->e[1])->data.as_ptr = cur->e[2];
        BZLA_PUSH_STACK(visit, cur->e[0]);
      }

      if (rho)
      {
        bzla_iter_hashptr_init(&it, rho);
        if (static_rho) bzla_iter_hashptr_queue(&it, static_rho);
      }
      else if (static_rho)
        bzla_iter_hashptr_init(&it, static_rho);

      if (rho || static_rho)
      {
        while (bzla_iter_hashptr_has_next(&it))
        {
          value = it.bucket->data.as_ptr;
          assert(!bzla_node_is_proxy(value));
          args = bzla_iter_hashptr_next(&it);
          assert(!bzla_node_is_proxy(args));

          if (!bzla_hashptr_table_get(table, args))
            bzla_hashptr_table_add(table, args)->data.as_ptr = value;
        }
      }

      /* child already pushed w.r.t. evaluation of condition */
      if (bzla_node_is_fun_cond(cur)
          || bzla_node_is_update(cur)
          /* do not traverse further down if it's a non-array lambda. */
          || (bzla_node_is_lambda(cur) && !bzla_node_is_array(cur)))
        continue;
    }

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  assert(cur_fun);
  *base_array = cur_fun;

  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);

  return table;
}

static void
add_extensionality_lemmas(Bzla *bzla)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);

  double start, delta;
  bool skip;
  BzlaBitVector *evalbv;
  uint32_t num_lemmas = 0;
  BzlaNode *cur, *cur_args, *app0, *app1, *eq, *con, *value;
  BzlaNode *base0, *base1;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *table0, *table1, *conflicts;
  BzlaPtrHashTableIterator hit;
  BzlaNodePtrStack feqs, const_arrays;
  BzlaMemMgr *mm;
  BzlaPtrHashBucket *b;
  BzlaFunSolver *slv;

  start = bzla_util_time_stamp();

  BZLALOG(1, "");
  BZLALOG(1, "*** %s", __FUNCTION__);

  slv = BZLA_FUN_SOLVER(bzla);
  mm  = bzla->mm;
  BZLA_INIT_STACK(mm, feqs);
  BZLA_INIT_STACK(mm, const_arrays);

  /* collect all reachable function equalities */
  bzla_iter_hashptr_init(&it, bzla->feqs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BZLA_PUSH_STACK(feqs, bzla_iter_hashptr_next(&it));
  }

  BzlaUnionFind *ufind = bzla_ufind_new(bzla->mm);

  while (!BZLA_EMPTY_STACK(feqs))
  {
    cur = bzla_node_get_simplified(bzla, BZLA_POP_STACK(feqs));
    if (!bzla_node_is_fun_eq(cur)) continue;

    evalbv = get_bv_assignment(bzla, cur);
    assert(evalbv);
    skip = bzla_bv_is_false(evalbv);
    bzla_bv_free(bzla->mm, evalbv);

    if (skip) continue;

    base0 = base1 = 0;
    table0        = generate_table(bzla, cur->e[0], &base0);
    table1        = generate_table(bzla, cur->e[1], &base1);

    assert(base0);
    assert(base1);

    bzla_ufind_merge(ufind, base0, base1);
    BZLA_PUSH_STACK_IF(bzla_node_is_const_array(base0), const_arrays, base0);
    BZLA_PUSH_STACK_IF(bzla_node_is_const_array(base1), const_arrays, base1);

    conflicts = bzla_hashptr_table_new(mm,
                                       (BzlaHashPtr) hash_args_assignment,
                                       (BzlaCmpPtr) compare_args_assignments);

    bzla_iter_hashptr_init(&hit, table0);
    while (bzla_iter_hashptr_has_next(&hit))
    {
      value    = hit.bucket->data.as_ptr;
      cur_args = bzla_iter_hashptr_next(&hit);
      b        = bzla_hashptr_table_get(table1, cur_args);

      if (bzla_hashptr_table_get(conflicts, cur_args)) continue;

      if (!b || !equal_bv_assignments(value, b->data.as_ptr))
        bzla_hashptr_table_add(conflicts, cur_args);
    }

    bzla_iter_hashptr_init(&hit, table1);
    while (bzla_iter_hashptr_has_next(&hit))
    {
      value    = hit.bucket->data.as_ptr;
      cur_args = bzla_iter_hashptr_next(&hit);
      b        = bzla_hashptr_table_get(table0, cur_args);

      if (bzla_hashptr_table_get(conflicts, cur_args)) continue;

      if (!b || !equal_bv_assignments(value, b->data.as_ptr))
        bzla_hashptr_table_add(conflicts, cur_args);
    }

    BZLALOG(1, "  %s", bzla_util_node2string(cur));
    bzla_iter_hashptr_init(&hit, conflicts);
    while (bzla_iter_hashptr_has_next(&hit))
    {
      cur_args = bzla_iter_hashptr_next(&hit);
      app0     = bzla_exp_apply(bzla, cur->e[0], cur_args);
      app1     = bzla_exp_apply(bzla, cur->e[1], cur_args);
      eq       = bzla_exp_eq(bzla, app0, app1);
      con      = bzla_exp_implies(bzla, cur, eq);

      /* add instantiation of extensionality lemma */
      if (!bzla_hashptr_table_get(slv->lemmas, con))
      {
        bzla_hashptr_table_add(slv->lemmas, bzla_node_copy(bzla, con));
        BZLA_PUSH_STACK(slv->cur_lemmas, con);
        slv->stats.extensionality_lemmas++;
        slv->stats.lod_refinements++;
        num_lemmas++;
        BZLALOG(1,
                "    %s, %s",
                bzla_util_node2string(app0),
                bzla_util_node2string(app1));
      }
      bzla_node_release(bzla, app0);
      bzla_node_release(bzla, app1);
      bzla_node_release(bzla, eq);
      bzla_node_release(bzla, con);
    }
    bzla_hashptr_table_delete(conflicts);
    bzla_hashptr_table_delete(table0);
    bzla_hashptr_table_delete(table1);
  }
  BZLA_RELEASE_STACK(feqs);

  /* No conflicts found. Check if we have positive (chains of) equalities over
   * constant arrays. */
  if (num_lemmas == 0)
  {
    int32_t id;
    BzlaIntHashTable *cache = bzla_hashint_map_new(bzla->mm);
    BzlaNode *ca;
    BzlaHashTableData *d;
    BzlaBitVector *bv0, *bv1;
    for (size_t i = 0; i < BZLA_COUNT_STACK(const_arrays); i++)
    {
      ca = BZLA_PEEK_STACK(const_arrays, i);
      id = bzla_node_get_id(bzla_ufind_get_repr(ufind, ca));
      assert(id > 0);

      if ((d = bzla_hashint_map_get(cache, id)))
      {
        bv0 = get_bv_assignment(bzla, ca->e[1]);
        bv1 = get_bv_assignment(bzla, ((BzlaNode *) d->as_ptr)->e[1]);
        BZLALOG(1,
                "found equality over constant array: %s and %s\n",
                bzla_util_node2string(d->as_ptr),
                bzla_util_node2string(ca));
        BZLA_ABORT(bzla_bv_compare(bv0, bv1),
                   "Found positive equality over two constant arrays, "
                   "which is currently not supported.");
        bzla_bv_free(mm, bv0);
        bzla_bv_free(mm, bv1);
      }
      else
      {
        bzla_hashint_map_add(cache, id)->as_ptr = ca;
      }
    }
    bzla_hashint_map_delete(cache);
  }

  BZLA_RELEASE_STACK(const_arrays);

  bzla_ufind_delete(ufind);

  delta = bzla_util_time_stamp() - start;
  BZLALOG(
      1, "  added %u extensionality lemma in %.2f seconds", num_lemmas, delta);
  slv->time.check_extensionality += delta;
}

/* Find and collect all unreachable apply nodes. */
static void
push_unreachable_applies(Bzla *bzla, BzlaNodePtrStack *init_apps)
{
  uint32_t i;
  BzlaNode *cur;
  BzlaIntHashTable *cache;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack visit;

  cache = bzla_hashint_table_new(bzla->mm);

  BZLA_INIT_STACK(bzla->mm, visit);

  /* Cache reachable nodes. */
  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(visit, cur);
    while (!BZLA_EMPTY_STACK(visit))
    {
      cur = bzla_node_real_addr(
          bzla_node_get_simplified(bzla, BZLA_POP_STACK(visit)));
      if (bzla_hashint_table_contains(cache, cur->id)) continue;
      bzla_hashint_table_add(cache, cur->id);
      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
    }
  }
  BZLA_RELEASE_STACK(visit);

  /* Collect unreachable applies. */
  for (size_t i = 1; i < BZLA_COUNT_STACK(bzla->nodes_id_table); i++)
  {
    cur = BZLA_PEEK_STACK(bzla->nodes_id_table, i);
    if (!cur) continue;
    cur = bzla_node_get_simplified(bzla, cur);
    if (cur->parameterized || !bzla_node_is_apply(cur)
        || bzla_hashint_table_contains(cache, cur->id))
      continue;

    BZLALOG(1, "unreachable apply: %s", bzla_util_node2string(cur));
    BZLA_PUSH_STACK(*init_apps, cur);
  }

  bzla_hashint_table_delete(cache);
}

static void
check_and_resolve_conflicts(Bzla *bzla,
                            Bzla *clone,
                            BzlaNode *clone_root,
                            BzlaNodeMap *exp_map,
                            BzlaNodePtrStack *init_apps,
                            BzlaIntHashTable *init_apps_cache)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);

  double start, start_cleanup;
  bool found_conflicts;
  int32_t i;
  BzlaMemMgr *mm;
  BzlaFunSolver *slv;
  BzlaNode *app, *cur;
  BzlaNodePtrStack prop_stack;
  BzlaNodePtrStack top_applies;
  BzlaPtrHashTable *cleanup_table;
  BzlaIntHashTable *apply_search_cache;
  BzlaPtrHashTableIterator pit;
  BzlaIntHashTableIterator iit;

  start           = bzla_util_time_stamp();
  found_conflicts = false;
  mm              = bzla->mm;
  slv             = BZLA_FUN_SOLVER(bzla);
  cleanup_table   = bzla_hashptr_table_new(mm,
                                         (BzlaHashPtr) bzla_node_hash_by_id,
                                         (BzlaCmpPtr) bzla_node_compare_by_id);

  BZLA_INIT_STACK(mm, prop_stack);
  BZLA_INIT_STACK(mm, top_applies);
  apply_search_cache = bzla_hashint_table_new(mm);

  /* NOTE: if terms containing applies do not occur in the formula anymore due
   * to variable substitution, we still need to ensure that the assignment
   * computed for the substituted variable is correct. hence, we need to check
   * the applies for consistency and push them onto the propagation stack.
   * this also applies for don't care reasoning.
   */
  bzla_iter_hashptr_init(&pit, bzla->inputs);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    cur = bzla_simplify_exp(bzla, bzla_iter_hashptr_next(&pit));
    /* no parents -> is not reachable from the roots */
    if (bzla_node_real_addr(cur)->parents > 0 || bzla_node_is_fun(cur))
      continue;
    push_applies_for_propagation(bzla, cur, &prop_stack, apply_search_cache);
  }

  if (clone)
  {
    search_initial_applies_dual_prop(
        bzla, clone, clone_root, exp_map, &top_applies);
    init_apps = &top_applies;
  }
  else if (bzla_opt_get(bzla, BZLA_OPT_FUN_JUST))
  {
    search_initial_applies_just(bzla, &top_applies);
    init_apps = &top_applies;
  }
  else
    search_initial_applies_bv_skeleton(slv, init_apps, init_apps_cache);

  /* For non-extensional problems, our model generation is able to compute
   * values for applies that are not reachable from assertions. However, for
   * extensional problems this is not sufficient (extensionality axiom not
   * checked). We therefore queue all unreachable applies to make sure that we
   * compute the correct model values.
   */
  if (bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS) == 2 && bzla->feqs->count > 0)
  {
    push_unreachable_applies(bzla, init_apps);
  }

  for (i = BZLA_COUNT_STACK(*init_apps) - 1; i >= 0; i--)
  {
    app = BZLA_PEEK_STACK(*init_apps, i);
    assert(bzla_node_is_regular(app));
    assert(bzla_node_is_apply(app));
    assert(!app->parameterized);
    assert(!app->propagated);
    BZLA_PUSH_STACK(prop_stack, app);
    BZLA_PUSH_STACK(prop_stack, app->e[0]);
    BZLALOG(2, "push apply: %s", bzla_util_node2string(app));
  }

  propagate(bzla, &prop_stack, cleanup_table, apply_search_cache);
  found_conflicts = BZLA_COUNT_STACK(slv->cur_lemmas) > 0;

  /* check consistency of array/uf equalities */
  if (!found_conflicts && bzla->feqs->count > 0)
  {
    assert(BZLA_EMPTY_STACK(prop_stack));
    add_extensionality_lemmas(bzla);
    found_conflicts = BZLA_COUNT_STACK(slv->cur_lemmas) > 0;
  }

  /* applies may have assignments that were not checked for consistency, which
   * is the case when they are not required for deriving SAT (don't care
   * reasoning). hence, we remove those applies from the 'bv_model' as they do
   * not have a valid assignment. an assignment will be generated during
   * model construction */
  if (!found_conflicts)
  {
    bzla_iter_hashint_init(&iit, bzla->bv_model);
    while (bzla_iter_hashint_has_next(&iit))
    {
      cur = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&iit));
      if (bzla_node_is_apply(cur) && !bzla_node_real_addr(cur)->propagated)
        bzla_model_remove_from_bv(bzla, bzla->bv_model, cur);
    }
  }

  start_cleanup = bzla_util_time_stamp();
  bzla_iter_hashptr_init(&pit, cleanup_table);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    cur = bzla_iter_hashptr_next(&pit);
    assert(bzla_node_is_regular(cur));
    if (bzla_node_is_apply(cur))
    {
      /* generate model for apply */
      if (!found_conflicts)
        bzla_bv_free(bzla->mm, get_bv_assignment(bzla, cur));
      cur->propagated = 0;
    }
    else
    {
      assert(bzla_node_is_fun(cur));
      assert(cur->rho);

      if (found_conflicts)
      {
        bzla_hashptr_table_delete(cur->rho);
        cur->rho = 0;
      }
      else
      {
        /* remember functions for incremental usage (and prevent
         * premature release in case that function is released via API
         * call) */
        BZLA_PUSH_STACK(bzla->functions_with_model, bzla_node_copy(bzla, cur));
      }
    }
  }
  slv->time.prop_cleanup += bzla_util_time_stamp() - start_cleanup;
  bzla_hashptr_table_delete(cleanup_table);
  BZLA_RELEASE_STACK(prop_stack);
  BZLA_RELEASE_STACK(top_applies);
  bzla_hashint_table_delete(apply_search_cache);
  slv->time.check_consistency += bzla_util_time_stamp() - start;
}

static void
reset_lemma_cache(BzlaFunSolver *slv)
{
  Bzla *bzla;
  BzlaPtrHashTableIterator it;
  bzla = slv->bzla;
  bzla_iter_hashptr_init(&it, slv->lemmas);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(slv->lemmas);

  slv->lemmas = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
}

static void
mark_cone(Bzla *bzla,
          BzlaNode *node,
          BzlaIntHashTable *cone,
          BzlaIntHashTable *roots,
          BzlaNodePtrStack *false_roots)
{
  assert(bzla_lsutils_is_leaf_node(node));

  BzlaNode *cur;
  BzlaNodeIterator it;
  BzlaNodePtrStack visit;
  BzlaHashTableData *d;

  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_PUSH_STACK(visit, node);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cone, cur->id)) continue;
    bzla_hashint_table_add(cone, cur->id);

    d = bzla_hashint_map_get(roots, cur->id);

    if (d && d->flag)
    {
      BZLA_PUSH_STACK(*false_roots, cur);
    }

    bzla_iter_parent_init(&it, cur);
    while (bzla_iter_parent_has_next(&it))
    {
      BZLA_PUSH_STACK(visit, bzla_iter_parent_next(&it));
    }
  }
  BZLA_RELEASE_STACK(visit);
}

static BzlaSolverResult
check_sat_prels(BzlaFunSolver *slv, BzlaSolver **ls_slv)
{
  assert(slv);

  size_t i;
  double start;
  BzlaSolver *preslv;
  BzlaNodePtrStack assertions, roots_true, roots_false;
  BzlaIntHashTable *visited;
  const BzlaBitVector *bv;
  BzlaNode *root, *cur, *real_cur, *bvconst, *assertion;
  BzlaPtrHashTableIterator it;
  Bzla *bzla;
  BzlaMemMgr *mm;
  BzlaSolverResult result;
  BzlaHashTableData *d;

  bzla = slv->bzla;
  assert(!bzla->inconsistent);
  mm    = bzla->mm;
  start = bzla_util_time_stamp();

  if (!*ls_slv)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_FUN_PREPROP))
    {
      *ls_slv = bzla_new_prop_solver(bzla);
    }
    else
    {
      *ls_slv = bzla_new_sls_solver(bzla);
    }
  }

  assert(*ls_slv);
  preslv    = *ls_slv;
  bzla->slv = preslv;
  result    = preslv->api.sat(preslv);

  /* print prop/sls solver statistics */
  preslv->api.print_stats(preslv);
  preslv->api.print_time_stats(preslv);

  /* reset */
  bzla->slv = (BzlaSolver *) slv;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg,
           1,
           "%s engine determined '%s'",
           preslv->kind == BZLA_PROP_SOLVER_KIND ? "PROP" : "SLS",
           result == BZLA_RESULT_SAT
               ? "sat"
               : (result == BZLA_RESULT_UNSAT ? "unsat" : "unknown"));

  /* Use the partial model of the prels engine and determine input assignments
   * that already satisfy constraints and separated from all other unsatisfied
   * constraints. Assert these assignments to the bit-blasting engine. */
  if (result == BZLA_RESULT_UNKNOWN && bzla_opt_get(bzla, BZLA_OPT_LS_SHARE_SAT)
      && !bzla_terminate(bzla)
      /* We support model sharing for QF_BV only. */
      && !bzla_get_sat_mgr(bzla)->inc_required)
  {
    BZLA_INIT_STACK(mm, roots_true);
    BZLA_INIT_STACK(mm, roots_false);

    BZLA_INIT_STACK(mm, assertions);
    bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->assumptions);

    /* Collect all constraints. */
    BzlaIntHashTable *roots = bzla_hashint_map_new(mm);
    while (bzla_iter_hashptr_has_next(&it))
    {
      root = bzla_iter_hashptr_next(&it);
      d    = bzla_hashint_map_add(roots, bzla_node_real_addr(root)->id);
      if (bzla_bv_is_true(bzla_model_get_bv(bzla, root)))
      {
        d->flag = true;
        BZLA_PUSH_STACK(roots_true, root);
      }
      else
      {
        d->flag = false;
        BZLA_PUSH_STACK(roots_false, root);
      }
    }

    /* Traverse each unsatisfied constraint down to the inputs and mark cone of
     * each input in function mark_cone. If a satisfied constraint is in the
     * cone of a traversed input, it is handled as an unsatisfied constraints
     * and therefore pushed onto the roots_false stack and continue. */
    BzlaIntHashTable *cone = bzla_hashint_table_new(mm);
    visited                = bzla_hashint_table_new(mm);
    while (!BZLA_EMPTY_STACK(roots_false))
    {
      real_cur = bzla_node_real_addr(BZLA_POP_STACK(roots_false));
      if (bzla_hashint_table_contains(visited, real_cur->id)) continue;
      bzla_hashint_table_add(visited, real_cur->id);
      if (bzla_lsutils_is_leaf_node(real_cur))
      {
        mark_cone(bzla, real_cur, cone, roots, &roots_false);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BZLA_PUSH_STACK(roots_false, real_cur->e[i]);
        }
      }
    }
    BZLA_RELEASE_STACK(roots_false);

    /* Collect all remaining inputs that are separated from the unsatisfied
     * constraints. */
    while (!BZLA_EMPTY_STACK(roots_true))
    {
      real_cur = bzla_node_real_addr(BZLA_POP_STACK(roots_true));
      if (bzla_hashint_table_contains(cone, real_cur->id)) continue;
      if (bzla_hashint_table_contains(visited, real_cur->id)) continue;
      bzla_hashint_table_add(visited, real_cur->id);

      if (bzla_lsutils_is_leaf_node(real_cur))
      {
        bv        = bzla_model_get_bv(bzla, real_cur);
        bvconst   = bzla_exp_bv_const(bzla, bv);
        assertion = bzla_exp_eq(bzla, real_cur, bvconst);
        bzla_node_release(bzla, bvconst);
        BZLA_PUSH_STACK(assertions, assertion);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BZLA_PUSH_STACK(roots_true, real_cur->e[i]);
        }
      }
    }
    bzla_hashint_table_delete(visited);
    bzla_hashint_table_delete(cone);
    bzla_hashint_map_delete(roots);
    BZLA_RELEASE_STACK(roots_true);

    BZLA_FUN_SOLVER(bzla)->stats.prels_shared = BZLA_COUNT_STACK(assertions);

    BZLA_MSG(bzla->msg,
             1,
             "asserting %u model values",
             BZLA_COUNT_STACK(assertions));

    /* assert model values */
    for (i = 0; i < BZLA_COUNT_STACK(assertions); ++i)
    {
      cur = BZLA_PEEK_STACK(assertions, i);
      bzla_assert_exp(bzla, cur);
      bzla_node_release(bzla, cur);
    }
    BZLA_RELEASE_STACK(assertions);
  }

  slv->time.prels_sat += bzla_util_time_stamp() - start;

  return result;
}

static BzlaSolverResult
sat_fun_solver(BzlaFunSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  uint32_t i;
  bool opt_prels, opt_prop_const_bits;
  BzlaSolverResult result;
  Bzla *bzla, *clone;
  BzlaNode *clone_root, *lemma;
  BzlaNodeMap *exp_map;
  BzlaIntHashTable *init_apps_cache;
  BzlaNodePtrStack init_apps;
  BzlaMemMgr *mm;
  BzlaSolver *ls_slv = 0;

  bzla      = slv->bzla;
  mm        = bzla->mm;
  opt_prels = bzla_opt_get(bzla, BZLA_OPT_FUN_PREPROP)
              || bzla_opt_get(bzla, BZLA_OPT_FUN_PRESLS);
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS) != 0;

  assert(!bzla->inconsistent);

  /* make initial applies in bv skeleton global in order to prevent
   * traversing the whole formula every refinement round */
  BZLA_INIT_STACK(mm, init_apps);
  init_apps_cache = bzla_hashint_table_new(mm);

  clone      = 0;
  clone_root = 0;
  exp_map    = 0;

  configure_sat_mgr(bzla);

  if (bzla_terminate(bzla))
  {
    result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  if (slv->assume_lemmas) reset_lemma_cache(slv);

  if (bzla->feqs->count > 0) add_function_disequality_witnesses(bzla);

  /* initialize dual prop clone */
  if (bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP))
  {
    clone = new_exp_layer_clone_for_dual_prop(bzla, &exp_map, &clone_root);
  }

  BzlaPtrHashTableIterator it;
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BZLA_PUSH_STACK(slv->constraints,
                    bzla_node_copy(bzla, bzla_iter_hashptr_next(&it)));
  }

  while (true)
  {
    result = BZLA_RESULT_UNKNOWN;

    if (bzla_terminate(bzla)
        || (slv->lod_limit > -1
            && slv->stats.lod_refinements >= (uint32_t) slv->lod_limit))
    {
      break;
    }

    if (opt_prels)
    {
      if (opt_prop_const_bits)
      {
        bzla_process_unsynthesized_constraints(bzla);
        if (bzla->found_constraint_false)
        {
          result = BZLA_RESULT_UNSAT;
          break;
        }
        assert(bzla->unsynthesized_constraints->count == 0);
        assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
        assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
      }
      result = check_sat_prels(slv, &ls_slv);
    }

    if (result == BZLA_RESULT_UNKNOWN)
    {
      /* Word-blasting may add new constraints. Make sure that these also get
       * synthesized. */
      bzla_add_again_assumptions(bzla);

      bzla_process_unsynthesized_constraints(bzla);
      if (bzla->found_constraint_false)
      {
        result = BZLA_RESULT_UNSAT;
        break;
      }
      assert(bzla->unsynthesized_constraints->count == 0);
      assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
      assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));

      /* make SAT call on bv skeleton */
      result = timed_sat_sat(bzla, slv->sat_limit);

      /* Initialize new bit vector model, which will be constructed while
       * consistency checking. This also deletes the model from the previous
       * run.
       */
      bzla_model_init_bv(bzla, &bzla->bv_model);
    }

    if (result == BZLA_RESULT_UNSAT)
    {
      break;
    }
    else if (result == BZLA_RESULT_UNKNOWN)
    {
      assert(slv->sat_limit > -1 || bzla_terminate(bzla)
             || bzla_opt_get(bzla, BZLA_OPT_PRINT_DIMACS));
      break;
    }

    assert(result == BZLA_RESULT_SAT);

    if (bzla->ufs->count == 0 && bzla->lambdas->count == 0) break;
    bzla_reset_functions_with_model(bzla);

    check_and_resolve_conflicts(
        bzla, clone, clone_root, exp_map, &init_apps, init_apps_cache);
    if (BZLA_EMPTY_STACK(slv->cur_lemmas)) break;
    slv->stats.refinement_iterations++;

    BZLALOG(1, "add %d lemma(s)", BZLA_COUNT_STACK(slv->cur_lemmas));
    /* add generated lemmas to formula */
    for (i = 0; i < BZLA_COUNT_STACK(slv->cur_lemmas); i++)
    {
      lemma = BZLA_PEEK_STACK(slv->cur_lemmas, i);
      assert(!bzla_node_is_simplified(lemma));
      // TODO (ma): use bzla_assert_exp?
      if (slv->assume_lemmas)
        bzla_assume_exp(bzla, lemma);
      else
        bzla_insert_unsynthesized_constraint(bzla, lemma);
      if (clone)
        add_lemma_to_dual_prop_clone(bzla, clone, &clone_root, lemma, exp_map);
      BZLA_PUSH_STACK(slv->constraints, bzla_node_copy(bzla, lemma));
    }
    BZLA_RESET_STACK(slv->cur_lemmas);

    if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY))
    {
      printf(
          "[bzlaslvfun] %d iterations, %d lemmas, %d ext. lemmas, "
          "vars %d, applies %d\n",
          slv->stats.refinement_iterations,
          slv->stats.lod_refinements,
          slv->stats.extensionality_lemmas,
          bzla->ops[BZLA_VAR_NODE].cur,
          bzla->ops[BZLA_APPLY_NODE].cur);
    }

    /* may be set via insert_unsythesized_constraint
     * in case generated lemma is false */
    if (bzla->inconsistent)
    {
      result = BZLA_RESULT_UNSAT;
      break;
    }
  }

DONE:
  BZLA_RELEASE_STACK(init_apps);
  bzla_hashint_table_delete(init_apps_cache);

  if (clone)
  {
    assert(exp_map);
    bzla_nodemap_delete(exp_map);
    bzla_node_release(clone, clone_root);
    bzla_delete(clone);
  }
  if (ls_slv)
  {
    bzla->slv = ls_slv;
    ls_slv->api.delet(ls_slv);
    bzla->slv = (BzlaSolver *) slv;
  }
  bzla->last_sat_result = result;
  return result;
}

/*------------------------------------------------------------------------*/

static void
generate_model_fun_solver(BzlaFunSolver *slv,
                          bool model_for_all_nodes,
                          bool reset)
{
  assert(slv);
  assert(slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  (void) reset;

  /* already created during check_and_resolve_conflicts */
  if (!slv->bzla->bv_model) bzla_model_init_bv(slv->bzla, &slv->bzla->bv_model);
  bzla_model_init_fun(slv->bzla, &slv->bzla->fun_model);

  bzla_model_generate(slv->bzla,
                      slv->bzla->bv_model,
                      slv->bzla->fun_model,
                      model_for_all_nodes);
}

static void
print_stats_fun_solver(BzlaFunSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  uint32_t i;
  Bzla *bzla;

  bzla = slv->bzla;

  if (!(slv = BZLA_FUN_SOLVER(bzla))) return;

  if (bzla_opt_get(bzla, BZLA_OPT_FUN_PREPROP)
      || bzla_opt_get(bzla, BZLA_OPT_FUN_PRESLS))
  {
    BZLA_MSG(bzla->msg, 1, "");
    BZLA_MSG(bzla->msg, 1, "preprop/presls statistics:");
    BZLA_MSG(bzla->msg,
             1,
             "%7d assignments shared with bit-blasting engine",
             slv->stats.prels_shared);
  }

  if (bzla->ufs->count || bzla->lambdas->count)
  {
    BZLA_MSG(bzla->msg, 1, "");
    BZLA_MSG(bzla->msg, 1, "lemmas on demand statistics:");
    BZLA_MSG(bzla->msg,
             1,
             "%4d refinement iterations",
             slv->stats.refinement_iterations);
    BZLA_MSG(bzla->msg, 1, "%4d LOD refinements", slv->stats.lod_refinements);
    if (slv->stats.lod_refinements)
    {
      BZLA_MSG(bzla->msg,
               1,
               "  %4d function congruence conflicts",
               slv->stats.function_congruence_conflicts);
      BZLA_MSG(bzla->msg,
               1,
               "  %4d beta reduction conflicts",
               slv->stats.beta_reduction_conflicts);
      BZLA_MSG(bzla->msg,
               1,
               "  %4d extensionality lemmas",
               slv->stats.extensionality_lemmas);
      BZLA_MSG(bzla->msg,
               1,
               "  %.1f average lemma size",
               BZLA_AVERAGE_UTIL(slv->stats.lemmas_size_sum,
                                 slv->stats.lod_refinements));
      for (i = 1; i < BZLA_SIZE_STACK(slv->stats.lemmas_size); i++)
      {
        if (!slv->stats.lemmas_size.start[i]) continue;
        BZLA_MSG(bzla->msg,
                 1,
                 "    %4d lemmas of size %d",
                 slv->stats.lemmas_size.start[i],
                 i);
      }
    }
    BZLA_MSG(bzla->msg, 1, "");
    BZLA_MSG(bzla->msg,
             1,
             "%7lld expression evaluations",
             slv->stats.eval_exp_calls);
    BZLA_MSG(bzla->msg,
             1,
             "%7lld partial beta reductions",
             bzla->stats.betap_reduce_calls);
    BZLA_MSG(bzla->msg, 1, "%7lld propagations", slv->stats.propagations);
    BZLA_MSG(
        bzla->msg, 1, "%7lld propagations down", slv->stats.propagations_down);
  }

  if (bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP))
  {
    BZLA_MSG(bzla->msg,
             1,
             "%d/%d dual prop. vars (failed/assumed)",
             slv->stats.dp_failed_vars,
             slv->stats.dp_assumed_vars);
    BZLA_MSG(bzla->msg,
             1,
             "%d/%d dual prop. applies (failed/assumed)",
             slv->stats.dp_failed_applies,
             slv->stats.dp_assumed_applies);
  }
}

static void
print_time_stats_fun_solver(BzlaFunSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla;

  bzla = slv->bzla;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds consistency checking",
           slv->time.check_consistency);
  BZLA_MSG(bzla->msg,
           1,
           "  %.2f seconds initial applies search",
           slv->time.search_init_apps);

  if (bzla_opt_get(bzla, BZLA_OPT_FUN_JUST)
      || bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP))
  {
    BZLA_MSG(bzla->msg,
             1,
             "    %.2f seconds compute scores",
             slv->time.search_init_apps_compute_scores);
    BZLA_MSG(bzla->msg,
             1,
             "      %.2f seconds merge applies",
             slv->time.search_init_apps_compute_scores_merge_applies);
  }

  if (bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP))
  {
    BZLA_MSG(bzla->msg,
             1,
             "    %.2f seconds cloning",
             slv->time.search_init_apps_cloning);
    BZLA_MSG(bzla->msg,
             1,
             "    %.2f seconds SAT solving",
             slv->time.search_init_apps_sat);
    BZLA_MSG(bzla->msg,
             1,
             "    %.2f seconds collecting bv vars and apps",
             slv->time.search_init_apps_collect_var_apps);
    BZLA_MSG(bzla->msg,
             1,
             "    %.2f seconds collecting initial applies (FA)",
             slv->time.search_init_apps_collect_fa);
    BZLA_MSG(bzla->msg,
             1,
             "      %.2f seconds cone traversal",
             slv->time.search_init_apps_collect_fa_cone);
  }

  BZLA_MSG(bzla->msg, 1, "  %.2f seconds propagation", slv->time.prop);
  BZLA_MSG(
      bzla->msg, 1, "    %.2f seconds expression evaluation", slv->time.eval);
  BZLA_MSG(bzla->msg,
           1,
           "    %.2f seconds partial beta reduction",
           bzla->time.betap);
  BZLA_MSG(
      bzla->msg, 1, "    %.2f seconds lemma generation", slv->time.lemma_gen);
  BZLA_MSG(bzla->msg,
           1,
           "    %.2f seconds propagation apply search",
           slv->time.find_prop_app);
  BZLA_MSG(bzla->msg,
           1,
           "    %.2f seconds conflict apply search",
           slv->time.find_conf_app);
  if (bzla->feqs->count > 0)
    BZLA_MSG(bzla->msg,
             1,
             "  %.2f seconds check extensionality",
             slv->time.check_extensionality);
  BZLA_MSG(bzla->msg,
           1,
           "  %.2f seconds propagation cleanup",
           slv->time.prop_cleanup);

  BZLA_MSG(bzla->msg, 1, "");
  if ((bzla_opt_get(bzla, BZLA_OPT_FUN_PREPROP)
       || bzla_opt_get(bzla, BZLA_OPT_FUN_PRESLS))
      && bzla_opt_get(bzla, BZLA_OPT_LS_SHARE_SAT))
  {
    BZLA_MSG(bzla->msg,
             1,
             "%.2f seconds for preprop/presls SAT check with partial "
             "assignment",
             slv->time.prels_sat);
  }
  BZLA_MSG(bzla->msg, 1, "%.2f seconds in pure SAT solving", slv->time.sat);
  BZLA_MSG(bzla->msg, 1, "");
}

static void
print_model_fun_solver(BzlaFunSolver *slv, const char *format, FILE *file)
{
  bzla_print_model_aufbvfp(slv->bzla, format, file);
}

BzlaSolver *
bzla_new_fun_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaFunSolver *slv;

  BZLA_CNEW(bzla->mm, slv);

  slv->kind = BZLA_FUN_SOLVER_KIND;
  slv->bzla = bzla;

  slv->api.clone          = (BzlaSolverClone) clone_fun_solver;
  slv->api.delet          = (BzlaSolverDelete) delete_fun_solver;
  slv->api.sat            = (BzlaSolverSat) sat_fun_solver;
  slv->api.generate_model = (BzlaSolverGenerateModel) generate_model_fun_solver;
  slv->api.print_stats    = (BzlaSolverPrintStats) print_stats_fun_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_fun_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_fun_solver;

  slv->lod_limit = -1;
  slv->sat_limit = -1;

  slv->lemmas = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
  BZLA_INIT_STACK(bzla->mm, slv->cur_lemmas);
  BZLA_INIT_STACK(bzla->mm, slv->constraints);

  BZLA_INIT_STACK(bzla->mm, slv->stats.lemmas_size);

  BZLA_MSG(bzla->msg, 1, "enabled core engine");

  return (BzlaSolver *) slv;
}

// TODO (ma): this is just a fix for now, this should be moved elsewhere
BzlaBitVector *
bzla_eval_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(bzla->slv);
  assert(bzla->slv->kind == BZLA_FUN_SOLVER_KIND);
  assert(exp);
  assert(bzla->bv_model);

  uint32_t i;
  double start;
  BzlaMemMgr *mm;
  BzlaNodePtrStack work_stack;
  BzlaVoidPtrStack arg_stack;
  BzlaNode *cur, *real_cur, *next;
  BzlaPtrHashTable *cache;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTableIterator it;
  BzlaBitVector *result = 0, *inv_result, **e;
  BzlaFunSolver *slv;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;

  start = bzla_util_time_stamp();
  mm    = bzla->mm;
  slv   = BZLA_FUN_SOLVER(bzla);
  slv->stats.eval_exp_calls++;

  BZLA_INIT_STACK(mm, work_stack);
  BZLA_INIT_STACK(mm, arg_stack);
  cache = bzla_hashptr_table_new(mm,
                                 (BzlaHashPtr) bzla_node_hash_by_id,
                                 (BzlaCmpPtr) bzla_node_compare_by_id);
  mark  = bzla_hashint_map_new(mm);

  BZLA_PUSH_STACK(work_stack, exp);
  while (!BZLA_EMPTY_STACK(work_stack))
  {
    cur      = bzla_node_get_simplified(bzla, BZLA_POP_STACK(work_stack));
    real_cur = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(mark, real_cur->id);

    if (!d)
    {
      if (bzla_node_is_bv_var(real_cur) || bzla_node_is_apply(real_cur)
          || bzla_node_is_fun_eq(real_cur) || has_bv_assignment(bzla, real_cur))
      {
        result = get_bv_assignment(bzla, real_cur);
        goto EVAL_EXP_PUSH_RESULT;
      }
      else if (bzla_node_is_bv_const(real_cur))
      {
        result = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(real_cur));
        goto EVAL_EXP_PUSH_RESULT;
      }
      /* Word-blast FP nodes and do evaluation on BV representation */
      else if (bzla_node_fp_needs_word_blast(bzla, real_cur))
      {
        next = bzla_fp_word_blast(bzla, real_cur);
        BZLA_PUSH_STACK(work_stack, next);
        continue;
      }
      /* substitute param with its assignment */
      else if (bzla_node_is_param(real_cur))
      {
        next = bzla_node_param_get_assigned_exp(real_cur);
        assert(next);
        if (bzla_node_is_inverted(cur)) next = bzla_node_invert(next);
        BZLA_PUSH_STACK(work_stack, next);
        continue;
      }

      BZLA_PUSH_STACK(work_stack, cur);
      bzla_hashint_map_add(mark, real_cur->id);

      for (i = 0; i < real_cur->arity; i++)
        BZLA_PUSH_STACK(work_stack, real_cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      assert(!bzla_node_is_param(real_cur));
      assert(!bzla_node_is_args(real_cur));
      assert(!bzla_node_is_fun(real_cur));
      assert(real_cur->arity >= 1);
      assert(real_cur->arity <= BZLA_NODE_MAX_CHILDREN);
      assert(real_cur->arity <= BZLA_COUNT_STACK(arg_stack));

      d->as_int = 1;
      arg_stack.top -= real_cur->arity;
      e = (BzlaBitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BZLA_BV_SLICE_NODE:
          result = bzla_bv_slice(mm,
                                 e[0],
                                 bzla_node_bv_slice_get_upper(real_cur),
                                 bzla_node_bv_slice_get_lower(real_cur));
          bzla_bv_free(mm, e[0]);
          break;
        case BZLA_BV_AND_NODE:
          result = bzla_bv_and(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_EQ_NODE:
          result = bzla_bv_eq(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_ADD_NODE:
          result = bzla_bv_add(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_MUL_NODE:
          result = bzla_bv_mul(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_ULT_NODE:
          result = bzla_bv_ult(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_SLT_NODE:
          result = bzla_bv_slt(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_SLL_NODE:
          result = bzla_bv_sll(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_SRL_NODE:
          result = bzla_bv_srl(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_UDIV_NODE:
          result = bzla_bv_udiv(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_UREM_NODE:
          result = bzla_bv_urem(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_CONCAT_NODE:
          result = bzla_bv_concat(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_COND_NODE:
          if (bzla_bv_is_true(e[2]))
            result = bzla_bv_copy(mm, e[1]);
          else
            result = bzla_bv_copy(mm, e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          bzla_bv_free(mm, e[2]);
          break;
        default:
          BZLALOG(1, "  *** %s", bzla_util_node2string(real_cur));
          /* should be unreachable */
          assert(0);
      }

      assert(!bzla_hashptr_table_get(cache, real_cur));
      bzla_hashptr_table_add(cache, real_cur)->data.as_ptr =
          bzla_bv_copy(mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (bzla_node_is_inverted(cur))
      {
        inv_result = bzla_bv_not(mm, result);
        bzla_bv_free(mm, result);
        result = inv_result;
      }

      BZLA_PUSH_STACK(arg_stack, result);
    }
    else
    {
      assert(d->as_int == 1);
      b = bzla_hashptr_table_get(cache, real_cur);
      assert(b);
      result = bzla_bv_copy(mm, (BzlaBitVector *) b->data.as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(arg_stack) == 1);
  result = BZLA_POP_STACK(arg_stack);
  assert(result);

  while (!BZLA_EMPTY_STACK(arg_stack))
  {
    inv_result = BZLA_POP_STACK(arg_stack);
    bzla_bv_free(mm, inv_result);
  }

  bzla_iter_hashptr_init(&it, cache);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_bv_free(mm, (BzlaBitVector *) it.bucket->data.as_ptr);
    real_cur = bzla_iter_hashptr_next(&it);
  }

  BZLA_RELEASE_STACK(work_stack);
  BZLA_RELEASE_STACK(arg_stack);
  bzla_hashptr_table_delete(cache);
  bzla_hashint_map_delete(mark);

  //  BZLALOG ("%s: %s '%s'", __FUNCTION__, bzla_util_node2string (exp),
  //  result);
  slv->time.eval += bzla_util_time_stamp() - start;

  return result;
}
