/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaslvaigprop.h"

#include "aigprop.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlamodel.h"
#include "bzlaopt.h"
#include "bzlaprintmodel.h"
#include "bzlaslvprop.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"

/*------------------------------------------------------------------------*/

#define BZLA_AIGPROP_MAXSTEPS_CFACT 100
#define BZLA_AIGPROP_MAXSTEPS(i) \
  (BZLA_AIGPROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

/*------------------------------------------------------------------------*/

static BzlaAIGPropSolver *
clone_aigprop_solver(Bzla *clone, BzlaAIGPropSolver *slv, BzlaNodeMap *exp_map)
{
  assert(clone);
  assert(slv);
  assert(slv->kind == BZLA_AIGPROP_SOLVER_KIND);
  assert(exp_map);

  (void) exp_map;

  BzlaAIGPropSolver *res;

  BZLA_NEW(clone->mm, res);
  memcpy(res, slv, sizeof(BzlaAIGPropSolver));
  res->bzla  = clone;
  res->aprop = bzla_aigprop_clone_aigprop(bzla_get_aig_mgr(clone), slv->aprop);
  return res;
}

static void
delete_aigprop_solver(BzlaAIGPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_AIGPROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla = slv->bzla;

  if (slv->aprop) bzla_aigprop_delete_aigprop(slv->aprop);
  BZLA_DELETE(bzla->mm, slv);
}

static int32_t
get_assignment_aig(BzlaAIGProp *aprop, BzlaAIG *aig)
{
  assert(aprop);
  assert(aprop->model);

  if (aig == BZLA_AIG_TRUE) return 1;
  if (aig == BZLA_AIG_FALSE) return -1;
  /* initialize don't care bits with false */
  if (!bzla_hashint_map_contains(aprop->model, BZLA_REAL_ADDR_AIG(aig)->id))
    return BZLA_IS_INVERTED_AIG(aig) ? 1 : -1;
  return bzla_aigprop_get_assignment_aig(aprop, aig);
}

static BzlaBitVector *
get_assignment_bv(BzlaMemMgr *mm, BzlaNode *exp, BzlaAIGProp *aprop)
{
  assert(mm);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(aprop);

  int32_t bit;
  uint32_t i, j, width;
  BzlaBitVector *res;
  BzlaAIGVec *av;

  if (!exp->av) return bzla_bv_new(mm, bzla_node_bv_get_width(exp->bzla, exp));

  av    = exp->av;
  width = av->width;
  res   = bzla_bv_new(mm, width);

  for (i = 0, j = width - 1; i < width; i++, j--)
  {
    bit = get_assignment_aig(aprop, av->aigs[j]);
    assert(bit == -1 || bit == 1);
    bzla_bv_set_bit(res, i, bit == 1 ? 1 : 0);
  }
  return res;
}

static void
generate_model_from_aig_model(Bzla *bzla)
{
  assert(bzla);

  uint32_t i;
  BzlaNode *cur, *real_cur;
  BzlaBitVector *bv;
  BzlaAIGPropSolver *slv;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack stack;
  BzlaIntHashTable *cache;
  BzlaAIGProp *aprop;

  if (!(slv = BZLA_AIGPROP_SOLVER(bzla))) return;

  aprop = slv->aprop;
  assert(aprop);
  assert(aprop->model);

  bzla_model_init_bv(bzla, &bzla->bv_model);
  bzla_model_init_fun(bzla, &bzla->fun_model);

  /* map inputs back to expression layer
   * Note: we can only map inputs back, since other nodes might have partial
   *       assignments only (e.g. for a slice we may have AIGs for the sliced
   *       bits of its input only) */
  BZLA_INIT_STACK(bzla->mm, stack);
  cache = bzla_hashint_table_new(bzla->mm);
  assert(bzla->unsynthesized_constraints->count == 0);
  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    BZLA_PUSH_STACK(stack, bzla_iter_hashptr_next(&it));
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = bzla_node_real_addr(cur);
    if (bzla_hashint_table_contains(cache, real_cur->id)) continue;
    bzla_hashint_table_add(cache, real_cur->id);
    if (bzla_node_is_bv_const(real_cur))
      bzla_model_add_to_bv(bzla,
                           bzla->bv_model,
                           real_cur,
                           bzla_node_bv_const_get_bits(real_cur));
    if (bzla_node_is_bv_var(real_cur))
    {
      bv = get_assignment_bv(bzla->mm, real_cur, aprop);
      bzla_model_add_to_bv(bzla, bzla->bv_model, real_cur, bv);
      bzla_bv_free(bzla->mm, bv);
    }
    for (i = 0; i < real_cur->arity; i++)
      BZLA_PUSH_STACK(stack, real_cur->e[i]);
  }
  BZLA_RELEASE_STACK(stack);
  bzla_hashint_table_delete(cache);
}

static void
generate_model_aigprop_solver(BzlaAIGPropSolver *slv,
                              bool model_for_all_nodes,
                              bool reset)
{
  assert(slv);

  Bzla *bzla = slv->bzla;

  if (reset)
  {
    bzla_model_init_bv(bzla, &bzla->bv_model);
    bzla_model_init_fun(bzla, &bzla->fun_model);
    bzla_model_generate(
        bzla, bzla->bv_model, bzla->fun_model, model_for_all_nodes);
    return;
  }

  /* generate model for non-input nodes */
  bzla_model_generate(
      bzla, bzla->bv_model, bzla->fun_model, model_for_all_nodes);
}

/* Note: limits are currently unused */
static int32_t
sat_aigprop_solver(BzlaAIGPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_AIGPROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  int32_t sat_result;
  BzlaIntHashTable *roots;
  BzlaPtrHashTableIterator it;
  BzlaNode *root;
  BzlaAIG *aig;
  Bzla *bzla;

  bzla = slv->bzla;
  assert(!bzla->inconsistent);
  roots = 0;

  if (bzla_terminate(bzla))
  {
  UNKNOWN:
    sat_result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  BZLA_ABORT(bzla->ufs->count != 0
                 || (!bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE)
                     && bzla->lambdas->count != 0),
             "aigprop engine supports QF_BV only");

  bzla_process_unsynthesized_constraints(bzla);

  if (bzla->found_constraint_false)
  {
  UNSAT:
    sat_result = BZLA_RESULT_UNSAT;
    goto DONE;
  }
  assert(bzla->unsynthesized_constraints->count == 0);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));

#ifndef NDEBUG
  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    assert(!bzla_node_real_addr(((BzlaNode *) bzla_iter_hashptr_next(&it)))
                ->simplified);
#endif

  assert(slv->aprop);
  assert(!slv->aprop->roots);
  assert(!slv->aprop->score);
  assert(!slv->aprop->model);
  slv->aprop->loglevel     = bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL);
  slv->aprop->seed         = bzla_opt_get(bzla, BZLA_OPT_SEED);
  slv->aprop->use_restarts = bzla_opt_get(bzla, BZLA_OPT_AIGPROP_USE_RESTARTS);
  slv->aprop->use_bandit   = bzla_opt_get(bzla, BZLA_OPT_AIGPROP_USE_BANDIT);

  /* collect roots AIGs */
  roots = bzla_hashint_table_new(bzla->mm);
  assert(bzla->unsynthesized_constraints->count == 0);
  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    root = bzla_iter_hashptr_next(&it);

    if (!bzla_node_real_addr(root)->av) bzla_synthesize_exp(bzla, root, 0);
    assert(bzla_node_real_addr(root)->av->width == 1);
    aig = bzla_node_real_addr(root)->av->aigs[0];
    if (bzla_node_is_inverted(root)) aig = BZLA_INVERT_AIG(aig);
    if (aig == BZLA_AIG_FALSE) goto UNSAT;
    if (aig == BZLA_AIG_TRUE) continue;
    if (!bzla_hashint_table_contains(roots, bzla_aig_get_id(aig)))
      (void) bzla_hashint_table_add(roots, bzla_aig_get_id(aig));
  }

  sat_result = bzla_aigprop_sat(slv->aprop, roots);
  if (sat_result == BZLA_AIGPROP_UNKNOWN)
    goto UNKNOWN;
  else if (sat_result == BZLA_AIGPROP_UNSAT)
    goto UNSAT;
  assert(sat_result == BZLA_AIGPROP_SAT);
  sat_result = BZLA_RESULT_SAT;
  generate_model_from_aig_model(bzla);
DONE:
  slv->stats.moves                  = slv->aprop->stats.moves;
  slv->stats.props                  = slv->aprop->stats.props;
  slv->stats.restarts               = slv->aprop->stats.restarts;
  slv->time.aprop_sat               = slv->aprop->time.sat;
  slv->time.aprop_update_cone       = slv->aprop->time.update_cone;
  slv->time.aprop_update_cone_reset = slv->aprop->time.update_cone_reset;
  slv->time.aprop_update_cone_model_gen =
      slv->aprop->time.update_cone_model_gen;
  slv->time.aprop_update_cone_compute_score =
      slv->aprop->time.update_cone_compute_score;
  if (slv->aprop->model)
  {
    bzla_hashint_map_delete(slv->aprop->model);
    slv->aprop->model = 0;
  }
  if (roots) bzla_hashint_table_delete(roots);
  return sat_result;
}

static void
print_stats_aigprop_solver(BzlaAIGPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_AIGPROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla;

  bzla = slv->bzla;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "restarts: %d", slv->stats.restarts);
  BZLA_MSG(bzla->msg, 1, "moves: %d", slv->stats.moves);
  BZLA_MSG(
      bzla->msg,
      1,
      "moves per second: %.2f",
      slv->stats.moves ? (double) slv->stats.moves / slv->time.aprop_sat : 0.0);
  BZLA_MSG(bzla->msg, 1, "props: %d", slv->stats.props);
  BZLA_MSG(
      bzla->msg,
      1,
      "props per second: %.2f",
      slv->stats.props ? (double) slv->stats.props / slv->time.aprop_sat : 0.0);
}

static void
print_time_stats_aigprop_solver(BzlaAIGPropSolver *slv)
{
  assert(slv);

  Bzla *bzla;

  bzla = slv->bzla;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "%.2f seconds in AIG propagator", slv->time.aprop_sat);
  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (total)",
           slv->time.aprop_update_cone);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (reset)",
           slv->time.aprop_update_cone_reset);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (model gen)",
           slv->time.aprop_update_cone_model_gen);
  if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
    BZLA_MSG(bzla->msg,
             1,
             "%.2f seconds for updating cone (compute score)",
             slv->time.aprop_update_cone_compute_score);
  BZLA_MSG(bzla->msg, 1, "");
}

static void
print_model(BzlaAIGPropSolver *slv, const char *format, FILE *file)
{
  bzla_print_model_aufbvfp(slv->bzla, format, file);
}

BzlaSolver *
bzla_new_aigprop_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaAIGPropSolver *slv;

  BZLA_CNEW(bzla->mm, slv);

  slv->bzla = bzla;
  slv->kind = BZLA_AIGPROP_SOLVER_KIND;

  slv->api.clone = (BzlaSolverClone) clone_aigprop_solver;
  slv->api.delet = (BzlaSolverDelete) delete_aigprop_solver;
  slv->api.sat   = (BzlaSolverSat) sat_aigprop_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_aigprop_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_aigprop_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_aigprop_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model;

  slv->aprop = bzla_aigprop_new_aigprop(
      bzla_get_aig_mgr(bzla),
      bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL),
      bzla_opt_get(bzla, BZLA_OPT_SEED),
      bzla_opt_get(bzla, BZLA_OPT_AIGPROP_USE_RESTARTS),
      bzla_opt_get(bzla, BZLA_OPT_AIGPROP_USE_BANDIT),
      bzla_opt_get(bzla, BZLA_OPT_AIGPROP_NPROPS));

  BZLA_MSG(bzla->msg, 1, "enabled aigprop engine");

  return (BzlaSolver *) slv;
}
