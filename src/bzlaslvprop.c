/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlaslvprop.h"

#include <math.h>

#include "bzlaabort.h"
#include "bzlabv.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlalsutils.h"
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlaopt.h"
#include "bzlaprintmodel.h"
#include "bzlaproputils.h"
#include "bzlaslsutils.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#define BZLA_PROP_MAXSTEPS_CFACT 100
#define BZLA_PROP_MAXSTEPS(i) \
  (BZLA_PROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BZLA_PROP_SELECT_CFACT 20

/*------------------------------------------------------------------------*/

static BzlaNode *
select_constraint(Bzla *bzla, uint32_t nmoves)
{
  assert(bzla);

  BzlaNode *res, *cur;
  BzlaPropSolver *slv;
  BzlaIntHashTableIterator it;

  slv = BZLA_PROP_SOLVER(bzla);
  assert(slv);
  assert(slv->roots);
  assert(slv->roots->count);

#ifndef NDEBUG
  BzlaPtrHashTableIterator pit;
  BzlaNode *root;
  bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    root = bzla_iter_hashptr_next(&pit);
    if (bzla_bv_is_false(bzla_model_get_bv(bzla, root)))
      assert(bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root)));
    else
      assert(!bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root)));
  }
#endif

  res = 0;

  if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
  {
    assert(slv->score);

    int32_t *selected;
    double value, max_value, score;
    max_value = 0.0;
    bzla_iter_hashint_init(&it, slv->roots);
    while (bzla_iter_hashint_has_next(&it))
    {
      selected = &slv->roots->data[it.cur_pos].as_int;
      cur      = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));

      assert(bzla_hashint_map_contains(slv->score, bzla_node_get_id(cur)));
      score = bzla_hashint_map_get(slv->score, bzla_node_get_id(cur))->as_dbl;
      assert(score < 1.0);
      value = score + BZLA_PROP_SELECT_CFACT * sqrt(log(*selected) / nmoves);

      if (!res || value > max_value)
      {
        res       = cur;
        max_value = value;
        *selected += 1;
      }
    }
  }
  else
  {
    size_t j, r;

    j = 0;
    r = bzla_rng_pick_rand(&bzla->rng, 0, slv->roots->count - 1);
    bzla_iter_hashint_init(&it, slv->roots);
    while (bzla_iter_hashint_has_next(&it) && j <= r)
    {
      res = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));
      j += 1;
    }
    assert(res);
    assert(!bzla_node_is_bv_const(res));
  }

  assert(res);
  assert(bzla_bv_is_zero(bzla_model_get_bv(bzla, res)));

  BZLALOG(1, "");
  BZLALOG(1, "select constraint: %s", bzla_util_node2string(res));

  return res;
}

static bool
move(Bzla *bzla, uint32_t nmoves)
{
  assert(bzla);

  BZLALOG(1, "");
  BZLALOG(1, "*** move");

  BzlaNode *root, *input;
  BzlaBitVector *bvroot, *assignment;
  BzlaPropSolver *slv;
  BzlaIntHashTable *exps;
  BzlaPropInfo prop;
  int32_t eidx;
  uint64_t props;

  slv = BZLA_PROP_SOLVER(bzla);
  assert(slv);

  bvroot = 0;
  do
  {
    if (bvroot) bzla_bv_free(bzla->mm, bvroot);

    if (BZLA_EMPTY_STACK(slv->toprop))
    {
      root   = select_constraint(bzla, nmoves);
      bvroot = bzla_bv_one(bzla->mm, 1);
      eidx   = -1;
    }
    else
    {
      prop   = BZLA_POP_STACK(slv->toprop);
      root   = prop.exp;
      bvroot = prop.bvexp;
      eidx   = prop.eidx;
    }

    props = bzla_proputils_select_move_prop(
        bzla, root, bvroot, eidx, &input, &assignment);
  } while (!input);

  assert(assignment);
  slv->stats.props += props;
  if (eidx != -1) slv->stats.props_entailed += props;

  bzla_bv_free(bzla->mm, bvroot);

#ifndef NBZLALOG
  char *a;
  BzlaBitVector *ass;
  ass = (BzlaBitVector *) bzla_model_get_bv(bzla, input);
  a   = bzla_bv_to_char(bzla->mm, ass);
  BZLALOG(1, "");
  BZLALOG(1, "move");
  BZLALOG(1,
          "  input: %s%s",
          bzla_node_is_regular(input) ? "" : "-",
          bzla_util_node2string(input));
  BZLALOG(1, "  prev. assignment: %s", a);
  bzla_mem_freestr(bzla->mm, a);
  a = bzla_bv_to_char(bzla->mm, assignment);
  BZLALOG(1, "  new   assignment: %s", a);
  bzla_mem_freestr(bzla->mm, a);
#endif

  exps = bzla_hashint_map_new(bzla->mm);
  assert(bzla_node_is_regular(input));
  bzla_hashint_map_add(exps, input->id)->as_ptr = assignment;
  bzla_lsutils_update_cone(
      bzla,
      bzla->bv_model,
      slv->roots,
      bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT) ? slv->score : 0,
      exps,
      true,
      &slv->stats.updates,
      &slv->time.update_cone,
      &slv->time.update_cone_reset,
      &slv->time.update_cone_model_gen,
      &slv->time.update_cone_compute_score);
  bzla_hashint_map_delete(exps);

  slv->stats.moves += 1;
  if (eidx != -1) slv->stats.fixed_conf += 1;
  bzla_bv_free(bzla->mm, assignment);

  return true;
}

/*------------------------------------------------------------------------*/

static BzlaPropSolver *
clone_prop_solver(Bzla *clone, BzlaPropSolver *slv, BzlaNodeMap *exp_map)
{
  assert(clone);
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);

  BzlaPropSolver *res;

  (void) exp_map;

  BZLA_NEW(clone->mm, res);
  memcpy(res, slv, sizeof(BzlaPropSolver));

  res->bzla  = clone;
  res->roots = bzla_hashint_map_clone(clone->mm, slv->roots, 0, 0);
  res->score =
      bzla_hashint_map_clone(clone->mm, slv->score, bzla_clone_data_as_dbl, 0);

  bzla_proputils_clone_prop_info_stack(
      clone->mm, &slv->toprop, &res->toprop, exp_map);
  return res;
}

static void
delete_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  if (slv->score) bzla_hashint_map_delete(slv->score);
  if (slv->roots) bzla_hashint_map_delete(slv->roots);

  assert(BZLA_EMPTY_STACK(slv->toprop));
  BZLA_RELEASE_STACK(slv->toprop);
  BZLA_DELETE(slv->bzla->mm, slv);
}

/* This is an extra function in order to be able to test completeness
 * via test suite. */
#ifdef NDEBUG
static inline int32_t
#else
int32_t
#endif
sat_prop_solver_aux(Bzla *bzla)
{
  assert(bzla);

  uint32_t j, max_steps;
  int32_t sat_result;
  uint32_t nmoves, nprops;
  BzlaNode *root;
  BzlaPtrHashTableIterator it;
  BzlaPropSolver *slv;

  slv = BZLA_PROP_SOLVER(bzla);
  assert(slv);
  nprops = bzla_opt_get(bzla, BZLA_OPT_PROP_NPROPS);

  nmoves = 0;

  /* check for constraints occurring in both phases */
  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    root = bzla_iter_hashptr_next(&it);
    if (bzla_hashptr_table_get(bzla->unsynthesized_constraints,
                               bzla_node_invert(root)))
      goto UNSAT;
    if (bzla_hashptr_table_get(bzla->synthesized_constraints,
                               bzla_node_invert(root)))
      goto UNSAT;
    if (bzla_hashptr_table_get(bzla->assumptions, bzla_node_invert(root)))
      goto UNSAT;
  }

  for (;;)
  {
    assert(BZLA_EMPTY_STACK(slv->toprop));

    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert(!slv->roots);
    slv->roots = bzla_hashint_map_new(bzla->mm);
    bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->assumptions);
    while (bzla_iter_hashptr_has_next(&it))
    {
      root = bzla_iter_hashptr_next(&it);

      if (!bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root))
          && bzla_bv_is_zero(bzla_model_get_bv(bzla, root)))
      {
        if (bzla_node_is_bv_const(root))
          goto UNSAT; /* contains false constraint -> unsat */
        bzla_hashint_map_add(slv->roots, bzla_node_get_id(root));
      }
    }

    if (!slv->score && bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
      slv->score = bzla_hashint_map_new(bzla->mm);

    if (bzla_terminate(bzla))
    {
      sat_result = BZLA_RESULT_UNKNOWN;
      goto DONE;
    }

    /* all constraints sat? */
    if (!slv->roots->count) goto SAT;

    /* compute initial sls score */
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
      bzla_slsutils_compute_sls_scores(
          bzla, bzla->bv_model, bzla->fun_model, slv->score);

    /* init */
    slv->flip_cond_const_prob =
        bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND_CONST);
    slv->flip_cond_const_prob_delta =
        slv->flip_cond_const_prob > (BZLA_PROB_MAX / 2)
            ? -BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA
            : BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA;

    /* move */
    for (j = 0, max_steps = BZLA_PROP_MAXSTEPS(slv->stats.restarts + 1);
         !bzla_opt_get(bzla, BZLA_OPT_PROP_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (bzla_terminate(bzla) || (nprops && slv->stats.props >= nprops))
      {
        sat_result = BZLA_RESULT_UNKNOWN;
        goto DONE;
      }

      if (!(move(bzla, nmoves))) goto UNSAT;
      nmoves += 1;

      /* all constraints sat? */
      if (!slv->roots->count) goto SAT;
    }

    /* restart */
    slv->api.generate_model((BzlaSolver *) slv, false, true);
    bzla_hashint_map_delete(slv->roots);
    slv->roots = 0;
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
    {
      bzla_hashint_map_delete(slv->score);
      slv->score = bzla_hashint_map_new(bzla->mm);
    }
    slv->stats.restarts += 1;
    bzla_proputils_reset_prop_info_stack(slv->bzla->mm, &slv->toprop);
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
  if (slv->score)
  {
    bzla_hashint_map_delete(slv->score);
    slv->score = 0;
  }
  bzla_proputils_reset_prop_info_stack(slv->bzla->mm, &slv->toprop);
  return sat_result;
}

/* Note: failed assumptions handling not necessary, prop only works for SAT */
static int32_t
sat_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  int32_t sat_result;
  Bzla *bzla;

  bzla = slv->bzla;
  assert(!bzla->inconsistent);

  if (bzla_terminate(bzla))
  {
    sat_result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  BZLA_ABORT(bzla->ufs->count != 0
                 || (!bzla_opt_get(bzla, BZLA_OPT_BETA_REDUCE)
                     && bzla->lambdas->count != 0),
             "prop engine supports QF_BV only");

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model((BzlaSolver *) slv, false, true);
  sat_result = sat_prop_solver_aux(bzla);
DONE:
  assert(BZLA_EMPTY_STACK(slv->toprop));
  return sat_result;
}

static void
generate_model_prop_solver(BzlaPropSolver *slv,
                           bool model_for_all_nodes,
                           bool reset)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla = slv->bzla;

  if (!reset && bzla->bv_model) return;
  bzla_model_init_bv(bzla, &bzla->bv_model);
  bzla_model_init_fun(bzla, &bzla->fun_model);
  bzla_model_generate(
      bzla, bzla->bv_model, bzla->fun_model, model_for_all_nodes);
}

static void
print_stats_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla           = slv->bzla;
  bool enable_entailed = bzla_opt_get(slv->bzla, BZLA_OPT_PROP_ENTAILED);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "restarts: %u", slv->stats.restarts);
  BZLA_MSG(bzla->msg, 1, "moves: %u", slv->stats.moves);

  BZLA_MSG(bzla->msg,
           1,
           "moves per second: %.2f",
           (double) slv->stats.moves / (bzla->time.sat - bzla->time.simplify));
  BZLA_MSG(bzla->msg, 1, "propagation (steps): %u", slv->stats.props);
  if (enable_entailed)
    BZLA_MSG(bzla->msg,
             1,
             "   entailed propagations: %u",
             slv->stats.props_entailed);
  BZLA_MSG(bzla->msg,
           1,
           "   consistent value propagations: %u",
           slv->stats.props_cons);
  BZLA_MSG(
      bzla->msg, 1, "   inverse value propagations: %u", slv->stats.props_inv);
  BZLA_MSG(bzla->msg,
           1,
           "propagation (steps) per second: %.2f",
           (double) slv->stats.props / (bzla->time.sat - bzla->time.simplify));
  BZLA_MSG(bzla->msg,
           1,
           "propagation conflicts (non-recoverable): %u",
           slv->stats.non_rec_conf);
  BZLA_MSG(bzla->msg,
           1,
           "propagation conflicts (recoverable): %u",
           slv->stats.rec_conf);
  if (enable_entailed)
    BZLA_MSG(bzla->msg,
             1,
             "   fixed recoverable conflicts (= entailed moves): %u",
             slv->stats.fixed_conf);
  BZLA_MSG(bzla->msg, 1, "updates (cone): %u", slv->stats.updates);
#ifndef NDEBUG
  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (add): %u", slv->stats.cons_add);
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (and): %u", slv->stats.cons_and);
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (eq): %u", slv->stats.cons_eq);
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (ult): %u", slv->stats.cons_ult);
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (sll): %u", slv->stats.cons_sll);
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (srl): %u", slv->stats.cons_srl);
  BZLA_MSG(bzla->msg, 1, "consistent fun calls (mul): %u", slv->stats.cons_mul);
  BZLA_MSG(
      bzla->msg, 1, "consistent fun calls (udiv): %u", slv->stats.cons_udiv);
  BZLA_MSG(
      bzla->msg, 1, "consistent fun calls (urem): %u", slv->stats.cons_urem);
  BZLA_MSG(bzla->msg,
           1,
           "consistent fun calls (concat): %u",
           slv->stats.cons_concat);
  BZLA_MSG(
      bzla->msg, 1, "consistent fun calls (slice): %u", slv->stats.cons_slice);
  BZLA_MSG(
      bzla->msg, 1, "consistent fun calls (cond): %u", slv->stats.cons_cond);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (add): %u", slv->stats.inv_add);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (and): %u", slv->stats.inv_and);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (eq): %u", slv->stats.inv_eq);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (ult): %u", slv->stats.inv_ult);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (sll): %u", slv->stats.inv_sll);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (srl): %u", slv->stats.inv_srl);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (mul): %u", slv->stats.inv_mul);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (udiv): %u", slv->stats.inv_udiv);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (urem): %u", slv->stats.inv_urem);
  BZLA_MSG(
      bzla->msg, 1, "inverse fun calls (concat): %u", slv->stats.inv_concat);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (slice): %u", slv->stats.inv_slice);
  BZLA_MSG(bzla->msg, 1, "inverse fun calls (cond): %u", slv->stats.inv_cond);
#endif
}

static void
print_time_stats_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

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
  if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
    BZLA_MSG(bzla->msg,
             1,
             "%.2f seconds for updating cone (compute score)",
             slv->time.update_cone_compute_score);
  BZLA_MSG(bzla->msg, 1, "");
}

static void
print_model_prop_solver(BzlaPropSolver *slv, const char *format, FILE *file)
{
  bzla_print_model_aufbv(slv->bzla, format, file);
}

BzlaSolver *
bzla_new_prop_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaPropSolver *slv;

  BZLA_CNEW(bzla->mm, slv);

  slv->bzla = bzla;
  slv->kind = BZLA_PROP_SOLVER_KIND;

  slv->api.clone = (BzlaSolverClone) clone_prop_solver;
  slv->api.delet = (BzlaSolverDelete) delete_prop_solver;
  slv->api.sat   = (BzlaSolverSat) sat_prop_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_prop_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_prop_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_prop_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_prop_solver;

  BZLA_INIT_STACK(bzla->mm, slv->toprop);

  BZLA_MSG(bzla->msg, 1, "enabled prop engine");

  return (BzlaSolver *) slv;
}
