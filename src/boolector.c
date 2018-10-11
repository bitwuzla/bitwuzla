/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2016 Armin Biere.
 *  Copyright (C) 2012-2020 Mathias Preiner.
 *  Copyright (C) 2013-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#include "boolector.h"

#include "bzlaabort.h"
#include "bzlachkclone.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlaexit.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlaparse.h"
#include "bzlaprintmodel.h"
#include "bzlasat.h"
#include "bzlasort.h"
#include "bzlatrapi.h"
#include "dumper/bzladumpaig.h"
#include "dumper/bzladumpbtor.h"
#include "dumper/bzladumpsmt.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#include <limits.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static void
abort_aux(const char *msg)
{
  if (bzla_abort_callback.cb_fun)
    ((void (*)(const char *)) bzla_abort_callback.cb_fun)(msg);
}

BzlaAbortCallback bzla_abort_callback = {.abort_fun = abort_aux,
                                         .cb_fun    = bzla_abort_fun};

/*------------------------------------------------------------------------*/

static void
inc_sort_ext_ref_counter(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);
  assert(id);

  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);

  BZLA_ABORT(sort->ext_refs == INT32_MAX, "Node reference counter overflow");
  sort->ext_refs += 1;
  bzla->external_refs += 1;
}

static void
dec_sort_ext_ref_counter(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);
  assert(id);

  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->ext_refs > 0);
  sort->ext_refs -= 1;
  bzla->external_refs -= 1;
}

/*------------------------------------------------------------------------*/

void
boolector_chkclone(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");

#ifndef NDEBUG
  BzlaBVAss *bvass, *cbvass;
  BzlaBVAssList *bvasslist, *cbvasslist;
  BzlaFunAss *funass, *cfunass;
  BzlaFunAssList *funasslist, *cfunasslist;
  char **indices, **values, **cindices, **cvalues;
  uint32_t i;

  if (bzla->clone)
  {
    /* force auto cleanup (might have been disabled via btormbt) */
    bzla_opt_set(bzla->clone, BZLA_OPT_AUTO_CLEANUP, 1);
    bzla_delete(bzla->clone);
    bzla->clone = 0;
  }
  /* do not generate shadow clone if sat solver does not support cloning
   * (else only expression layer will be cloned and shadowed API function
   *  calls may fail) */
  if (!bzla_sat_mgr_has_clone_support(bzla_get_sat_mgr(bzla))) return;
  bzla->clone           = bzla_clone(bzla);
  bzla->clone->apitrace = 0; /* disable tracing of shadow clone */
  assert(bzla->clone->mm);
  assert((!bzla->avmgr && !bzla->clone->avmgr)
         || (bzla->avmgr && bzla->clone->avmgr));
  /* update assignment lists */
  bvasslist  = bzla->bv_assignments;
  cbvasslist = bzla->clone->bv_assignments;
  for (bvass = bvasslist->first, cbvass = cbvasslist->first; bvass;
       bvass = bvass->next, cbvass = cbvass->next)
  {
    assert(cbvass);
    assert(!strcmp(bzla_ass_get_bv_str(bvass), bzla_ass_get_bv_str(cbvass)));
    bvass->cloned_assignment = bzla_ass_get_bv_str(cbvass);
  }
  funasslist  = bzla->fun_assignments;
  cfunasslist = bzla->clone->fun_assignments;
  for (funass = funasslist->first, cfunass = cfunasslist->first; funass;
       funass = funass->next, cfunass = cfunass->next)
  {
    assert(cfunass);
    assert(funass->size == cfunass->size);
    bzla_ass_get_fun_indices_values(funass, &indices, &values, funass->size);
    bzla_ass_get_fun_indices_values(
        cfunass, &cindices, &cvalues, cfunass->size);
    for (i = 0; i < funass->size; i++)
    {
      assert(!strcmp(indices[i], cindices[i]));
      assert(!strcmp(values[i], cvalues[i]));
    }
    funass->cloned_indices = cindices;
    funass->cloned_values  = cvalues;
  }
  bzla_chkclone(bzla, bzla->clone);
#endif
}

#ifndef NDEBUG
#define BZLA_CLONED_EXP(exp)                                                  \
  ((bzla->clone ? BZLA_EXPORT_BOOLECTOR_NODE(                                 \
        bzla_node_is_inverted(exp)                                            \
            ? bzla_node_invert(BZLA_PEEK_STACK(bzla->clone->nodes_id_table,   \
                                               bzla_node_real_addr(exp)->id)) \
            : BZLA_PEEK_STACK(bzla->clone->nodes_id_table,                    \
                              bzla_node_real_addr(exp)->id))                  \
                : 0))

#else
#define BZLA_CLONED_EXP(exp) 0
#endif

/*------------------------------------------------------------------------*/

/* for internal use (parser), only */

void
boolector_set_bzla_id(Bzla *bzla, BoolectorNode *node, int32_t id)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN_EXT(exp, "%d", id);
  BZLA_ABORT(!bzla_node_is_bv_var(exp) && !bzla_node_is_uf_array(exp),
             "'exp' is neither BV/array variable nor UF");
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  bzla_node_set_bzla_id(bzla, exp, id);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(set_bzla_id, BZLA_CLONED_EXP(exp), id);
#endif
}

BzlaMsg *
boolector_get_bzla_msg(Bzla *bzla)
{
  BzlaMsg *res;
  /* do not trace, clutters the trace unnecessarily */
  res = bzla->msg;
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(get_bzla_msg);
#endif
  return res;
}

void
boolector_print_value_smt2(Bzla *bzla,
                           BoolectorNode *node,
                           char *symbol_str,
                           FILE *file)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN_EXT(exp, "%s", symbol_str);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT(
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments,
      "cannot retrieve model if input formula is not SAT");
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN),
             "model generation has not been enabled");
  BZLA_ABORT(bzla->quantifiers->count,
             "models are currently not supported with quantifiers");
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  bzla_print_value_smt2(bzla, exp, symbol_str, file);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(print_value_smt2, BZLA_CLONED_EXP(exp), symbol_str, file);
#endif
}

void
boolector_var_mark_bool(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_ARG_NULL(node);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);

  BzlaPtrHashBucket *b = bzla_hashptr_table_get(bzla->inputs, exp);
  assert(b);
  b->data.flag = true;
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(var_mark_bool, BZLA_CLONED_EXP(exp));
#endif
}

void
boolector_add_output(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_ARG_NULL(node);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_PUSH_STACK(bzla->outputs, bzla_node_copy(bzla, exp));
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(add_output, BZLA_CLONED_EXP(exp));
#endif
}

/*------------------------------------------------------------------------*/

Bzla *
boolector_new(void)
{
  char *trname;
  Bzla *bzla;

  bzla = bzla_new();
  if ((trname = getenv("BZLAAPITRACE"))) bzla_trapi_open_trace(bzla, trname);
  BZLA_TRAPI("");
  BZLA_TRAPI_RETURN_PTR(bzla);
  return bzla;
}

Bzla *
boolector_clone(Bzla *bzla)
{
  Bzla *clone;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  clone = bzla_clone(bzla);
  BZLA_TRAPI_RETURN_PTR(clone);
#ifndef NDEBUG
  if (bzla->clone)
  {
    Bzla *cshadow = boolector_clone(bzla->clone);
    bzla_chkclone(bzla->clone, cshadow);
    bzla_delete(cshadow);
  }
#endif
  return clone;
}

void
boolector_delete(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  if (bzla->close_apitrace == 1)
    fclose(bzla->apitrace);
  else if (bzla->close_apitrace == 2)
    pclose(bzla->apitrace);
#ifndef NDEBUG
  if (bzla->clone) boolector_delete(bzla->clone);
#endif
  bzla_delete(bzla);
}

void
boolector_set_term(Bzla *bzla, int32_t (*fun)(void *), void *state)
{
  BZLA_ABORT_ARG_NULL(bzla);
  bzla_set_term(bzla, fun, state);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(set_term, fun, state);
#endif
}

int32_t
boolector_terminate(Bzla *bzla)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  res = bzla_terminate(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_INT(res, terminate);
#endif
  return res;
}

void
boolector_set_abort(void (*fun)(const char *msg))
{
  bzla_abort_callback.abort_fun = abort_aux;
  bzla_abort_callback.cb_fun    = fun;
}

void
boolector_set_msg_prefix(Bzla *bzla, const char *prefix)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%s", prefix);
  bzla_set_msg_prefix(bzla, prefix);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(set_msg_prefix, prefix);
#endif
}

uint32_t
boolector_get_refs(Bzla *bzla)
{
  uint32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  res = bzla->external_refs;
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, get_refs);
#endif
  return res;
}

void
boolector_reset_time(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  bzla_reset_time(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(reset_time);
#endif
}

void
boolector_reset_stats(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  bzla_reset_stats(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(reset_stats);
#endif
}

void
boolector_print_stats(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  bzla_sat_print_stats(bzla_get_sat_mgr(bzla));
  bzla_print_stats(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(print_stats);
#endif
}

void
boolector_set_trapi(Bzla *bzla, FILE *apitrace)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(bzla->apitrace, "API trace already set");
  bzla->apitrace = apitrace;
}

FILE *
boolector_get_trapi(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  return bzla->apitrace;
}

/*------------------------------------------------------------------------*/

void
boolector_push(Bzla *bzla, uint32_t level)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u", level);
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
             "incremental usage has not been enabled");

  if (level == 0) return;

  uint32_t i;
  for (i = 0; i < level; i++)
  {
    BZLA_PUSH_STACK(bzla->assertions_trail, BZLA_COUNT_STACK(bzla->assertions));
  }
  bzla->num_push_pop++;
}

void
boolector_pop(Bzla *bzla, uint32_t level)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u", level);
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
             "incremental usage has not been enabled");
  BZLA_ABORT(level > BZLA_COUNT_STACK(bzla->assertions_trail),
             "can not pop more levels (%u) than created via push (%u).",
             level,
             BZLA_COUNT_STACK(bzla->assertions_trail));

  if (level == 0) return;

  uint32_t i, pos;
  BzlaNode *cur;

  for (i = 0, pos = 0; i < level; i++)
    pos = BZLA_POP_STACK(bzla->assertions_trail);

  while (BZLA_COUNT_STACK(bzla->assertions) > pos)
  {
    cur = BZLA_POP_STACK(bzla->assertions);
    bzla_hashint_table_remove(bzla->assertions_cache, bzla_node_get_id(cur));
    bzla_node_release(bzla, cur);
  }
  bzla->num_push_pop++;
}

/*------------------------------------------------------------------------*/

void
boolector_assert(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(bzla_node_bv_get_width(bzla, exp) != 1,
             "'exp' must have bit-width one");
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_real_addr(exp)->sort_id),
             "'exp' must have bit-width one");
  BZLA_ABORT(bzla_node_real_addr(exp)->parameterized,
             "assertion must not be parameterized");

  /* all assertions at a context level > 0 are internally handled as
   * assumptions. */
  if (BZLA_COUNT_STACK(bzla->assertions_trail) > 0)
  {
    int32_t id = bzla_node_get_id(exp);
    if (!bzla_hashint_table_contains(bzla->assertions_cache, id))
    {
      BZLA_PUSH_STACK(bzla->assertions, bzla_node_copy(bzla, exp));
      bzla_hashint_table_add(bzla->assertions_cache, id);
    }
  }
  else
    bzla_assert_exp(bzla, exp);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(assert, BZLA_CLONED_EXP(exp));
#endif
}

void
boolector_assume(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
             "incremental usage has not been enabled");
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_real_addr(exp)->sort_id),
             "'exp' must have bit-width one");
  BZLA_ABORT(bzla_node_real_addr(exp)->parameterized,
             "assumption must not be parameterized");
  BZLA_PUSH_STACK(bzla->failed_assumptions, bzla_node_copy(bzla, exp));
  bzla_assume_exp(bzla, exp);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(assume, BZLA_CLONED_EXP(exp));
#endif
}

bool
boolector_failed(Bzla *bzla, BoolectorNode *node)
{
  bool res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(bzla->last_sat_result != BZLA_RESULT_UNSAT,
             "cannot check failed assumptions if input formula is not UNSAT");
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
             "incremental usage has not been enabled");
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(bzla_node_bv_get_width(bzla, exp) != 1,
             "'exp' must have bit-width one");
  BZLA_ABORT(!bzla_is_assumption_exp(bzla, exp), "'exp' must be an assumption");
  res = bzla_failed_exp(bzla, exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, failed, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

BoolectorNode **
boolector_get_failed_assumptions(Bzla *bzla)
{
  BoolectorNode **res;
  BzlaNodePtrStack failed;
  BzlaNode *fass;
  uint32_t i;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(bzla->last_sat_result != BZLA_RESULT_UNSAT,
             "cannot check failed assumptions if input formula is not UNSAT");

  BZLA_INIT_STACK(bzla->mm, failed);
  for (i = 0; i < BZLA_COUNT_STACK(bzla->failed_assumptions); i++)
  {
    fass = BZLA_PEEK_STACK(bzla->failed_assumptions, i);
    if (!fass) continue;
    assert(bzla_hashptr_table_get(bzla->orig_assumptions, fass));
    if (bzla_failed_exp(bzla, fass))
      BZLA_PUSH_STACK(failed, fass);
    else
      bzla_node_release(bzla, fass);
  }
  BZLA_PUSH_STACK(failed, NULL);
  BZLA_RELEASE_STACK(bzla->failed_assumptions);
  bzla->failed_assumptions = failed;
  res                      = (BoolectorNode **) bzla->failed_assumptions.start;
#ifndef NDEBUG
  if (bzla->clone)
  {
    BoolectorNode **cloneres;
    cloneres = boolector_get_failed_assumptions(bzla->clone);
    for (i = 0; res[i] != NULL; i++)
      bzla_chkclone_exp(bzla,
                        bzla->clone,
                        BZLA_IMPORT_BOOLECTOR_NODE(res[i]),
                        BZLA_IMPORT_BOOLECTOR_NODE(cloneres[i]));
    bzla_chkclone(bzla, bzla->clone);
  }
#endif
  return res;
}

void
boolector_fixate_assumptions(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  BZLA_ABORT(
      !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
      "incremental usage has not been enabled, no assumptions available");
  bzla_fixate_assumptions(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(fixate_assumptions);
#endif
}

void
boolector_reset_assumptions(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  BZLA_ABORT(
      !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
      "incremental usage has not been enabled, no assumptions available");
  bzla_reset_assumptions(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(reset_assumptions);
#endif
}

/*------------------------------------------------------------------------*/

int32_t
boolector_sat(Bzla *bzla)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL)
                 && bzla->bzla_sat_bzla_called > 0,
             "incremental usage has not been enabled."
             "'boolector_sat' may only be called once");
  res = bzla_check_sat(bzla, -1, -1);
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_INT(res, sat);
#endif
  return res;
}

int32_t
boolector_limited_sat(Bzla *bzla, int32_t lod_limit, int32_t sat_limit)
{
  int32_t res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%d %d", lod_limit, sat_limit);
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL)
                 && bzla->bzla_sat_bzla_called > 0,
             "incremental usage has not been enabled."
             "'boolector_limited_sat' may only be called once");
  res = bzla_check_sat(bzla, lod_limit, sat_limit);
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_INT(res, limited_sat, lod_limit, sat_limit);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

int32_t
boolector_simplify(Bzla *bzla)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");

  res = bzla_simplify(bzla);
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_INT(res, simplify);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

void
boolector_set_sat_solver(Bzla *bzla, const char *solver)
{
  BzlaPtrHashBucket *b;
  uint32_t sat_engine, oldval;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%s", solver);
  BZLA_ABORT_ARG_NULL(solver);
  BZLA_ABORT(
      bzla->bzla_sat_bzla_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");

  sat_engine = BZLA_SAT_ENGINE_DFLT;
  oldval     = bzla_opt_get(bzla, BZLA_OPT_SAT_ENGINE);

  if ((b = bzla_hashptr_table_get(bzla->options[BZLA_OPT_SAT_ENGINE].options,
                                  solver)))
  {
    sat_engine = ((BzlaOptHelp *) b->data.as_ptr)->val;
  }
  else
    BZLA_ABORT(1, "invalid sat engine '%s' selected", solver);

  if (false
#ifndef BZLA_USE_LINGELING
      || sat_engine == BZLA_SAT_ENGINE_LINGELING
#endif
#ifndef BZLA_USE_CADICAL
      || sat_engine == BZLA_SAT_ENGINE_CADICAL
#endif
#ifndef BZLA_USE_MINISAT
      || sat_engine == BZLA_SAT_ENGINE_MINISAT
#endif
#ifndef BZLA_USE_PICOSAT
      || sat_engine == BZLA_SAT_ENGINE_PICOSAT
#endif
#ifndef BZLA_USE_CMS
      || sat_engine == BZLA_SAT_ENGINE_CMS
#endif
  )
  {
    BZLA_WARN(true,
              "SAT solver %s not compiled in, using %s",
              g_bzla_se_name[sat_engine],
              g_bzla_se_name[oldval]);
    sat_engine = oldval;
  }

  bzla_opt_set(bzla, BZLA_OPT_SAT_ENGINE, sat_engine);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(set_sat_solver, solver);
#endif
}

/*------------------------------------------------------------------------*/

void
boolector_set_opt(Bzla *bzla, BzlaOption opt, uint32_t val)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s %u", opt, bzla_opt_get_lng(bzla, opt), val);
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  BZLA_ABORT(
      val < bzla_opt_get_min(bzla, opt) || val > bzla_opt_get_max(bzla, opt),
      "invalid option value '%u' for option '%s'",
      val,
      bzla_opt_get_lng(bzla, opt));

  if (val)
  {
    if (opt == BZLA_OPT_INCREMENTAL)
    {
      BZLA_ABORT(bzla->bzla_sat_bzla_called > 0,
                 "enabling/disabling incremental usage must be done "
                 "before calling 'bitwuzla_check_sat'");
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_UCOPT),
                 "incremental solving cannot be enabled "
                 "if unconstrained optimization is enabled");
    }
    else if (opt == BZLA_OPT_UCOPT)
    {
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN),
                 "Unconstrained optimization cannot be enabled "
                 "if model generation is enabled");
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
                 "Unconstrained optimization cannot be enabled "
                 "in incremental mode");
    }
    else if (opt == BZLA_OPT_FUN_DUAL_PROP)
    {
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_FUN_JUST),
                 "enabling multiple optimization techniques is not allowed");
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_NONDESTR_SUBST),
                 "Non-destructive substitution is not supported with dual "
                 "propagation");
    }
    else if (opt == BZLA_OPT_FUN_JUST)
    {
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP),
                 "enabling multiple optimization techniques is not allowed");
    }
    else if (opt == BZLA_OPT_NONDESTR_SUBST)
    {
      BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP),
                 "Non-destructive substitution is not supported with dual "
                 "propagation");
    }
  }

  uint32_t oldval = bzla_opt_get(bzla, opt);

  if (opt == BZLA_OPT_SAT_ENGINE)
  {
    if (false
#ifndef BZLA_USE_LINGELING
        || val == BZLA_SAT_ENGINE_LINGELING
#endif
#ifndef BZLA_USE_CADICAL
        || val == BZLA_SAT_ENGINE_CADICAL
#endif
#ifndef BZLA_USE_MINISAT
        || val == BZLA_SAT_ENGINE_MINISAT
#endif
#ifndef BZLA_USE_PICOSAT
        || val == BZLA_SAT_ENGINE_PICOSAT
#endif
#ifndef BZLA_USE_CMS
        || val == BZLA_SAT_ENGINE_CMS
#endif
    )
    {
      BZLA_WARN(true,
                "SAT solver %s not compiled in, using %s",
                g_bzla_se_name[val],
                g_bzla_se_name[oldval]);
      val = oldval;
    }
  }
#ifndef BZLA_USE_LINGELING
  if (opt == BZLA_OPT_SAT_ENGINE_LGL_FORK)
  {
    val = oldval;
    BZLA_MSG(bzla->msg,
             1,
             "SAT solver Lingeling not compiled in, will not set option "
             "to clone/fork Lingeling");
  }
#endif

  if (opt == BZLA_OPT_REWRITE_LEVEL)
  {
    BZLA_ABORT(
        BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
        "setting rewrite level must be done before creating expressions");
  }

  bzla_opt_set(bzla, opt, val);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(set_opt, opt, val);
#endif
}

uint32_t
boolector_get_opt(Bzla *bzla, BzlaOption opt)
{
  uint32_t res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get(bzla, opt);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, get_opt, opt);
#endif
  return res;
}

uint32_t
boolector_get_opt_min(Bzla *bzla, BzlaOption opt)
{
  uint32_t res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get_min(bzla, opt);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, get_opt_min, opt);
#endif
  return res;
}

uint32_t
boolector_get_opt_max(Bzla *bzla, BzlaOption opt)
{
  uint32_t res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get_max(bzla, opt);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, get_opt_max, opt);
#endif
  return res;
}

uint32_t
boolector_get_opt_dflt(Bzla *bzla, BzlaOption opt)
{
  uint32_t res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get_dflt(bzla, opt);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, get_opt_dflt, opt);
#endif
  return res;
}

const char *
boolector_get_opt_lng(Bzla *bzla, BzlaOption opt)
{
  const char *res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get_lng(bzla, opt);
  BZLA_TRAPI_RETURN_STR(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_STR(res, get_opt_lng, opt);
#endif
  return res;
}

const char *
boolector_get_opt_shrt(Bzla *bzla, BzlaOption opt)
{
  const char *res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get_shrt(bzla, opt);
  BZLA_TRAPI_RETURN_STR(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_STR(res, get_opt_shrt, opt);
#endif
  return res;
}

const char *
boolector_get_opt_desc(Bzla *bzla, BzlaOption opt)
{
  const char *res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_get_desc(bzla, opt);
  BZLA_TRAPI_RETURN_STR(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_STR(res, get_opt_desc, opt);
#endif
  return res;
}

bool
boolector_has_opt(Bzla *bzla, BzlaOption opt)
{
  bool res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  res = bzla_opt_is_valid(bzla, opt);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, next_opt, opt);
#endif
  return res;
}

BzlaOption
boolector_first_opt(Bzla *bzla)
{
  BzlaOption res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  res = bzla_opt_first(bzla);
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, first_opt);
#endif
  return res;
}

BzlaOption
boolector_next_opt(Bzla *bzla, BzlaOption opt)
{
  BzlaOption res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %s", opt, bzla_opt_get_lng(bzla, opt));
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option");
  res = bzla_opt_next(bzla, opt);
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, next_opt, opt);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_copy(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_copy(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, copy, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

void
boolector_release(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
#ifndef NDEBUG
  BoolectorNode *cexp = BZLA_CLONED_EXP(exp);
#endif
  assert(bzla_node_real_addr(exp)->ext_refs);
  bzla_node_dec_ext_ref_counter(bzla, exp);
  bzla_node_release(bzla, exp);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(release, cexp);
#endif
}

void
boolector_release_all(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  bzla_release_all_ext_refs(bzla);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(release_all);
#endif
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_true(Bzla *bzla)
{
  BzlaNode *res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  res = bzla_exp_true(bzla);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, true);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_false(Bzla *bzla)
{
  BzlaNode *res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");
  res = bzla_exp_false(bzla);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, false);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_implies(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT(bzla_node_bv_get_width(bzla, e0) != 1
                 || bzla_node_bv_get_width(bzla, e1) != 1,
             "bit-width of 'e0' and 'e1' must be 1");
  res = bzla_exp_implies(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, implies, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_iff(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT(bzla_node_bv_get_width(bzla, e0) != 1
                 || bzla_node_bv_get_width(bzla, e1) != 1,
             "bit-width of 'e0' and 'e1' must not be unequal to 1");
  res = bzla_exp_iff(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, iff, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_eq(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT(bzla_node_get_sort_id(e0) != bzla_node_get_sort_id(e1)
                 || bzla_node_real_addr(e0)->is_array
                        != bzla_node_real_addr(e1)->is_array,
             "nodes must have equal sorts");
  BZLA_ABORT(bzla_sort_is_fun(bzla, bzla_node_get_sort_id(e0))
                 && (bzla_node_real_addr(e0)->parameterized
                     || bzla_node_real_addr(e1)->parameterized),
             "parameterized function equalities not supported");
  res = bzla_exp_eq(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, eq, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ne(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT(bzla_node_get_sort_id(e0) != bzla_node_get_sort_id(e1),
             "nodes must have equal sorts");
  BZLA_ABORT(bzla_sort_is_fun(bzla, bzla_node_get_sort_id(e0))
                 && (bzla_node_real_addr(e0)->parameterized
                     || bzla_node_real_addr(e1)->parameterized),
             "parameterized function equalities not supported");
  res = bzla_exp_ne(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ne, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_const(Bzla *bzla, const char *bits)
{
  BzlaNode *res;
  BzlaBitVector *bv;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%s", bits);
  BZLA_ABORT_ARG_NULL(bits);
  BZLA_ABORT(*bits == '\0', "'bits' must not be empty");
  bv  = bzla_bv_char_to_bv(bzla->mm, (char *) bits);
  res = bzla_exp_bv_const(bzla, bv);
  bzla_node_inc_ext_ref_counter(bzla, res);
  bzla_bv_free(bzla->mm, bv);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, const, bits);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_constd(Bzla *bzla, BoolectorSort sort, const char *str)
{
  uint32_t w;
  BzlaNode *res;
  BzlaBitVector *bv;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT " %s", sort, str);
  BZLA_ABORT_ARG_NULL(str);
  BZLA_ABORT(*str == '\0', "'str' must not be empty");

  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  w = bzla_sort_bv_get_width(bzla, s);
  BZLA_ABORT(!bzla_util_check_dec_to_bv(bzla->mm, str, w),
             "'%s' does not fit into a bit-vector of size %u",
             str,
             w);
  bv  = bzla_bv_constd(bzla->mm, str, w);
  res = bzla_exp_bv_const(bzla, bv);
  assert(bzla_node_get_sort_id(res) == s);
  bzla_bv_free(bzla->mm, bv);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, constd, sort, str);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_consth(Bzla *bzla, BoolectorSort sort, const char *str)
{
  uint32_t w;
  BzlaNode *res;
  BzlaBitVector *bv;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%s", str);
  BZLA_ABORT_ARG_NULL(str);
  BZLA_ABORT(*str == '\0', "'str' must not be empty");

  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  w = bzla_sort_bv_get_width(bzla, s);
  BZLA_ABORT(!bzla_util_check_hex_to_bv(bzla->mm, str, w),
             "'%s' does not fit into a bit-vector of size %u",
             str,
             w);
  bv  = bzla_bv_consth(bzla->mm, str, w);
  res = bzla_exp_bv_const(bzla, bv);
  assert(bzla_node_get_sort_id(res) == s);
  bzla_bv_free(bzla->mm, bv);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, consth, sort, str);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

bool
boolector_is_bv_const_zero(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_is_bv_const_zero(bzla, exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bv_const_zero, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_bv_const_one(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_is_bv_const_one(bzla, exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bv_const_one, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_bv_const_ones(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_is_bv_const_ones(bzla, exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bv_const_ones, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_bv_const_max_signed(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_is_bv_const_max_signed(bzla, exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bv_const_max_signed, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_bv_const_min_signed(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_is_bv_const_min_signed(bzla, exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bv_const_min_signed, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_zero(Bzla *bzla, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_zero(bzla, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, zero, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ones(Bzla *bzla, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_ones(bzla, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ones, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_one(Bzla *bzla, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_one(bzla, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, one, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_min_signed(Bzla *bzla, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_min_signed(bzla, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, min_signed, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_max_signed(Bzla *bzla, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_max_signed(bzla, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, max_signed, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_unsigned_int(Bzla *bzla, uint32_t u, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u " BZLA_TRAPI_SORT_FMT, u, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_unsigned(bzla, u, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, unsigned_int, u, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_int(Bzla *bzla, int32_t i, BoolectorSort sort)
{
  BzlaNode *res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%d " BZLA_TRAPI_SORT_FMT, i, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  res = bzla_exp_bv_int(bzla, i, s);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, int, i, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

/* Remove unique symbol prefix and return start address of original symbol
 * without prefix. */
static const char *
remove_unique_symbol_prefix(Bzla *bzla, const char *symbol)
{
  if (symbol)
  {
    size_t len    = strlen(symbol);
    size_t offset = 5 + bzla_util_num_digits(bzla->num_push_pop);
    if (len > offset && !strncmp(symbol, "BZLA_", 5) && symbol[offset] == '@')
    {
      return symbol + offset + 1;
    }
  }
  return symbol;
}

/* Create symbol that is unique in the current scope. Prefix symbols with
 * BZLA_<num_push_pop>@<symbol> to make them unique in the current context. */
static char *
mk_unique_symbol_aux(BzlaMemMgr *mm, uint32_t num_push_pop, const char *symbol)
{
  char *symb;
  size_t len;
  if (num_push_pop)
  {
    len = strlen(symbol) + 1;
    len += strlen("BZLA_@");
    len += bzla_util_num_digits(num_push_pop);
    BZLA_CNEWN(mm, symb, len);
    sprintf(symb, "BZLA_%u@%s", num_push_pop, symbol);
  }
  else
  {
    symb = bzla_mem_strdup(mm, symbol);
  }
  return symb;
}

static char *
mk_unique_symbol(Bzla *bzla, const char *symbol)
{
  char *res = mk_unique_symbol_aux(bzla->mm, bzla->num_push_pop, symbol);
  assert(!symbol || !strcmp(symbol, remove_unique_symbol_prefix(bzla, res)));
  return res;
}

BoolectorNode *
boolector_var(Bzla *bzla, BoolectorSort sort, const char *symbol)
{
  BZLA_ABORT_ARG_NULL(bzla);

  BzlaNode *res;
  char *symb;
  BzlaSortId s;

  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  symb = mk_unique_symbol(bzla, symbol);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT " %s", sort, bzla, symb);
  BZLA_ABORT(symb && bzla_hashptr_table_get(bzla->symbols, (char *) symb),
             "symbol '%s' is already in use in the current context",
             symb);
  res = bzla_exp_var(bzla, s, symb);
  bzla_mem_freestr(bzla->mm, symb);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
  (void) bzla_hashptr_table_add(bzla->inputs, bzla_node_copy(bzla, res));
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, var, sort, symbol);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_array(Bzla *bzla, BoolectorSort sort, const char *symbol)
{
  BZLA_ABORT_ARG_NULL(bzla);

  BzlaNode *res;
  char *symb;
  BzlaSortId s;

  symb = mk_unique_symbol(bzla, symbol);
  s    = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(
      !bzla_sort_is_fun(bzla, s)
          || bzla_sort_tuple_get_arity(bzla, bzla_sort_fun_get_domain(bzla, s))
                 != 1,
      "'sort' is not an array sort");
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT " %s", sort, bzla, symb);
  BZLA_ABORT(symb && bzla_hashptr_table_get(bzla->symbols, symb),
             "symbol '%s' is already in use in the current context",
             symb);
  res = bzla_exp_array(bzla, s, symb);
  bzla_mem_freestr(bzla->mm, symb);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
  (void) bzla_hashptr_table_add(bzla->inputs, bzla_node_copy(bzla, res));
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, array, sort, symbol);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_const_array(Bzla *bzla, BoolectorSort sort, BoolectorNode *value)
{
  BZLA_ABORT_ARG_NULL(bzla);

  BzlaNode *res, *val;
  BzlaSortId s;

  val = BZLA_IMPORT_BOOLECTOR_NODE(value);

  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(
      !bzla_sort_is_fun(bzla, s)
          || bzla_sort_tuple_get_arity(bzla, bzla_sort_fun_get_domain(bzla, s))
                 != 1,
      "'sort' is not an array sort");
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT BZLA_TRAPI_NODE_FMT,
             sort,
             bzla,
             BZLA_TRAPI_NODE_ID(val));
  BZLA_ABORT_ARG_NULL(val);
  BZLA_ABORT_REFS_NOT_POS(val);
  BZLA_ABORT_BZLA_MISMATCH(bzla, val);
  BZLA_ABORT_IS_NOT_BV(val);
  BZLA_ABORT(bzla_node_get_sort_id(val) != bzla_sort_array_get_element(bzla, s),
             "sort of 'value' does not match element sort of array");

  res = bzla_exp_const_array(bzla, s, val);

  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);

#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, const_array, sort, value);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_uf(Bzla *bzla, BoolectorSort sort, const char *symbol)
{
  BZLA_ABORT_ARG_NULL(bzla);

  BzlaNode *res;
  BzlaSortId s;
  char *symb;

  symb = mk_unique_symbol(bzla, symbol);
  s    = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT "%s", sort, bzla, symb);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_fun(bzla, s),
             "%ssort%s%s%s%s must be a function sort",
             symbol ? "" : "'",
             symbol ? "" : "'",
             symbol ? " '" : "",
             symbol ? symbol : "",
             symbol ? "'" : "");
  BZLA_ABORT(symb && bzla_hashptr_table_get(bzla->symbols, symb),
             "symbol '%s' is already in use in the current context",
             symb);

  res = bzla_exp_uf(bzla, s, symb);
  bzla_mem_freestr(bzla->mm, symb);
  assert(bzla_node_is_regular(res));
  bzla_node_inc_ext_ref_counter(bzla, res);
  (void) bzla_hashptr_table_add(bzla->inputs, bzla_node_copy(bzla, res));
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, uf, sort, symbol);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_bv_not(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_not(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_not, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_neg(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_neg(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_neg, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_redor(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_redor(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_redor, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_redxor(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_redxor(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_redxor, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_redand(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_redand(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_redand, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_slice(Bzla *bzla,
                   BoolectorNode *node,
                   uint32_t upper,
                   uint32_t lower)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN_EXT(exp, "%u %u", upper, lower);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(upper < lower, "'upper' must not be < 'lower'");
  BZLA_ABORT((uint32_t) upper >= bzla_node_bv_get_width(bzla, exp),
             "'upper' must not be >= width of 'exp'");
  res = bzla_exp_bv_slice(bzla, exp, upper, lower);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_slice, BZLA_CLONED_EXP(exp), upper, lower);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_uext(Bzla *bzla, BoolectorNode *node, uint32_t width)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN_EXT(exp, "%u", width);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(width > UINT32_MAX - bzla_node_bv_get_width(bzla, exp),
             "extending 'exp' (width %u) by %u bits exceeds maximum "
             "bit-width of %u",
             bzla_node_bv_get_width(bzla, exp),
             width,
             UINT32_MAX);
  res = bzla_exp_bv_uext(bzla, exp, width);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_uext, BZLA_CLONED_EXP(exp), width);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_sext(Bzla *bzla, BoolectorNode *node, uint32_t width)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN_EXT(exp, "%u", width);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(width > UINT32_MAX - bzla_node_bv_get_width(bzla, exp),
             "extending 'exp' (width %u) by %u bits exceeds maximum "
             "bit-width of %u",
             bzla_node_bv_get_width(bzla, exp),
             width,
             UINT32_MAX);
  res = bzla_exp_bv_sext(bzla, exp, width);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_sext, BZLA_CLONED_EXP(exp), width);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_bv_xor(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_xor(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, bv_xor, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_xnor(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_xnor(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, xnor, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_and(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_and(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, and, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_nand(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_nand(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, nand, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_or(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_or(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, or, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_nor(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_nor(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, nor, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_add(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_add(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, add, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_uaddo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_uaddo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, uaddo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_saddo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_saddo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, saddo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_mul(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_mul(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, mul, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_umulo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_umulo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, umulo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_smulo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_smulo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, smulo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ult(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_ult(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ult, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_slt(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_slt(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, slt, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ulte(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_ulte(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ulte, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_slte(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_slte(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, slte, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ugt(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_ugt(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ugt, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sgt(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_sgt(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sgt, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ugte(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_ugte(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ugte, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sgte(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_sgte(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sgte, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sll(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width0, width1;
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);

  width0 = bzla_node_bv_get_width(bzla, e0);
  width1 = bzla_node_bv_get_width(bzla, e1);
  if (width0 == width1)
  {
    res = bzla_exp_bv_sll(bzla, e0, e1);
  }
  else
  {
    BZLA_ABORT(!bzla_util_is_power_of_2(width0),
               "bit-width of 'e0' must be a power of 2");
    BZLA_ABORT(bzla_util_log_2(width0) != width1,
               "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    BzlaNode *tmp_e1 = bzla_exp_bv_uext(bzla, e1, width0 - width1);
    res              = bzla_exp_bv_sll(bzla, e0, tmp_e1);
    bzla_node_release(bzla, tmp_e1);
  }
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sll, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_srl(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width0, width1;
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  width0 = bzla_node_bv_get_width(bzla, e0);
  width1 = bzla_node_bv_get_width(bzla, e1);
  if (width0 == width1)
  {
    res = bzla_exp_bv_srl(bzla, e0, e1);
  }
  else
  {
    BZLA_ABORT(!bzla_util_is_power_of_2(width0),
               "bit-width of 'e0' must be a power of 2");
    BZLA_ABORT(bzla_util_log_2(width0) != width1,
               "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    BzlaNode *tmp_e1 = bzla_exp_bv_uext(bzla, e1, width0 - width1);
    res              = bzla_exp_bv_srl(bzla, e0, tmp_e1);
    bzla_node_release(bzla, tmp_e1);
  }
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, srl, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sra(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width0, width1;
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  width0 = bzla_node_bv_get_width(bzla, e0);
  width1 = bzla_node_bv_get_width(bzla, e1);
  if (width0 == width1)
  {
    res = bzla_exp_bv_sra(bzla, e0, e1);
  }
  else
  {
    BZLA_ABORT(!bzla_util_is_power_of_2(width0),
               "bit-width of 'e0' must be a power of 2");
    BZLA_ABORT(bzla_util_log_2(width0) != width1,
               "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    BzlaNode *tmp_e1 = bzla_exp_bv_uext(bzla, e1, width0 - width1);
    res              = bzla_exp_bv_sra(bzla, e0, tmp_e1);
    bzla_node_release(bzla, tmp_e1);
  }
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sra, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_rol(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width0, width1;
  BzlaNode *e0, *e1, *res;

  BZLA_ABORT_ARG_NULL(bzla);
  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  width0 = bzla_node_bv_get_width(bzla, e0);
  width1 = bzla_node_bv_get_width(bzla, e1);
  if (width0 == width1)
  {
    res = bzla_exp_bv_rol(bzla, e0, e1);
  }
  else
  {
    BZLA_ABORT(!bzla_util_is_power_of_2(width0),
               "bit-width of 'e0' must be a power of 2");
    BZLA_ABORT(bzla_util_log_2(width0) != width1,
               "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    BzlaNode *tmp_e1 = bzla_exp_bv_uext(bzla, e1, width0 - width1);
    res              = bzla_exp_bv_rol(bzla, e0, tmp_e1);
    bzla_node_release(bzla, tmp_e1);
  }
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, rol, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ror(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  uint32_t width0, width1;
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  width0 = bzla_node_bv_get_width(bzla, e0);
  width1 = bzla_node_bv_get_width(bzla, e1);
  if (width0 == width1)
  {
    res = bzla_exp_bv_ror(bzla, e0, e1);
  }
  else
  {
    BZLA_ABORT(!bzla_util_is_power_of_2(width0),
               "bit-width of 'e0' must be a power of 2");
    BZLA_ABORT(bzla_util_log_2(width0) != width1,
               "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
    BzlaNode *tmp_e1 = bzla_exp_bv_uext(bzla, e1, width0 - width1);
    res              = bzla_exp_bv_ror(bzla, e0, tmp_e1);
    bzla_node_release(bzla, tmp_e1);
  }
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ror, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_roli(Bzla *bzla, BoolectorNode *n, uint32_t nbits)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(n);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN_EXT(exp, "%u", nbits);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_roli(bzla, exp, nbits);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, roli, BZLA_CLONED_EXP(exp), nbits);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_rori(Bzla *bzla, BoolectorNode *n, uint32_t nbits)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(n);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN_EXT(exp, "%u", nbits);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  res = bzla_exp_bv_rori(bzla, exp, nbits);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, rori, BZLA_CLONED_EXP(exp), nbits);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sub(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_sub(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sub, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_usubo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_usubo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, usubo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_ssubo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_ssubo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, ssubo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_udiv(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_udiv(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, udiv, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sdiv(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_sdiv(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sdiv, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_sdivo(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_sdivo(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, sdivo, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_urem(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_urem(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, urem, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_srem(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_srem(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, srem, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_smod(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT_SORT_MISMATCH(e0, e1);
  res = bzla_exp_bv_smod(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, smod, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_concat(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  BzlaNode *e0, *e1, *res;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  BZLA_ABORT_IS_NOT_BV(e0);
  BZLA_ABORT_IS_NOT_BV(e1);
  BZLA_ABORT(bzla_node_bv_get_width(bzla, e0)
                 > UINT32_MAX - bzla_node_bv_get_width(bzla, e1),
             "bit-width of result is too large");
  res = bzla_exp_bv_concat(bzla, e0, e1);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, concat, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_repeat(Bzla *bzla, BoolectorNode *node, uint32_t n)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN_EXT(exp, "%u", n);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  BZLA_ABORT(((uint32_t)(UINT32_MAX / n)) < bzla_node_bv_get_width(bzla, exp),
             "resulting bit-width of 'repeat' too large");
  res = bzla_exp_bv_repeat(bzla, exp, n);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, repeat, BZLA_CLONED_EXP(exp), n);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_read(Bzla *bzla, BoolectorNode *n_array, BoolectorNode *n_index)
{
  BzlaNode *e_array, *e_index, *res;

  e_array = BZLA_IMPORT_BOOLECTOR_NODE(n_array);
  e_index = BZLA_IMPORT_BOOLECTOR_NODE(n_index);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e_array);
  BZLA_ABORT_ARG_NULL(e_index);
  BZLA_TRAPI_BINFUN(e_array, e_index);
  BZLA_ABORT_REFS_NOT_POS(e_array);
  BZLA_ABORT_REFS_NOT_POS(e_index);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_array);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_index);
  BZLA_ABORT_IS_NOT_ARRAY(e_array);
  BZLA_ABORT_IS_NOT_BV(e_index);
  BZLA_ABORT(
      bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(e_array))
          != bzla_node_get_sort_id(e_index),
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  res = bzla_exp_read(bzla, e_array, e_index);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(
      res, read, BZLA_CLONED_EXP(e_array), BZLA_CLONED_EXP(e_index));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_write(Bzla *bzla,
                BoolectorNode *n_array,
                BoolectorNode *n_index,
                BoolectorNode *n_value)
{
  BzlaNode *e_array, *e_index, *e_value;
  BzlaNode *res;

  e_array = BZLA_IMPORT_BOOLECTOR_NODE(n_array);
  e_index = BZLA_IMPORT_BOOLECTOR_NODE(n_index);
  e_value = BZLA_IMPORT_BOOLECTOR_NODE(n_value);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e_array);
  BZLA_ABORT_ARG_NULL(e_index);
  BZLA_ABORT_ARG_NULL(e_value);
  BZLA_TRAPI_TERFUN(e_array, e_index, e_value);
  BZLA_ABORT_REFS_NOT_POS(e_array);
  BZLA_ABORT_REFS_NOT_POS(e_index);
  BZLA_ABORT_REFS_NOT_POS(e_value);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_array);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_index);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_value);
  BZLA_ABORT_IS_NOT_ARRAY(e_array);
  BZLA_ABORT_IS_NOT_BV(e_index);
  BZLA_ABORT_IS_NOT_BV(e_value);
  BZLA_ABORT(
      bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(e_array))
          != bzla_node_get_sort_id(e_index),
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  BZLA_ABORT(
      bzla_sort_array_get_element(bzla, bzla_node_get_sort_id(e_array))
          != bzla_node_get_sort_id(e_value),
      "element bit-width of 'e_array' and bit-width of 'e_value' must be "
      "equal");
  res = bzla_exp_write(bzla, e_array, e_index, e_value);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res,
                        write,
                        BZLA_CLONED_EXP(e_array),
                        BZLA_CLONED_EXP(e_index),
                        BZLA_CLONED_EXP(e_value));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_cond(Bzla *bzla,
               BoolectorNode *n_cond,
               BoolectorNode *n_then,
               BoolectorNode *n_else)
{
  BzlaNode *e_cond, *e_if, *e_else;
  BzlaNode *res;

  e_cond = BZLA_IMPORT_BOOLECTOR_NODE(n_cond);
  e_if   = BZLA_IMPORT_BOOLECTOR_NODE(n_then);
  e_else = BZLA_IMPORT_BOOLECTOR_NODE(n_else);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e_cond);
  BZLA_ABORT_ARG_NULL(e_if);
  BZLA_ABORT_ARG_NULL(e_else);
  BZLA_TRAPI_TERFUN(e_cond, e_if, e_else);
  BZLA_ABORT_REFS_NOT_POS(e_cond);
  BZLA_ABORT_REFS_NOT_POS(e_if);
  BZLA_ABORT_REFS_NOT_POS(e_else);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_cond);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_if);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_else);
  BZLA_ABORT_IS_NOT_BV(e_cond);
  BZLA_ABORT(bzla_node_bv_get_width(bzla, e_cond) != 1,
             "bit-width of 'e_cond' must be equal to 1");
  BZLA_ABORT(bzla_node_get_sort_id(e_if) != bzla_node_get_sort_id(e_else),
             "sorts of 'e_if' and 'e_else' branch must be equal");
  res = bzla_exp_cond(bzla, e_cond, e_if, e_else);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res,
                        cond,
                        BZLA_CLONED_EXP(e_cond),
                        BZLA_CLONED_EXP(e_if),
                        BZLA_CLONED_EXP(e_else));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_param(Bzla *bzla, BoolectorSort sort, const char *symbol)
{
  BZLA_ABORT_ARG_NULL(bzla);

  BzlaNode *res;
  char *symb;
  BzlaSortId s;

  symb = mk_unique_symbol(bzla, symbol);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT " %s", sort, bzla, symb);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, s), "'sort' is not a bit vector sort");
  BZLA_ABORT(symb && bzla_hashptr_table_get(bzla->symbols, symb),
             "symbol '%s' is already in use in the current context",
             symb);
  res = bzla_exp_param(bzla, s, symb);
  bzla_mem_freestr(bzla->mm, symb);
  bzla_node_inc_ext_ref_counter(bzla, res);

  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, param, sort, symbol);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_fun(Bzla *bzla,
              BoolectorNode **param_nodes,
              uint32_t paramc,
              BoolectorNode *node)
{
  uint32_t i;
  BzlaNode **params, *exp, *res;

  params = BZLA_IMPORT_BOOLECTOR_NODE_ARRAY(param_nodes);
  exp    = BZLA_IMPORT_BOOLECTOR_NODE(node);

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(params);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT(paramc < 1, "'paramc' must not be < 1");

  BZLA_TRAPI_PRINT("%s %p %u ", __FUNCTION__ + 10, bzla, paramc);
  for (i = 0; i < paramc; i++)
  {
    BZLA_ABORT(!params[i] || !bzla_node_is_param(params[i]),
               "'params[%u]' is not a parameter",
               i);
    BZLA_ABORT(bzla_node_param_is_bound(params[i]),
               "'params[%u]' already bound");
    BZLA_ABORT_REFS_NOT_POS(params[i]);
    BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(params[i]));
  }
  BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(exp));
  BZLA_TRAPI_PRINT("\n");

  BZLA_ABORT(bzla_node_is_uf(bzla_simplify_exp(bzla, exp)),
             "expected bit vector term as function body");
  res = bzla_exp_fun(bzla, params, paramc, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; bzla->clone && i < paramc; i++)
    cparam_nodes[i] = BZLA_CLONED_EXP(params[i]);
  BZLA_CHKCLONE_RES_PTR(res, fun, cparam_nodes, paramc, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_apply(Bzla *bzla,
                BoolectorNode **arg_nodes,
                uint32_t argc,
                BoolectorNode *n_fun)
{
  uint32_t i;
  int32_t fcheck;
  BzlaNode **args, *e_fun, *res;

  args  = BZLA_IMPORT_BOOLECTOR_NODE_ARRAY(arg_nodes);
  e_fun = BZLA_IMPORT_BOOLECTOR_NODE(n_fun);

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e_fun);

  BZLA_ABORT_REFS_NOT_POS(e_fun);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_fun);

  BZLA_TRAPI_PRINT("%s %p %u ", __FUNCTION__ + 10, bzla, argc);
  for (i = 0; i < argc; i++)
    BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(args[i]));
  BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(e_fun));
  BZLA_TRAPI_PRINT("\n");

  BZLA_ABORT(!bzla_sort_is_fun(bzla, bzla_node_get_sort_id(e_fun)),
             "'e_fun' must be a function");
  BZLA_ABORT((uint32_t) argc != bzla_node_fun_get_arity(bzla, e_fun),
             "number of arguments must be equal to the number of parameters in "
             "'e_fun'");
  BZLA_ABORT(argc < 1, "'argc' must not be < 1");
  BZLA_ABORT(argc >= 1 && !args, "no arguments given but argc defined > 0");
  fcheck = bzla_fun_sort_check(bzla, args, argc, e_fun);
  BZLA_ABORT(fcheck >= 0, "invalid argument given at position %d", fcheck);
  res = bzla_exp_apply_n(bzla, e_fun, args, argc);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; bzla->clone && i < argc; i++)
    carg_nodes[i] = BZLA_CLONED_EXP(args[i]);
  BZLA_CHKCLONE_RES_PTR(res, apply, carg_nodes, argc, BZLA_CLONED_EXP(e_fun));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_inc(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);

  res = bzla_exp_bv_inc(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, inc, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_dec(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);

  res = bzla_exp_bv_dec(bzla, exp);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, dec, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

static bool
params_distinct(Bzla *bzla, BzlaNode *params[], uint32_t paramc)
{
  bool res                = true;
  BzlaIntHashTable *cache = bzla_hashint_table_new(bzla->mm);
  for (uint32_t i = 0; i < paramc; i++)
  {
    if (bzla_hashint_table_contains(cache, bzla_node_get_id(params[i])))
    {
      res = false;
      break;
    }
    bzla_hashint_table_add(cache, bzla_node_get_id(params[i]));
  }
  bzla_hashint_table_delete(cache);
  return res;
}

BoolectorNode *
boolector_forall(Bzla *bzla,
                 BoolectorNode *param_nodes[],
                 uint32_t paramc,
                 BoolectorNode *body_node)
{
  uint32_t i;
  BzlaNode **params, *body, *res;

  params = BZLA_IMPORT_BOOLECTOR_NODE_ARRAY(param_nodes);
  body   = BZLA_IMPORT_BOOLECTOR_NODE(body_node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(params);
  BZLA_ABORT_ARG_NULL(body);

  BZLA_TRAPI_PRINT("%s %p %u ", __FUNCTION__ + 10, bzla, paramc);
  for (i = 0; i < paramc; i++)
  {
    BZLA_ABORT(!params[i] || !bzla_node_is_param(params[i]),
               "'params[%u]' is not a parameter",
               i);
    BZLA_ABORT(bzla_node_param_is_bound(params[i]),
               "'params[%u]' already bound");
    BZLA_ABORT_REFS_NOT_POS(params[i]);
    BZLA_ABORT_BZLA_MISMATCH(bzla, params[i]);
    BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(params[i]));
  }
  BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(body));
  BZLA_TRAPI_PRINT("\n");
  BZLA_ABORT(!params_distinct(bzla, params, paramc),
             "given parameters are not distinct");

  BZLA_ABORT_REFS_NOT_POS(body);
  BZLA_ABORT_BZLA_MISMATCH(bzla, body);
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_real_addr(body)->sort_id),
             "body of forall must be bit width 1, but has "
             "%u instead",
             bzla_node_bv_get_width(bzla, body));

  res = bzla_exp_forall_n(bzla, params, paramc, body);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; bzla->clone && i < paramc; i++)
    cparam_nodes[i] = BZLA_CLONED_EXP(params[i]);
  BZLA_CHKCLONE_RES_PTR(
      res, forall, cparam_nodes, paramc, BZLA_CLONED_EXP(body));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_exists(Bzla *bzla,
                 BoolectorNode *param_nodes[],
                 uint32_t paramc,
                 BoolectorNode *body_node)
{
  uint32_t i;
  BzlaNode **params, *body, *res;

  params = BZLA_IMPORT_BOOLECTOR_NODE_ARRAY(param_nodes);
  body   = BZLA_IMPORT_BOOLECTOR_NODE(body_node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(params);
  BZLA_ABORT_ARG_NULL(body);

  BZLA_TRAPI_PRINT("%s %p %u ", __FUNCTION__ + 10, bzla, paramc);
  for (i = 0; i < paramc; i++)
  {
    BZLA_ABORT(!params[i] || !bzla_node_is_param(params[i]),
               "'params[%u]' is not a parameter",
               i);
    BZLA_ABORT(bzla_node_param_is_bound(params[i]),
               "'params[%u]' already bound");
    BZLA_ABORT_REFS_NOT_POS(params[i]);
    BZLA_ABORT_BZLA_MISMATCH(bzla, params[i]);
    BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(params[i]));
  }
  BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(body));
  BZLA_TRAPI_PRINT("\n");
  BZLA_ABORT(!params_distinct(bzla, params, paramc),
             "given parameters are not distinct");

  BZLA_ABORT_REFS_NOT_POS(body);
  BZLA_ABORT_BZLA_MISMATCH(bzla, body);
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_real_addr(body)->sort_id),
             "body of exists must be bit width 1, but has "
             "%u instead",
             bzla_node_bv_get_width(bzla, body));

  res = bzla_exp_exists_n(bzla, params, paramc, body);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; bzla->clone && i < paramc; i++)
    cparam_nodes[i] = BZLA_CLONED_EXP(params[i]);
  BZLA_CHKCLONE_RES_PTR(
      res, exists, cparam_nodes, paramc, BZLA_CLONED_EXP(body));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

Bzla *
boolector_get_btor(BoolectorNode *node)
{
  BzlaNode *exp, *real_exp;
  Bzla *bzla;
  BZLA_ABORT_ARG_NULL(node);
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_REFS_NOT_POS(exp);
  real_exp = bzla_node_real_addr(exp);
  bzla     = real_exp->bzla;
  BZLA_TRAPI_UNFUN(exp);
  BZLA_TRAPI_RETURN_PTR(bzla);
#ifndef NDEBUG
  if (bzla->clone)
  {
    Bzla *clone = boolector_get_btor(BZLA_CLONED_EXP(exp));
    assert(clone == bzla->clone);
    bzla_chkclone(bzla, bzla->clone);
  }
#endif
  return bzla;
}

int32_t
boolector_get_node_id(Bzla *bzla, BoolectorNode *node)
{
  int32_t res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(node);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_get_id(bzla_node_real_addr(exp));
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_INT(res, get_node_id, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

BoolectorSort
boolector_get_sort(Bzla *bzla, const BoolectorNode *node)
{
  BzlaNode *exp;
  BzlaSortId res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(node);
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_TRAPI_UNFUN(exp);
  res = bzla_node_get_sort_id(exp);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, get_sort, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

BoolectorSort
boolector_fun_get_domain_sort(Bzla *bzla, const BoolectorNode *node)
{
  BzlaNode *exp;
  BzlaSortId res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(node);
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT(!bzla_node_is_fun(bzla_simplify_exp(bzla, exp)),
             "node must be a function node");
  BZLA_TRAPI_UNFUN(exp);
  res =
      ((BzlaFunSort) bzla_sort_get_by_id(bzla, bzla_node_get_sort_id(exp))->fun)
          .domain->id;
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, fun_get_domain_sort, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

BoolectorSort
boolector_fun_get_codomain_sort(Bzla *bzla, const BoolectorNode *node)
{
  BzlaNode *exp;
  BzlaSortId res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(node);
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT(!bzla_node_is_fun(bzla_simplify_exp(bzla, exp)),
             "node must be a function node");
  BZLA_TRAPI_UNFUN(exp);
  res =
      ((BzlaFunSort) bzla_sort_get_by_id(bzla, bzla_node_get_sort_id(exp))->fun)
          .codomain->id;
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, fun_get_codomain_sort, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_match_node_by_id(Bzla *bzla, int32_t id)
{
  BzlaNode *res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(id <= 0, "node id must be > 0");
  BZLA_TRAPI("%d", id);
  res = bzla_node_match_by_id(bzla, id);
  BZLA_ABORT(
      !res,
      "invalid node id '%d', no matching node in given Boolector instance",
      id);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, match_node_by_id, id);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_match_node_by_symbol(Bzla *bzla, const char *symbol)
{
  char *symb;
  uint32_t i;
  BzlaNode *res;
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(symbol);
  BZLA_TRAPI("%s", symbol);
  for (i = 0, res = 0; !res && i <= bzla->num_push_pop; i++)
  {
    symb = mk_unique_symbol_aux(bzla->mm, i, symbol);
    res  = bzla_node_match_by_symbol(bzla, symb);
    bzla_mem_freestr(bzla->mm, symb);
  }
  BZLA_ABORT(!res,
             "invalid symbol'%s', no matching node in given Boolector instance",
             symbol);
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, match_node_by_symbol, symbol);
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

BoolectorNode *
boolector_match_node(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *res, *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_match(bzla, exp);
  BZLA_ABORT(!res,
             "invalid node, no matching node in given Boolector instance");
  bzla_node_inc_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_NODE(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_PTR(res, match_node, BZLA_CLONED_EXP(exp));
#endif
  return BZLA_EXPORT_BOOLECTOR_NODE(res);
}

/*------------------------------------------------------------------------*/

const char *
boolector_get_symbol(Bzla *bzla, BoolectorNode *node)
{
  const char *res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = remove_unique_symbol_prefix(bzla, bzla_node_get_symbol(bzla, exp));
  BZLA_TRAPI_RETURN_STR(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_STR(res, get_symbol, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

void
boolector_set_symbol(Bzla *bzla, BoolectorNode *node, const char *symbol)
{
  char *symb;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_ARG_NULL(symbol);
  BZLA_TRAPI_UNFUN_EXT(exp, "%s", symbol);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  symb = mk_unique_symbol(bzla, symbol);

  if (bzla_hashptr_table_get(bzla->symbols, symb))
  {
    BZLA_WARN(
        true, "symbol %s already defined, ignoring setting symbol", symbol);
  }
  else
  {
    bzla_node_set_symbol(bzla, exp, symb);
  }
  bzla_mem_freestr(bzla->mm, symb);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(set_symbol, BZLA_CLONED_EXP(exp), symbol);
#endif
}

uint32_t
boolector_bv_get_width(Bzla *bzla, BoolectorNode *node)
{
  uint32_t res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  if (bzla_sort_is_fun(bzla, bzla_node_get_sort_id(exp)))
    res = bzla_node_fun_get_width(bzla, exp);
  else
    res = bzla_node_bv_get_width(bzla, exp);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, bv_get_width, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

uint32_t
boolector_array_get_index_width(Bzla *bzla, BoolectorNode *n_array)
{
  uint32_t res;
  BzlaNode *e_array;

  e_array = BZLA_IMPORT_BOOLECTOR_NODE(n_array);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e_array);
  BZLA_TRAPI_UNFUN(e_array);
  BZLA_ABORT_REFS_NOT_POS(e_array);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_array);
  BZLA_ABORT_IS_NOT_ARRAY(e_array);
  BZLA_ABORT(bzla_node_fun_get_arity(bzla, e_array) > 1,
             "'n_array' is a function with arity > 1");
  res = bzla_node_array_get_index_width(bzla, e_array);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, array_get_index_width, BZLA_CLONED_EXP(e_array));
#endif
  return res;
}

const char *
boolector_get_bits(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp, *real;
  BzlaBVAss *bvass;
  char *bits;
  const char *res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_ARG_NULL(node);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT(!bzla_node_is_bv_const(exp), "argument is not a constant node");
  real = bzla_node_real_addr(exp);
  /* representations of bits of const nodes are maintained analogously
   * to bv assignment strings */
  if (!bzla_node_is_inverted(exp))
    bits = bzla_bv_to_char(bzla->mm, bzla_node_bv_const_get_bits(exp));
  else
    bits = bzla_bv_to_char(bzla->mm, bzla_node_bv_const_get_invbits(real));
  bvass = bzla_ass_new_bv(bzla->bv_assignments, bits);
  bzla_mem_freestr(bzla->mm, bits);
  res = bzla_ass_get_bv_str(bvass);
  BZLA_TRAPI_RETURN_PTR(res);
#ifndef NDEBUG
  if (bzla->clone)
  {
    const char *cloneres =
        boolector_get_bits(bzla->clone, BZLA_CLONED_EXP(exp));
    assert(!strcmp(cloneres, res));
    bvass->cloned_assignment = cloneres;
    bzla_chkclone(bzla, bzla->clone);
  }
#endif
  return res;
}

void
boolector_free_bits(Bzla *bzla, const char *bits)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%p", bits);
  BZLA_ABORT_ARG_NULL(bits);
#ifndef NDEBUG
  char *cass;
  cass = (char *) bzla_ass_get_bv((const char *) bits)->cloned_assignment;
#endif
  bzla_ass_release_bv(bzla->bv_assignments, bits);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(free_bits, cass);
#endif
}

uint32_t
boolector_fun_get_arity(Bzla *bzla, BoolectorNode *node)
{
  uint32_t res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT(!bzla_node_is_fun(bzla_simplify_exp(bzla, exp)),
             "given expression is not a function node");
  res = bzla_node_fun_get_arity(bzla, exp);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, fun_get_arity, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

bool
boolector_is_const(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  res = bzla_node_is_bv_const(exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_const, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_var(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;
  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_is_bv_var(bzla_simplify_exp(bzla, exp));
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_var, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_array(Bzla *bzla, BoolectorNode *node)
{
  bool res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_is_array(bzla_simplify_exp(bzla, exp));
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_array, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_array_var(Bzla *bzla, BoolectorNode *node)
{
  bool res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_is_uf_array(bzla_simplify_exp(bzla, exp));
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_array_var, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_param(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_is_param(bzla_simplify_exp(bzla, exp));
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_param, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_bound_param(Bzla *bzla, BoolectorNode *node)
{
  BzlaNode *exp;
  bool res;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT(!bzla_node_is_param(bzla_simplify_exp(bzla, exp)),
             "given expression is not a parameter node");
  res = bzla_node_param_is_bound(exp);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bound_param, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_uf(Bzla *bzla, BoolectorNode *node)
{
  bool res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_is_uf(bzla_simplify_exp(bzla, exp));
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_uf, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

bool
boolector_is_fun(Bzla *bzla, BoolectorNode *node)
{
  bool res;
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  res = bzla_node_is_fun(bzla_simplify_exp(bzla, exp));
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_fun, BZLA_CLONED_EXP(exp));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

int32_t
boolector_fun_sort_check(Bzla *bzla,
                         BoolectorNode **arg_nodes,
                         uint32_t argc,
                         BoolectorNode *n_fun)
{
  BzlaNode **args, *e_fun;
  uint32_t i;
  int32_t res;

  args  = BZLA_IMPORT_BOOLECTOR_NODE_ARRAY(arg_nodes);
  e_fun = BZLA_IMPORT_BOOLECTOR_NODE(n_fun);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e_fun);
  BZLA_ABORT(argc < 1, "'argc' must not be < 1");
  BZLA_ABORT(argc >= 1 && !args, "no arguments given but argc defined > 0");

  BZLA_TRAPI_PRINT("%s %p %u ", __FUNCTION__ + 10, bzla, argc);
  for (i = 0; i < argc; i++)
  {
    BZLA_ABORT_ARG_NULL(args[i]);
    BZLA_ABORT_REFS_NOT_POS(args[i]);
    BZLA_ABORT_BZLA_MISMATCH(bzla, args[i]);
    BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(args[i]));
  }
  BZLA_TRAPI_PRINT(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(e_fun));
  BZLA_TRAPI_PRINT("\n");

  res = bzla_fun_sort_check(bzla, args, argc, e_fun);
  BZLA_TRAPI_RETURN_INT(res);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; bzla->clone && i < argc; i++)
    carg_nodes[i] = BZLA_CLONED_EXP(args[i]);
  BZLA_CHKCLONE_RES_INT(
      res, fun_sort_check, carg_nodes, argc, BZLA_CLONED_EXP(e_fun));
#endif
  return res;
}

/*------------------------------------------------------------------------*/

const char *
boolector_bv_assignment(Bzla *bzla, BoolectorNode *node)
{
  char *ass;
  const char *res;
  BzlaNode *exp;
  BzlaBVAss *bvass;
  uint32_t opt;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments,
      "cannot retrieve model if input formula is not SAT");
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN),
             "model generation has not been enabled");
  BZLA_ABORT(bzla->quantifiers->count,
             "models are currently not supported with quantifiers");
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  BZLA_ABORT_IS_NOT_BV(exp);
  opt = bzla_opt_get(bzla, BZLA_OPT_OUTPUT_NUMBER_FORMAT);
  switch (opt)
  {
    case BZLA_OUTPUT_BASE_HEX:
      ass = bzla_bv_to_hex_char(bzla->mm, bzla_model_get_bv(bzla, exp));
      break;
    case BZLA_OUTPUT_BASE_DEC:
      ass = bzla_bv_to_dec_char(bzla->mm, bzla_model_get_bv(bzla, exp));
      break;
    default:
      assert(opt == BZLA_OUTPUT_BASE_BIN);
      ass = bzla_bv_to_char(bzla->mm, bzla_model_get_bv(bzla, exp));
  }
  bvass = bzla_ass_new_bv(bzla->bv_assignments, ass);
  bzla_mem_freestr(bzla->mm, ass);
  res = bzla_ass_get_bv_str(bvass);
  BZLA_TRAPI_RETURN_PTR(res);
#ifndef NDEBUG
  if (bzla->clone)
  {
    const char *cloneres =
        boolector_bv_assignment(bzla->clone, BZLA_CLONED_EXP(exp));
    assert(!strcmp(cloneres, res));
    bvass->cloned_assignment = cloneres;
    bzla_chkclone(bzla, bzla->clone);
  }
#endif
  return res;
}

void
boolector_free_bv_assignment(Bzla *bzla, const char *assignment)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%p", assignment);
  BZLA_ABORT_ARG_NULL(assignment);
#ifndef NDEBUG
  char *cass;
  cass = (char *) bzla_ass_get_bv((const char *) assignment)->cloned_assignment;
#endif
  bzla_ass_release_bv(bzla->bv_assignments, assignment);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(free_bv_assignment, cass);
#endif
}

static void
generate_fun_model_str(
    Bzla *bzla, BzlaNode *exp, char ***args, char ***values, uint32_t *size)
{
  assert(bzla);
  assert(exp);
  assert(args);
  assert(values);
  assert(size);
  assert(bzla_node_is_regular(exp));

  char *arg, *tmp, **bv;
  uint32_t i, j, len;
  BzlaPtrHashTableIterator it;
  const BzlaPtrHashTable *model;
  BzlaBitVector *value;
  BzlaBitVectorTuple *t;
  uint32_t opt;

  opt = bzla_opt_get(bzla, BZLA_OPT_OUTPUT_NUMBER_FORMAT);

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_node_is_fun(exp));

  model = bzla_model_get_fun_aux(bzla, bzla->bv_model, bzla->fun_model, exp);

  if ((bzla_node_is_lambda(exp) && bzla_node_fun_get_arity(bzla, exp) > 1)
      || !bzla->fun_model || !model)
  {
    *size = 0;
    return;
  }

  assert(model->count > 0);

  *size = model->count;
  BZLA_NEWN(bzla->mm, *args, *size);
  BZLA_NEWN(bzla->mm, *values, *size);

  i = 0;
  bzla_iter_hashptr_init(&it, (BzlaPtrHashTable *) model);
  while (bzla_iter_hashptr_has_next(&it))
  {
    value = (BzlaBitVector *) it.bucket->data.as_ptr;

    /* build assignment string for all arguments */
    t = (BzlaBitVectorTuple *) bzla_iter_hashptr_next(&it);
    if (t->arity)
    {
      BZLA_CNEWN(bzla->mm, bv, t->arity);
      len = t->arity;
      for (j = 0; j < t->arity; j++)
      {
        switch (opt)
        {
          case BZLA_OUTPUT_BASE_HEX:
            bv[j] = bzla_bv_to_hex_char(bzla->mm, t->bv[j]);
            break;
          case BZLA_OUTPUT_BASE_DEC:
            bv[j] = bzla_bv_to_dec_char(bzla->mm, t->bv[j]);
            break;
          default:
            assert(opt == BZLA_OUTPUT_BASE_BIN);
            bv[j] = bzla_bv_to_char(bzla->mm, t->bv[j]);
        }
        len += strlen(bv[j]);
      }
      BZLA_CNEWN(bzla->mm, arg, len);
      tmp = arg;
      strncpy(tmp, bv[0], len);
      len -= strlen(bv[0]);

      for (j = 1; j < t->arity; j++)
      {
        strncat(tmp, " ", len);
        len -= 1;
        strncat(tmp, bv[j], len);
        len -= strlen(bv[j]);
      }
      for (j = 0; j < t->arity; j++) bzla_mem_freestr(bzla->mm, bv[j]);
      BZLA_DELETEN(bzla->mm, bv, t->arity);
      len -= 1;
      assert(len == 0);
    }
    /* If argument tuple has arity 0, value represents the default value for
     * the function/array (constant arrays). */
    else
    {
      BZLA_CNEWN(bzla->mm, arg, 2);
      arg[0] = '*';
    }

    (*args)[i] = arg;
    switch (opt)
    {
      case BZLA_OUTPUT_BASE_HEX:
        (*values)[i] = (char *) bzla_bv_to_hex_char(bzla->mm, value);
        break;
      case BZLA_OUTPUT_BASE_DEC:
        (*values)[i] = (char *) bzla_bv_to_dec_char(bzla->mm, value);
        break;
      default:
        assert(opt == BZLA_OUTPUT_BASE_BIN);
        (*values)[i] = (char *) bzla_bv_to_char(bzla->mm, value);
    }
    i++;
  }
}

static void
fun_assignment(Bzla *bzla,
               BzlaNode *n,
               char ***args,
               char ***values,
               uint32_t *size,
               BzlaFunAss **ass)
{
  assert(bzla);
  assert(n);
  assert(args);
  assert(values);
  assert(size);
  assert(bzla_node_is_regular(n));

  uint32_t i;
  char **a = 0, **v = 0;

  *ass = 0;
  generate_fun_model_str(bzla, n, &a, &v, size);

  if (*size)
  {
    *ass = bzla_ass_new_fun(bzla->fun_assignments, a, v, *size);
    for (i = 0; i < *size; i++)
    {
      bzla_mem_freestr(bzla->mm, a[i]);
      bzla_mem_freestr(bzla->mm, v[i]);
    }
    bzla_mem_free(bzla->mm, a, *size * sizeof(*a));
    bzla_mem_free(bzla->mm, v, *size * sizeof(*v));
    bzla_ass_get_fun_indices_values(*ass, args, values, *size);
  }
}

void
boolector_array_assignment(Bzla *bzla,
                           BoolectorNode *n_array,
                           char ***indices,
                           char ***values,
                           uint32_t *size)
{
  BzlaNode *e_array;
  BzlaFunAss *ass;

  e_array = BZLA_IMPORT_BOOLECTOR_NODE(n_array);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments,
      "cannot retrieve model if input formula is not SAT");
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN),
             "model generation has not been enabled");
  BZLA_ABORT_ARG_NULL(e_array);
  BZLA_TRAPI_UNFUN(e_array);
  BZLA_ABORT_ARG_NULL(indices);
  BZLA_ABORT_ARG_NULL(values);
  BZLA_ABORT_ARG_NULL(size);
  BZLA_ABORT_REFS_NOT_POS(e_array);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_array);
  BZLA_ABORT_IS_NOT_ARRAY(e_array);

  fun_assignment(bzla, e_array, indices, values, size, &ass);

  /* special case: we treat out parameters as return values for btoruntrace */
  BZLA_TRAPI_RETURN("%p %p %u", *indices, *values, *size);

#ifndef NDEBUG
  if (bzla->clone)
  {
    char **cindices, **cvalues;
    uint32_t i, csize;
    boolector_array_assignment(
        bzla->clone, BZLA_CLONED_EXP(e_array), &cindices, &cvalues, &csize);
    assert(csize == *size);
    for (i = 0; i < *size; i++)
    {
      assert(!strcmp((*indices)[i], cindices[i]));
      assert(!strcmp((*values)[i], cvalues[i]));
    }
    if (ass)
    {
      assert(*size);
      ass->cloned_indices = cindices;
      ass->cloned_values  = cvalues;
    }
    bzla_chkclone(bzla, bzla->clone);
  }
#endif
}

void
boolector_free_array_assignment(Bzla *bzla,
                                char **indices,
                                char **values,
                                uint32_t size)
{
  BzlaFunAss *funass;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%p %p %u", indices, values, size);
  BZLA_ABORT(size && !indices, "size > 0 but 'indices' are zero");
  BZLA_ABORT(size && !values, "size > 0 but 'values' are zero");
  BZLA_ABORT(!size && indices, "non zero 'indices' but 'size == 0'");
  BZLA_ABORT(!size && values, "non zero 'values' but 'size == 0'");
  if (!size)
  {
    return;
  }

  funass =
      bzla_ass_get_fun((const char **) indices, (const char **) values, size);
  BZLA_ABORT(size != funass->size,
             "wrong size given, expected %u, but got %u",
             funass->size,
             size);
#ifndef NDEBUG
  char **cindices, **cvalues;
  cindices = funass->cloned_indices;
  cvalues  = funass->cloned_values;
#endif
  bzla_ass_release_fun(bzla->fun_assignments, indices, values, size);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(free_array_assignment, cindices, cvalues, size);
#endif
}

void
boolector_uf_assignment(Bzla *bzla,
                        BoolectorNode *n_uf,
                        char ***args,
                        char ***values,
                        uint32_t *size)
{
  BzlaNode *e_uf;
  BzlaFunAss *ass;

  e_uf = BZLA_IMPORT_BOOLECTOR_NODE(n_uf);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT(
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments,
      "cannot retrieve model if input formula is not SAT");
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN),
             "model generation has not been enabled");
  BZLA_ABORT_ARG_NULL(e_uf);
  BZLA_TRAPI_UNFUN(e_uf);
  BZLA_ABORT_ARG_NULL(args);
  BZLA_ABORT_ARG_NULL(values);
  BZLA_ABORT_ARG_NULL(size);
  BZLA_ABORT_REFS_NOT_POS(e_uf);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e_uf);
  BZLA_ABORT_IS_NOT_FUN(e_uf);

  fun_assignment(bzla, e_uf, args, values, size, &ass);

  /* special case: we treat out parameters as return values for btoruntrace */
  BZLA_TRAPI_RETURN("%p %p %u", *args, *values, *size);

#ifndef NDEBUG
  if (bzla->clone)
  {
    char **cargs, **cvalues;
    uint32_t i, csize;
    boolector_uf_assignment(
        bzla->clone, BZLA_CLONED_EXP(e_uf), &cargs, &cvalues, &csize);
    assert(csize == *size);
    for (i = 0; i < *size; i++)
    {
      assert(!strcmp((*args)[i], cargs[i]));
      assert(!strcmp((*values)[i], cvalues[i]));
    }
    if (ass)
    {
      assert(*size);
      ass->cloned_indices = cargs;
      ass->cloned_values  = cvalues;
    }
    bzla_chkclone(bzla, bzla->clone);
  }
#endif
}

void
boolector_free_uf_assignment(Bzla *bzla,
                             char **args,
                             char **values,
                             uint32_t size)
{
  BzlaFunAss *funass;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%p %p %u", args, values, size);
  BZLA_ABORT(size && !args, "size > 0 but 'args' are zero");
  BZLA_ABORT(size && !values, "size > 0 but 'values' are zero");
  BZLA_ABORT(!size && args, "non zero 'args' but 'size == 0'");
  BZLA_ABORT(!size && values, "non zero 'values' but 'size == 0'");
  funass = bzla_ass_get_fun((const char **) args, (const char **) values, size);
  BZLA_ABORT(size != funass->size,
             "wrong size given, expected %u, but got %u",
             funass->size,
             size);
#ifndef NDEBUG
  char **cargs, **cvalues;
  cargs   = funass->cloned_indices;
  cvalues = funass->cloned_values;
#endif
  bzla_ass_release_fun(bzla->fun_assignments, args, values, size);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(free_array_assignment, cargs, cvalues, size);
#endif
}

void
boolector_print_model(Bzla *bzla, char *format, FILE *file)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(format);
  BZLA_TRAPI("%s", format);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT(strcmp(format, "btor") && strcmp(format, "smt2"),
             "invalid model output format: %s",
             format);
  BZLA_ABORT(
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments,
      "cannot retrieve model if input formula is not SAT");
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN),
             "model generation has not been enabled");
  bzla_print_model(bzla, format, file);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(print_model, format, file);
#endif
}

/*------------------------------------------------------------------------*/

BoolectorSort
boolector_bool_sort(Bzla *bzla)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("");

  BzlaSortId res;
  res = bzla_sort_bool(bzla);
  inc_sort_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, bool_sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

BoolectorSort
boolector_bv_sort(Bzla *bzla, uint32_t width)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u", width);
  BZLA_ABORT(width == 0, "'width' must be > 0");

  BzlaSortId res;
  res = bzla_sort_bv(bzla, width);
  inc_sort_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, bv_sort, width);
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

BoolectorSort
boolector_fp_sort(Bzla *bzla, uint32_t ewidth, uint32_t swidth)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI("%u %u", ewidth, swidth);
  BZLA_ABORT(ewidth == 0, "'ewidth' must be > 0");
  BZLA_ABORT(swidth == 0, "'swidth' must be > 0");

  BzlaSortId res;
  res = bzla_sort_fp(bzla, ewidth, swidth);
  inc_sort_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, fp_sort, ewidth, swidth);
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

static BzlaSortId
boolector_tuple_sort(Bzla *bzla, BoolectorSort *sorts, size_t num_elements)
{
  BzlaSortId element_ids[num_elements];
  size_t i;
  for (i = 0; i < num_elements; i++)
    element_ids[i] = BZLA_IMPORT_BOOLECTOR_SORT(sorts[i]);
  return bzla_sort_tuple(bzla, element_ids, num_elements);
}

BoolectorSort
boolector_fun_sort(Bzla *bzla,
                   BoolectorSort domain[],
                   uint32_t arity,
                   BoolectorSort codomain)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(domain);
  BZLA_ABORT(arity <= 0, "'arity' must be > 0");

  uint32_t i;
  BzlaSortId res, tup, cos, s;

  BZLA_TRAPI_PRINT("%s %p ", __FUNCTION__ + 10, bzla);
  BZLA_TRAPI_PRINT(
      BZLA_TRAPI_SORT_FMT, BZLA_IMPORT_BOOLECTOR_SORT((domain[0])), bzla);
  for (i = 1; i < arity; i++)
    BZLA_TRAPI_PRINT(
        BZLA_TRAPI_SORT_FMT, BZLA_IMPORT_BOOLECTOR_SORT(domain[i]), bzla);
  BZLA_TRAPI_PRINT(
      BZLA_TRAPI_SORT_FMT, BZLA_IMPORT_BOOLECTOR_SORT(codomain), bzla);
  BZLA_TRAPI_PRINT("\n");

  for (i = 0; i < arity; i++)
  {
    s = BZLA_IMPORT_BOOLECTOR_SORT(domain[i]);
    BZLA_ABORT(!bzla_sort_is_valid(bzla, s),
               "'domain' sort at position %u is not a valid sort",
               i);
    BZLA_ABORT(!bzla_sort_is_bv(bzla, s) && !bzla_sort_is_bool(bzla, s),
               "'domain' sort at position %u must be a bool or bit vector sort",
               i);
  }
  cos = BZLA_IMPORT_BOOLECTOR_SORT(codomain);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, cos),
             "'codomain' sort is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, cos) && !bzla_sort_is_bool(bzla, cos),
             "'codomain' sort must be a bool or bit vector sort");

  tup = boolector_tuple_sort(bzla, domain, arity);

  res = bzla_sort_fun(bzla, tup, cos);
  bzla_sort_release(bzla, tup);
  inc_sort_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, fun_sort, domain, arity, codomain);
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

BoolectorSort
boolector_array_sort(Bzla *bzla, BoolectorSort index, BoolectorSort element)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(
      BZLA_TRAPI_SORT_FMT " " BZLA_TRAPI_SORT_FMT, index, bzla, element, bzla);

  BzlaSortId is, es, res;

  is = BZLA_IMPORT_BOOLECTOR_SORT(index);
  es = BZLA_IMPORT_BOOLECTOR_SORT(element);

  BZLA_ABORT(!bzla_sort_is_valid(bzla, is), "'index' sort is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, is), "'index' is not a bit vector sort");
  BZLA_ABORT(!bzla_sort_is_valid(bzla, es),
             "'element' sort is not a valid sort");
  BZLA_ABORT(!bzla_sort_is_bv(bzla, es), "'element' is not a bit vector sort");

  res = bzla_sort_array(bzla, is, es);
  inc_sort_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, array_sort, index, element);
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

BoolectorSort
boolector_copy_sort(Bzla *bzla, BoolectorSort sort)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, BZLA_IMPORT_BOOLECTOR_SORT(sort), bzla);

  BzlaSortId s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  BzlaSortId res = bzla_sort_copy(bzla, s);
  inc_sort_ext_ref_counter(bzla, res);
  BZLA_TRAPI_RETURN_SORT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_SORT(res, copy_sort, sort);
#endif
  return BZLA_EXPORT_BOOLECTOR_SORT(res);
}

void
boolector_release_sort(Bzla *bzla, BoolectorSort sort)
{
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, BZLA_IMPORT_BOOLECTOR_SORT(sort), bzla);

  BzlaSortId s = BZLA_IMPORT_BOOLECTOR_SORT(sort);
  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");
  dec_sort_ext_ref_counter(bzla, s);
  bzla_sort_release(bzla, s);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(release_sort, sort);
#endif
}

bool
boolector_is_equal_sort(Bzla *bzla, BoolectorNode *n0, BoolectorNode *n1)
{
  bool res;
  BzlaNode *e0, *e1;

  e0 = BZLA_IMPORT_BOOLECTOR_NODE(n0);
  e1 = BZLA_IMPORT_BOOLECTOR_NODE(n1);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(e0);
  BZLA_ABORT_ARG_NULL(e1);
  BZLA_TRAPI_BINFUN(e0, e1);
  BZLA_ABORT_REFS_NOT_POS(e0);
  BZLA_ABORT_REFS_NOT_POS(e1);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e0);
  BZLA_ABORT_BZLA_MISMATCH(bzla, e1);
  res = bzla_node_get_sort_id(e0) == bzla_node_get_sort_id(e1);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(
      res, is_equal_sort, BZLA_CLONED_EXP(e0), BZLA_CLONED_EXP(e1));
#endif
  return res;
}

bool
boolector_is_array_sort(Bzla *bzla, BoolectorSort sort)
{
  bool res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);

  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");

  res = bzla_sort_is_array(bzla, s);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_array_sort, sort);
#endif
  return res;
}

bool
boolector_is_bv_sort(Bzla *bzla, BoolectorSort sort)
{
  bool res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);

  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");

  res = bzla_sort_is_bv(bzla, s);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_bv_sort, sort);
#endif
  return res;
}

bool
boolector_is_fun_sort(Bzla *bzla, BoolectorSort sort)
{
  bool res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);

  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");

  res = bzla_sort_is_fun(bzla, s);
  BZLA_TRAPI_RETURN_BOOL(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_BOOL(res, is_fun_sort, sort);
#endif
  return res;
}

uint32_t
boolector_bitvec_sort_get_width(Bzla *bzla, BoolectorSort sort)
{
  uint32_t res;
  BzlaSortId s;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_TRAPI(BZLA_TRAPI_SORT_FMT, sort, bzla);
  s = BZLA_IMPORT_BOOLECTOR_SORT(sort);

  BZLA_ABORT(!bzla_sort_is_valid(bzla, s), "'sort' is not a valid sort");

  res = bzla_sort_bv_get_width(bzla, s);
  BZLA_TRAPI_RETURN_UINT(res);
#ifndef NDEBUG
  BZLA_CHKCLONE_RES_UINT(res, bitvec_sort_get_width, sort);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

/* Note: no need to trace parse function calls!! */

int32_t
boolector_parse(Bzla *bzla,
                FILE *infile,
                const char *infile_name,
                FILE *outfile,
                char **error_msg,
                int32_t *status,
                bool *parsed_smt2)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(infile);
  BZLA_ABORT_ARG_NULL(infile_name);
  BZLA_ABORT_ARG_NULL(outfile);
  BZLA_ABORT_ARG_NULL(error_msg);
  BZLA_ABORT_ARG_NULL(status);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  res = bzla_parse(
      bzla, infile, infile_name, outfile, error_msg, status, parsed_smt2);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int32_t
boolector_parse_btor(Bzla *bzla,
                     FILE *infile,
                     const char *infile_name,
                     FILE *outfile,
                     char **error_msg,
                     int32_t *status)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(infile);
  BZLA_ABORT_ARG_NULL(infile_name);
  BZLA_ABORT_ARG_NULL(outfile);
  BZLA_ABORT_ARG_NULL(error_msg);
  BZLA_ABORT_ARG_NULL(status);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  res = bzla_parse_btor(bzla, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int32_t
boolector_parse_btor2(Bzla *bzla,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      int32_t *status)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(infile);
  BZLA_ABORT_ARG_NULL(infile_name);
  BZLA_ABORT_ARG_NULL(outfile);
  BZLA_ABORT_ARG_NULL(error_msg);
  BZLA_ABORT_ARG_NULL(status);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  res = bzla_parse_btor2(bzla, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int32_t
boolector_parse_smt1(Bzla *bzla,
                     FILE *infile,
                     const char *infile_name,
                     FILE *outfile,
                     char **error_msg,
                     int32_t *status)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(infile);
  BZLA_ABORT_ARG_NULL(infile_name);
  BZLA_ABORT_ARG_NULL(outfile);
  BZLA_ABORT_ARG_NULL(error_msg);
  BZLA_ABORT_ARG_NULL(status);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  res = bzla_parse_smt1(bzla, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

int32_t
boolector_parse_smt2(Bzla *bzla,
                     FILE *infile,
                     const char *infile_name,
                     FILE *outfile,
                     char **error_msg,
                     int32_t *status)
{
  int32_t res;

  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(infile);
  BZLA_ABORT_ARG_NULL(infile_name);
  BZLA_ABORT_ARG_NULL(outfile);
  BZLA_ABORT_ARG_NULL(error_msg);
  BZLA_ABORT_ARG_NULL(status);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  res = bzla_parse_smt2(bzla, infile, infile_name, outfile, error_msg, status);
  /* shadow clone can not shadow boolector_parse* (parser uses API calls only,
   * hence all API calls issued while parsing are already shadowed and the
   * shadow clone already maintains the parsed formula) */
  return res;
}

/*------------------------------------------------------------------------*/

void
boolector_dump_bzla_node(Bzla *bzla, FILE *file, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  bzla_dumpbtor_dump_node(bzla, file, bzla_simplify_exp(bzla, exp));
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(dump_bzla_node, stdout, BZLA_CLONED_EXP(exp));
#endif
}

void
boolector_dump_btor(Bzla *bzla, FILE *file)
{
  BZLA_TRAPI("");
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT(!bzla_dumpbtor_can_be_dumped(bzla),
             "formula cannot be dumped in BTOR format as it does "
             "not support uninterpreted functions yet.");
  BZLA_WARN(bzla->assumptions->count > 0,
            "dumping in incremental mode only captures the current state "
            "of the input formula without assumptions");
  bzla_dumpbtor_dump(bzla, file, 1);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(dump_btor, stdout);
#endif
}

#if 0
void
boolector_dump_btor2 (Bzla * bzla, FILE * file)
{
  BZLA_TRAPI ("");
  BZLA_ABORT_ARG_NULL (bzla);
  BZLA_ABORT_ARG_NULL (file);
  bzla_dumpbtor_dump (bzla, file, 2);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES (dump_btor, file);
#endif
}
#endif

void
boolector_dump_smt2_node(Bzla *bzla, FILE *file, BoolectorNode *node)
{
  BzlaNode *exp;

  exp = BZLA_IMPORT_BOOLECTOR_NODE(node);
  BZLA_TRAPI_UNFUN(exp);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT_ARG_NULL(exp);
  BZLA_ABORT_REFS_NOT_POS(exp);
  BZLA_ABORT_BZLA_MISMATCH(bzla, exp);
  bzla_dumpsmt_dump_node(bzla, file, bzla_simplify_exp(bzla, exp), 0);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(dump_smt2_node, stdout, BZLA_CLONED_EXP(exp));
#endif
}

void
boolector_dump_smt2(Bzla *bzla, FILE *file)
{
  BZLA_TRAPI("");
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_WARN(bzla->assumptions->count > 0,
            "dumping in incremental mode only captures the current state "
            "of the input formula without assumptions");
  bzla_dumpsmt_dump(bzla, file);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(dump_smt2, stdout);
#endif
}

void
boolector_dump_aiger_ascii(Bzla *bzla, FILE *file, bool merge_roots)
{
  BZLA_TRAPI("%d", merge_roots);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT(bzla->lambdas->count > 0 || bzla->ufs->count > 0,
             "dumping to ASCII AIGER is supported for QF_BV only");
  BZLA_WARN(bzla->assumptions->count > 0,
            "dumping in incremental mode only captures the current state "
            "of the input formula without assumptions");
  bzla_dumpaig_dump(bzla, false, file, merge_roots);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(dump_aiger_ascii, stdout, merge_roots);
#endif
}

void
boolector_dump_aiger_binary(Bzla *bzla, FILE *file, bool merge_roots)
{
  BZLA_TRAPI("%d", merge_roots);
  BZLA_ABORT_ARG_NULL(bzla);
  BZLA_ABORT_ARG_NULL(file);
  BZLA_ABORT(bzla->lambdas->count > 0 || bzla->ufs->count > 0,
             "dumping to binary AIGER is supported for QF_BV only");
  BZLA_WARN(bzla->assumptions->count > 0,
            "dumping in incremental mode only captures the current state "
            "of the input formula without assumptions");
  bzla_dumpaig_dump(bzla, true, file, merge_roots);
#ifndef NDEBUG
  BZLA_CHKCLONE_NORES(dump_aiger_binary, stdout, merge_roots);
#endif
}

/*------------------------------------------------------------------------*/

const char *
boolector_copyright(Bzla *bzla)
{
  /* do not trace, not necessary */
  BZLA_ABORT_ARG_NULL(bzla);
  return "This software is\n"
         "Copyright (c) 2007-2009 Robert Brummayer\n"
         "Copyright (c) 2007-2018 Armin Biere\n"
         "Copyright (c) 2012-2019 Aina Niemetz, Mathias Preiner\n"
#ifdef BZLA_USE_LINGELING
         "\n"
         "This software is linked against Lingeling\n"
         "Copyright (c) 2010-2018 Armin Biere\n"
#endif
#ifdef BZLA_USE_PICOSAT
         "\n"
         "This software is linked against PicoSAT\n"
         "Copyright (c) 2006-2016 Armin Biere\n"
#endif
#ifdef BZLA_USE_MINISAT
         "\n"
         "This software is linked against MiniSAT\n"
         "Copyright (c) 2003-2013, Niklas Een, Niklas Sorensson\n"
#endif
#ifdef BZLA_USE_CADICAL
         "\n"
         "This software is linked against CaDiCaL\n"
         "Copyright (c) 2016-2019 Armin Biere\n"
#endif
         "";
}

const char *
boolector_version(Bzla *bzla)
{
  /* do not trace, not necessary */
  BZLA_ABORT_ARG_NULL(bzla);
  return bzla_version(bzla);
}

const char *
boolector_git_id(Bzla *bzla)
{
  /* do not trace, not necessary */
  BZLA_ABORT_ARG_NULL(bzla);
  return bzla_git_id(bzla);
}
