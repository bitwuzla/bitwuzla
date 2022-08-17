/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlapreprocess.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlasubst.h"
#include "preprocess/bzlaack.h"
#include "preprocess/bzlader.h"
#include "preprocess/bzlaelimapplies.h"
#include "preprocess/bzlaelimites.h"
#include "preprocess/bzlaelimslices.h"
#include "preprocess/bzlaembed.h"
#include "preprocess/bzlaextract.h"
#include "preprocess/bzlamerge.h"
#include "preprocess/bzlanormadd.h"
#include "preprocess/bzlaunconstrained.h"
#include "preprocess/bzlavarsubst.h"
#ifndef BZLA_DO_NOT_PROCESS_SKELETON
#include "preprocess/bzlaskel.h"
#endif
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

int32_t
bzla_simplify(Bzla *bzla)
{
  assert(bzla);

  BzlaSolverResult result;
  uint32_t rounds;
  double start, delta;
#ifndef BZLA_DO_NOT_PROCESS_SKELETON
  uint32_t skelrounds = 0;
#endif

  rounds = 0;
  start  = bzla_util_time_stamp();

  if (bzla->valid_assignments) bzla_reset_incremental_usage(bzla);

  if (bzla->inconsistent) goto DONE;

  /* empty varsubst_constraints table if variable substitution was disabled
   * after adding variable substitution constraints (they are still in
   * unsynthesized_constraints).
   */
  if (bzla_opt_get(bzla, BZLA_OPT_PP_VAR_SUBST) == 0
      && bzla->varsubst_constraints->count > 0)
  {
    bzla_delete_varsubst_constraints(bzla);
    bzla->varsubst_constraints =
        bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    // TODO: check if this is still valid, and if this is the case also clear
    //       var_substitutions and var_rhs?
  }

  do
  {
    rounds++;
    assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
    assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
    assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1)
    {
      if (bzla_opt_get(bzla, BZLA_OPT_PP_VAR_SUBST))
      {
        bzla_substitute_var_exps(bzla);

        if (bzla->inconsistent)
        {
          BZLALOG(1, "formula inconsistent after variable substitution");
          break;
        }

        if (bzla->varsubst_constraints->count)
          break;  // TODO (ma): continue instead of break?
      }

      while (bzla->embedded_constraints->count)
      {
        bzla_process_embedded_constraints(bzla);

        if (bzla->inconsistent)
        {
          BZLALOG(1,
                  "formula inconsistent after embedded constraint processing");
          break;
        }
      }

      if (bzla->varsubst_constraints->count) continue;
    }

    if (bzla_opt_get(bzla, BZLA_OPT_PP_ELIMINATE_EXTRACTS)
        && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
        && !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL))
    {
      bzla_eliminate_slices_on_bv_vars(bzla);
      if (bzla->inconsistent)
      {
        BZLALOG(1, "formula inconsistent after slice elimination");
        break;
      }

      if (bzla->varsubst_constraints->count
          || bzla->embedded_constraints->count)
        continue;
    }

#ifndef BZLA_DO_NOT_PROCESS_SKELETON
    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_PP_SKELETON_PREPROC))
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        bzla_process_skeleton(bzla);
        if (bzla->inconsistent)
        {
          BZLALOG(1, "formula inconsistent after skeleton preprocessing");
          break;
        }
      }

      if (bzla->varsubst_constraints->count
          || bzla->embedded_constraints->count)
        continue;
    }
#endif

    if (bzla->varsubst_constraints->count || bzla->embedded_constraints->count)
      continue;

    if (bzla_opt_get(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)
        && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
        && !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL)
        && !bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS))
    {
      bzla_optimize_unconstrained(bzla);
      if (bzla->inconsistent)
      {
        BZLALOG(1, "formula inconsistent after skeleton preprocessing");
        break;
      }
    }

    if (bzla->varsubst_constraints->count || bzla->embedded_constraints->count)
      continue;

    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_PP_EXTRACT_LAMBDAS))
      bzla_extract_lambdas(bzla);

    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_PP_MERGE_LAMBDAS))
      bzla_merge_lambdas(bzla);

    if (bzla->varsubst_constraints->count || bzla->embedded_constraints->count)
      continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE))
    {
      bzla_eliminate_applies(bzla);
    }

    if (bzla_opt_get(bzla, BZLA_OPT_PP_ELIMINATE_ITES))
    {
      bzla_eliminate_ites(bzla);
    }

    /* add ackermann constraints for all uninterpreted functions */
    if (bzla_opt_get(bzla, BZLA_OPT_PP_ACKERMANN))
      bzla_add_ackermann_constraints(bzla);

    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_PP_NORMALIZE_ADD))
      bzla_normalize_adds(bzla);

  } while (bzla->varsubst_constraints->count
           || bzla->embedded_constraints->count);

DONE:
  delta = bzla_util_time_stamp() - start;
  bzla->time.simplify += delta;
  BZLA_MSG(bzla->msg, 1, "%u rewriting rounds in %.1f seconds", rounds, delta);

  if (bzla->inconsistent)
  {
    BZLALOG(1, "formula inconsistent");
    result = BZLA_RESULT_UNSAT;
  }
  else if (bzla->unsynthesized_constraints->count == 0u
           && bzla->synthesized_constraints->count == 0u
           && bzla->assumptions->count == 0
           && BZLA_EMPTY_STACK(bzla->assertions))
  {
    result = BZLA_RESULT_SAT;
  }
  else
  {
    result = BZLA_RESULT_UNKNOWN;
  }

  BZLA_MSG(bzla->msg, 1, "simplification returned %d", result);
  return result;
}
