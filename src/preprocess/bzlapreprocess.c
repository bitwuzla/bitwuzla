/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2012-2019 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
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
  if (bzla_opt_get(bzla, BZLA_OPT_VAR_SUBST) == 0
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
    if (bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 1)
    {
      if (bzla_opt_get(bzla, BZLA_OPT_VAR_SUBST))
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

    if (bzla_opt_get(bzla, BZLA_OPT_ELIMINATE_SLICES)
        && bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 2
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
    if (bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_SKELETON_PREPROC))
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

    if (bzla_opt_get(bzla, BZLA_OPT_UCOPT)
        && bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 2
        && !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL)
        && !bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN))
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

    if (bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_EXTRACT_LAMBDAS))
      bzla_extract_lambdas(bzla);

    if (bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_MERGE_LAMBDAS))
      bzla_merge_lambdas(bzla);

    if (bzla->varsubst_constraints->count || bzla->embedded_constraints->count)
      continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (bzla_opt_get(bzla, BZLA_OPT_BETA_REDUCE))
    {
      /* If no UFs or function equalities are present, we eagerly eliminate all
       * remaining lambdas. */
      if (bzla->ufs->count == 0 && bzla->feqs->count == 0
          && !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL))
      {
        BZLA_MSG(bzla->msg,
                 1,
                 "no UFs or function equalities, enable beta-reduction=all");
        bzla_opt_set(bzla, BZLA_OPT_BETA_REDUCE, BZLA_BETA_REDUCE_ALL);
      }
      bzla_eliminate_applies(bzla);
    }

    if (bzla_opt_get(bzla, BZLA_OPT_ELIMINATE_ITES))
    {
      bzla_eliminate_ites(bzla);
    }

    /* add ackermann constraints for all uninterpreted functions */
    if (bzla_opt_get(bzla, BZLA_OPT_ACKERMANN))
      bzla_add_ackermann_constraints(bzla);

    if (bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL) > 2
        && bzla_opt_get(bzla, BZLA_OPT_SIMP_NORMAMLIZE_ADDERS))
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
           && bzla->synthesized_constraints->count == 0u)
    result = BZLA_RESULT_SAT;
  else
    result = BZLA_RESULT_UNKNOWN;

  BZLA_MSG(bzla->msg, 1, "simplification returned %d", result);
  return result;
}
