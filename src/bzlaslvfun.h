/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASLVFUN_H_INCLUDED
#define BZLASLVFUN_H_INCLUDED

#include "bzlanode.h"
#include "bzlaslv.h"
#include "utils/bzlahashptr.h"

#define BZLA_FUN_SOLVER(bzla) ((BzlaFunSolver *) (bzla)->slv)

struct BzlaFunSolver
{
  BZLA_SOLVER_STRUCT;

  BzlaPtrHashTable *lemmas;
  BzlaNodePtrStack cur_lemmas;
  BzlaNodePtrStack constraints;

  BzlaPtrHashTable *score; /* dcr score */

  // TODO (ma): make options for these
  int32_t lod_limit;
  int32_t sat_limit;
  bool assume_lemmas;

  struct
  {
    uint32_t lod_refinements; /* number of lemmas on demand refinements */
    uint32_t refinement_iterations;

    uint32_t function_congruence_conflicts;
    uint32_t beta_reduction_conflicts;
    uint32_t extensionality_lemmas;

    BzlaUIntStack lemmas_size;      /* distribution of n-size lemmas */
    uint_least64_t lemmas_size_sum; /* sum of the size of all added lemmas */

    uint32_t dp_failed_vars; /* number of vars in FA (dual prop) of last
                                sat call (final bv skeleton) */
    uint32_t dp_assumed_vars;
    uint32_t dp_failed_applies; /* number of applies in FA (dual prop) of last
                                   sat call (final bv skeleton) */
    uint32_t dp_assumed_applies;
    uint32_t dp_failed_eqs;
    uint32_t dp_assumed_eqs;

    /* number of assignments shared from local search engine */
    uint32_t prels_shared;

    uint_least64_t eval_exp_calls;
    uint_least64_t propagations;
    uint_least64_t propagations_down;
  } stats;

  struct
  {
    double sat;
    double eval;
    double search_init_apps;
    double search_init_apps_compute_scores;
    double search_init_apps_compute_scores_merge_applies;
    double search_init_apps_cloning;
    double search_init_apps_sat;
    double search_init_apps_collect_var_apps;
    double search_init_apps_collect_fa;
    double search_init_apps_collect_fa_cone;
    double lemma_gen;
    double find_prop_app;
    double check_consistency;
    double prop;
    double betap;
    double find_conf_app;
    double check_extensionality;
    double prop_cleanup;
    double prels_sat;
  } time;
};

typedef struct BzlaFunSolver BzlaFunSolver;

BzlaSolver *bzla_new_fun_solver(Bzla *bzla);

// TODO (ma): this is just a fix for now, this should be moved elsewhere
/* Evaluates expression and returns its value. */
BzlaBitVector *bzla_eval_exp(Bzla *bzla, BzlaNode *exp);
#endif
