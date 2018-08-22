/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLASLVPROP_H_INCLUDED
#define BZLASLVPROP_H_INCLUDED

#include "bzlabv.h"
#include "bzlaproputils.h"
#include "bzlaslv.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"

struct BzlaPropSolver
{
  BZLA_SOLVER_STRUCT;

  /* Map, maintains the roots.
   * Maps root to 'selected' (= how often it got selected) */
  BzlaIntHashTable *roots;

  /* Map, maintains SLS score.
   * Maps node to its SLS score, only used for heuristically selecting
   * a root r based on maximizing
   *   score(r) + BZLA_PROP_SELECT_CFACT * sqrt (log (selected(r)) / nmoves)
   * if BZLA_OPT_PROP_USE_BANDIT is enabled. */
  BzlaIntHashTable *score;

  /* Work stack, maintains entailed propagations. */
  BzlaPropInfoStack toprop;

  /* current probability for selecting the cond when either the
   * 'then' or 'else' branch is const (path selection) */
  uint32_t flip_cond_const_prob;
  /* current delta for updating the probability for selecting the cond
   * when either the 'then' or 'else' branch is const (path selection) */
  int32_t flip_cond_const_prob_delta;
  /* number of times the cond has already been selected when either
   * the 'then' or 'else' branch is const */
  uint32_t nflip_cond_const;

  struct
  {
    uint32_t restarts;
    uint32_t moves;
    uint32_t rec_conf;
    uint32_t non_rec_conf;
    uint64_t props;
    uint64_t props_cons;
    uint64_t props_inv;
    uint64_t updates;

#ifndef NDEBUG
    uint32_t inv_add;
    uint32_t inv_and;
    uint32_t inv_eq;
    uint32_t inv_ult;
    uint32_t inv_sll;
    uint32_t inv_srl;
    uint32_t inv_mul;
    uint32_t inv_udiv;
    uint32_t inv_urem;
    uint32_t inv_concat;
    uint32_t inv_slice;
    uint32_t inv_cond;

    uint32_t cons_add;
    uint32_t cons_and;
    uint32_t cons_eq;
    uint32_t cons_ult;
    uint32_t cons_sll;
    uint32_t cons_srl;
    uint32_t cons_mul;
    uint32_t cons_udiv;
    uint32_t cons_urem;
    uint32_t cons_concat;
    uint32_t cons_slice;
    uint32_t cons_cond;
#endif
  } stats;

  struct
  {
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BzlaPropSolver BzlaPropSolver;

#define BZLA_PROP_SOLVER(bzla) ((BzlaPropSolver *) (bzla)->slv)

BzlaSolver *bzla_new_prop_solver(Bzla *bzla);

/*------------------------------------------------------------------------*/

#endif
