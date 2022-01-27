/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
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

  /* Map, maintains constant bits.
   * Maps node id to its bit-vector domain (BzlaBvDomain*). */
  BzlaIntHashTable *domains;

  /* Work stack, maintains entailed propagations that need to be processed
   * with higher priority if BZLA_OPT_PROP_ENTAILED.
   *
   * A recoverable conflict entails that starting from the node where the
   * conflict occurred there are more paths to fix (in our case exactly one
   * other path since all bv operators are binary). These so-called entailed
   * propagations are pushed onto stack 'toprop'.
   */
  BzlaPropEntailInfoStack toprop;

#ifndef NDEBUG
  BzlaPropEntailInfoStack prop_path;
#endif

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
    /* Number of restarts (if BZLA_OPT_PROP_USE_RESTARTS). */
    uint32_t restarts;
    /* Number of moves. */
    uint32_t moves;
    /* Number of moves that were a consequence of entailed propagations from
     * recoverable conflicts. */
    uint32_t moves_entailed;
    uint32_t moves_skipped;
    /* Number of recoverable conflicts.
     * A recoverable conflict is a conflict that does not involve bit-vector
     * constants. */
    uint32_t rec_conf;
    /* Number of non-recoverable conflicts.
     * A non-recoverable conflict involves bit-vector constants. */
    uint32_t non_rec_conf;
    /* Number of recoverable conflicts that were fixed. */
    uint64_t fixed_conf;
    /* Number of propagations (total). */
    uint64_t props;
    /* Number of propagations via consistent value computation. */
    uint64_t props_cons;
    /* Number of propagataions via inverse value computation. */
    uint64_t props_inv;
    /* Number of entailed propagations. */
    uint64_t props_entailed;
    /* Number of updates performed when updating the cone of influence in the
     * current assignment as a consequence of a move. */
    uint64_t updates;

    /* Number of calls to inverse value computation functions. */
    uint32_t inv_add;
    uint32_t inv_and;
    uint32_t inv_eq;
    uint32_t inv_ult;
    uint32_t inv_sll;
    uint32_t inv_slt;
    uint32_t inv_srl;
    uint32_t inv_sra;
    uint32_t inv_mul;
    uint32_t inv_udiv;
    uint32_t inv_urem;
    uint32_t inv_concat;
    uint32_t inv_slice;
    uint32_t inv_cond;
    uint32_t inv_xor;

    /* Number of calls to consistent value computation functions. */
    uint32_t cons_add;
    uint32_t cons_and;
    uint32_t cons_eq;
    uint32_t cons_ult;
    uint32_t cons_sll;
    uint32_t cons_slt;
    uint32_t cons_srl;
    uint32_t cons_sra;
    uint32_t cons_mul;
    uint32_t cons_udiv;
    uint32_t cons_urem;
    uint32_t cons_concat;
    uint32_t cons_slice;
    uint32_t cons_cond;
    uint32_t cons_xor;

    /* constant bit information */
    uint64_t fixed_bits;
    uint64_t total_bits;
    uint64_t updated_domains;
    uint64_t updated_domains_children;
  } stats;

  struct
  {
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
    double check_sat;
  } time;
};

typedef struct BzlaPropSolver BzlaPropSolver;

#define BZLA_PROP_SOLVER(bzla) ((BzlaPropSolver *) (bzla)->slv)

BzlaSolver *bzla_new_prop_solver(Bzla *bzla);

void bzla_prop_solver_init_domains(Bzla *bzla,
                                   BzlaIntHashTable *domains,
                                   BzlaNode *root);

int32_t bzla_prop_solver_sat(Bzla *bzla);
/*------------------------------------------------------------------------*/

#endif
