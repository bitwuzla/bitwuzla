/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASLVSLS_H_INCLUDED
#define BZLASLVSLS_H_INCLUDED

#include "utils/bzlanodemap.h"
#ifndef NDEBUG
#include "bzlabv.h"
#endif

#include "bzlaslv.h"
#include "utils/bzlahashint.h"
#include "utils/bzlastack.h"

enum BzlaSLSMoveKind
{
  BZLA_SLS_MOVE_FLIP = 0,
  BZLA_SLS_MOVE_INC,
  BZLA_SLS_MOVE_DEC,
  BZLA_SLS_MOVE_NOT,
  BZLA_SLS_MOVE_FLIP_RANGE,
  BZLA_SLS_MOVE_FLIP_SEGMENT,
  BZLA_SLS_MOVE_DONE,
  BZLA_SLS_MOVE_RAND,
  BZLA_SLS_MOVE_RAND_WALK,
  BZLA_SLS_MOVE_PROP,
};
typedef enum BzlaSLSMoveKind BzlaSLSMoveKind;

struct BzlaSLSMove
{
  BzlaIntHashTable *cans;
  double sc;
};
typedef struct BzlaSLSMove BzlaSLSMove;

struct BzlaSLSConstrData
{
  int64_t weight;
  int64_t selected;
};
typedef struct BzlaSLSConstrData BzlaSLSConstrData;

BZLA_DECLARE_STACK(BzlaSLSMovePtr, BzlaSLSMove *);

/*------------------------------------------------------------------------*/

#define BZLA_SLS_SOLVER(bzla) ((BzlaSLSSolver *) (bzla)->slv)

struct BzlaSLSSolver
{
  BZLA_SOLVER_STRUCT;

  BzlaIntHashTable *roots;   /* must be map (for common local search funs)
                                but does not maintain anything */
  BzlaIntHashTable *weights; /* also maintains assertion weights */
  BzlaIntHashTable *score;   /* sls score */

  /* Map, maintains constant bits.
   * Maps node id to its bit-vector domain (BzlaBvDomain*). Only used by by
   * the propagation-based strategy if BZLA_OPT_PROP_CONST_BITS is enabled. */
  BzlaIntHashTable *domains;

  uint32_t nflips; /* limit, disabled if 0 */
  bool terminate;

  BzlaSLSMovePtrStack moves; /* record moves for prob rand walk */
  uint32_t npropmoves;       /* record #no moves for prop moves */
  uint32_t nslsmoves;        /* record #no moves for sls moves */
  double sum_score;          /* record sum of all scores for prob rand walk */

  /* prop moves only */
  uint32_t prop_flip_cond_const_prob;
  int32_t prop_flip_cond_const_prob_delta;
  uint32_t prop_nflip_cond_const;

  /* the following maintain data for the next move (i.e. either the move
   * with the maximum score of all tried moves, or a random walk, or a
   * randomized move). */
  BzlaIntHashTable *max_cans; /* list of (can, neigh) */
  double max_score;
  BzlaSLSMoveKind max_move; /* move kind (for stats) */
  int32_t max_gw;           /* is groupwise move? (for stats) */

  /* statistics */
  struct
  {
    uint32_t restarts;
    uint32_t moves;
    uint32_t flips;
    uint32_t props;
    uint32_t move_flip;
    uint32_t move_inc;
    uint32_t move_dec;
    uint32_t move_not;
    uint32_t move_range;
    uint32_t move_seg;
    uint32_t move_rand;
    uint32_t move_rand_walk;
    uint32_t move_prop;
    uint32_t move_prop_rec_conf;
    uint32_t move_prop_non_rec_conf;
    uint32_t move_gw_flip;
    uint32_t move_gw_inc;
    uint32_t move_gw_dec;
    uint32_t move_gw_not;
    uint32_t move_gw_range;
    uint32_t move_gw_seg;
    uint32_t move_gw_rand;
    uint32_t move_gw_rand_walk;
    uint64_t updates;
  } stats;

  struct
  {
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BzlaSLSSolver BzlaSLSSolver;

BzlaSolver *bzla_new_sls_solver(Bzla *bzla);

#endif
