/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef AIGPROP_H_INCLUDED
#define AIGPROP_H_INCLUDED

#include "bzlaaig.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlarng.h"

#define AIGPROP_UNKNOWN 0
#define AIGPROP_SAT 10
#define AIGPROP_UNSAT 20

struct AIGProp
{
  BzlaAIGMgr *amgr;
  BzlaIntHashTable *roots;
  BzlaIntHashTable *unsatroots;
  BzlaIntHashTable *score;
  BzlaIntHashTable *model;
  BzlaIntHashTable *parents;

  BzlaRNG rng;

  uint32_t loglevel;
  uint32_t seed;
  uint32_t use_restarts;
  uint32_t use_bandit;

  struct
  {
    uint32_t moves;
    uint32_t restarts;
  } stats;

  struct
  {
    double sat;
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct AIGProp AIGProp;

AIGProp *aigprop_new_aigprop(BzlaAIGMgr *amgr,
                             uint32_t loglevel,
                             uint32_t seed,
                             uint32_t use_restarts,
                             uint32_t use_bandit);

AIGProp *aigprop_clone_aigprop(BzlaAIGMgr *clone, AIGProp *aprop);
void aigprop_delete_aigprop(AIGProp *aprop);

int32_t aigprop_get_assignment_aig(AIGProp *aprop, BzlaAIG *aig);
void aigprop_generate_model(AIGProp *aprop, bool reset);

int32_t aigprop_sat(AIGProp *aprop, BzlaIntHashTable *roots);

#if 0
void aigprop_print_stats (AIGProp * aprop);
void aigprop_print_time_stats (AIGProp * aprop);
#endif

#endif
