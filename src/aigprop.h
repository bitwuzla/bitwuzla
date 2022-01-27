/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLA_AIGPROP_H_INCLUDED
#define BZLA_AIGPROP_H_INCLUDED

#include "bzlaaig.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlarng.h"

#define BZLA_AIGPROP_UNKNOWN 0
#define BZLA_AIGPROP_SAT 10
#define BZLA_AIGPROP_UNSAT 20

struct BzlaAIGProp
{
  BzlaAIGMgr *amgr;
  BzlaIntHashTable *roots;
  BzlaIntHashTable *unsatroots;
  BzlaIntHashTable *score;
  BzlaIntHashTable *model;
  BzlaIntHashTable *parents;
  BzlaMemMgr *mm;

  BzlaRNG *rng;

  uint32_t loglevel;
  uint32_t seed;
  uint32_t use_restarts;
  uint32_t use_bandit;
  uint64_t nprops;

  struct
  {
    uint32_t moves;
    uint64_t props;
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

typedef struct BzlaAIGProp BzlaAIGProp;

BzlaAIGProp *bzla_aigprop_new_aigprop(BzlaAIGMgr *amgr,
                                      uint32_t loglevel,
                                      uint32_t seed,
                                      uint32_t use_restarts,
                                      uint32_t use_bandit,
                                      uint64_t nprops);

BzlaAIGProp *bzla_aigprop_clone_aigprop(BzlaAIGMgr *clone, BzlaAIGProp *aprop);
void bzla_aigprop_delete_aigprop(BzlaAIGProp *aprop);

int32_t bzla_aigprop_get_assignment_aig(BzlaAIGProp *aprop, BzlaAIG *aig);
void bzla_aigprop_generate_model(BzlaAIGProp *aprop, bool reset);

int32_t bzla_aigprop_sat(BzlaAIGProp *aprop, BzlaIntHashTable *roots);

#if 0
void bzla_aigprop_print_stats (BzlaAIGProp * aprop);
void bzla_aigprop_print_time_stats (BzlaAIGProp * aprop);
#endif

#endif
