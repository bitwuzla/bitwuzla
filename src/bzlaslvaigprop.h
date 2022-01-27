/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAAIGPROP_H_INCLUDED
#define BZLAAIGPROP_H_INCLUDED

#include "aigprop.h"
#include "bzlaslv.h"

#define BZLA_AIGPROP_SOLVER(bzla) ((BzlaAIGPropSolver *) (bzla)->slv)

struct BzlaAIGPropSolver
{
  BZLA_SOLVER_STRUCT;

  BzlaAIGProp *aprop;

  /* statistics */
  struct
  {
    uint32_t moves;
    uint64_t props;
    uint32_t restarts;
  } stats;
  struct
  {
    double aprop_sat;
    double aprop_update_cone;
    double aprop_update_cone_reset;
    double aprop_update_cone_model_gen;
    double aprop_update_cone_compute_score;
  } time;
};

typedef struct BzlaAIGPropSolver BzlaAIGPropSolver;

BzlaSolver *bzla_new_aigprop_solver(Bzla *bzla);

#endif
