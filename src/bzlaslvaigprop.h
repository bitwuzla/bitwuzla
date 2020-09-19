/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAAIGPROP_H_INCLUDED
#define BZLAAIGPROP_H_INCLUDED

#include "aigprop.h"
#include "bzlaslv.h"

#define BZLA_AIGPROP_SOLVER(bzla) ((BzlaAIGPropSolver *) (bzla)->slv)

struct BzlaAIGPropSolver
{
  BZLA_SOLVER_STRUCT;

  AIGProp *aprop;

  /* statistics */
  struct
  {
    uint32_t moves;
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
