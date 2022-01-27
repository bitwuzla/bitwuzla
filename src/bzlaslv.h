/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASLV_H_INCLUDED
#define BZLASLV_H_INCLUDED

#include <stdbool.h>
#include <stdio.h>

#include "bzlatypes.h"
#include "utils/bzlamem.h"
#include "utils/bzlanodemap.h"

enum BzlaSolverResult
{
  BZLA_RESULT_SAT     = 10,
  BZLA_RESULT_UNSAT   = 20,
  BZLA_RESULT_UNKNOWN = 0,
};

typedef enum BzlaSolverResult BzlaSolverResult;

enum BzlaSolverKind
{
  BZLA_FUN_SOLVER_KIND,
  BZLA_SLS_SOLVER_KIND,
  BZLA_PROP_SOLVER_KIND,
  BZLA_AIGPROP_SOLVER_KIND,
  BZLA_QUANT_SOLVER_KIND,
};
typedef enum BzlaSolverKind BzlaSolverKind;

typedef struct BzlaSolver *(*BzlaSolverClone)(Bzla *,
                                              struct BzlaSolver *,
                                              BzlaNodeMap *);
typedef void (*BzlaSolverDelete)(struct BzlaSolver *);
typedef BzlaSolverResult (*BzlaSolverSat)(struct BzlaSolver *);
typedef void (*BzlaSolverGenerateModel)(struct BzlaSolver *, bool, bool);
typedef void (*BzlaSolverPrintStats)(struct BzlaSolver *);
typedef void (*BzlaSolverPrintTimeStats)(struct BzlaSolver *);
typedef void (*BzlaSolverPrintModel)(struct BzlaSolver *,
                                     const char *format,
                                     FILE *file);

#define BZLA_SOLVER_STRUCT                       \
  struct                                         \
  {                                              \
    BzlaSolverKind kind;                         \
    Bzla *bzla;                                  \
    struct                                       \
    {                                            \
      BzlaSolverClone clone;                     \
      BzlaSolverDelete delet;                    \
      BzlaSolverSat sat;                         \
      BzlaSolverGenerateModel generate_model;    \
      BzlaSolverPrintStats print_stats;          \
      BzlaSolverPrintTimeStats print_time_stats; \
      BzlaSolverPrintModel print_model;          \
    } api;                                       \
  }

struct BzlaSolver
{
  BZLA_SOLVER_STRUCT;
};
typedef struct BzlaSolver BzlaSolver;

#endif
