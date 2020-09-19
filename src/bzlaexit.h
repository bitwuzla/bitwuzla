/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BZLAEXIT_H_INCLUDED
#define BZLAEXIT_H_INCLUDED

enum BzlaExitCode
{
  BZLA_SUCC_EXIT    = 0,
  BZLA_ERR_EXIT     = 1,
  BZLA_SAT_EXIT     = 10,
  BZLA_UNSAT_EXIT   = 20,
  BZLA_UNKNOWN_EXIT = 0
};

typedef enum BzlaExitCode BzlaExitCode;

#endif
