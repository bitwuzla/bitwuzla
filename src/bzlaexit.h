/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
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
