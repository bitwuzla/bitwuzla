/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAMINISAT_H_INCLUDED
#define BZLAMINISAT_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_MINISAT
/*------------------------------------------------------------------------*/

#include "bzlasat.h"

bool bzla_sat_enable_minisat(BzlaSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
