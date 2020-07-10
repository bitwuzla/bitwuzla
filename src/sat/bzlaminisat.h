/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2012 Armin Biere.
 *  Copyright (C) 2017 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
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
