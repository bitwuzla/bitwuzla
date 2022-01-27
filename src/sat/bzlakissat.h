/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAKISSAT_H_INCLUDED
#define BZLAKISSAT_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "bzlasat.h"

bool bzla_sat_enable_kissat(BzlaSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
