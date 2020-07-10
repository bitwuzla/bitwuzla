/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLACADICAL_H_INCLUDED
#define BZLACADICAL_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*------------------------------------------------------------------------*/

#include "bzlasat.h"

bool bzla_sat_enable_cadical(BzlaSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
