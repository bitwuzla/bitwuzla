/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAGIMSATUL_H_INCLUDED
#define BZLAGIMSATUL_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_GIMSATUL
/*------------------------------------------------------------------------*/

#include "bzlasat.h"

bool bzla_sat_enable_gimsatul(BzlaSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
