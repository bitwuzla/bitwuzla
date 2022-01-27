/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
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
