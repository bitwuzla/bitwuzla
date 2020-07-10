/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLACMS_H_INCLUDED
#define BZLACMS_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_CMS
/*------------------------------------------------------------------------*/

#include "bzlasat.h"

bool bzla_sat_enable_cms(BzlaSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
