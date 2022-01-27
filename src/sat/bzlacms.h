/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
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
