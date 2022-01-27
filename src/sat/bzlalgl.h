/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASATLGL_H_INCLUDED
#define BZLASATLGL_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_LINGELING
/*------------------------------------------------------------------------*/

#include "bzlasat.h"
#include "lglib.h"

typedef struct BzlaLGL BzlaLGL;

struct BzlaLGL
{
  LGL* lgl;
  int32_t nforked, blimit;
};

bool bzla_sat_enable_lingeling(BzlaSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
