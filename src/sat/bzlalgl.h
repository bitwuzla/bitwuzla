/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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
