/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */
#ifndef BZLAAIGMAP_H_INCLUDED
#define BZLAAIGMAP_H_INCLUDED

/*------------------------------------------------------------------------*/

#include "boolector.h"
#include "bzlaaig.h"

/*------------------------------------------------------------------------*/

/* Simple map for AIG node.  Same reference counting and signed/tagged
 * behavior as BzlaNodeMap.
 */
struct BzlaAIGMap
{
  Bzla *bzla;           /* managing (owning) map internals */
  BzlaAIGMgr *amgr_src; /* managing (owning) source aigs */
  BzlaAIGMgr *amgr_dst; /* managing (owning) destination aigs */
  BzlaPtrHashTable *table;
};

typedef struct BzlaAIGMap BzlaAIGMap;

/*------------------------------------------------------------------------*/

BzlaAIGMap *bzla_aigmap_new(Bzla *, BzlaAIGMgr *, BzlaAIGMgr *);
BzlaAIG *bzla_aigmap_mapped(BzlaAIGMap *, BzlaAIG *);
void bzla_aigmap_map(BzlaAIGMap *, BzlaAIG *src, BzlaAIG *dst);
void bzla_aigmap_delete(BzlaAIGMap *);

/*------------------------------------------------------------------------*/

#endif
