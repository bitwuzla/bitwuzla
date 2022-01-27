/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLANODEMAP_H_INCLUDED
#define BZLANODEMAP_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashptr.h"

/*------------------------------------------------------------------------*/
/* Simple map for expression node.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'bzla_nodemap_map'.  Succesfull look-up
 * through 'bzla_nodemap_mapped' does not add a reference.  The destructor
 * releases all the owned references.  Mapping is signed, e.g. if you map
 * 'a' to 'b', then '~a' is implicitly mapped to '~b', too.
 */
struct BzlaNodeMap
{
  Bzla *bzla;  // For managing (owning) map memory
               // Otherwise src and dst can have different
               // Bitwuzla instances (even != 'bzla')!!!
  BzlaPtrHashTable *table;
};

typedef struct BzlaNodeMap BzlaNodeMap;

/*------------------------------------------------------------------------*/

BzlaNodeMap *bzla_nodemap_new(Bzla *bzla);
BzlaNode *bzla_nodemap_mapped(BzlaNodeMap *map, const BzlaNode *node);
void bzla_nodemap_map(BzlaNodeMap *map, BzlaNode *src, BzlaNode *dst);
void bzla_nodemap_delete(BzlaNodeMap *map);

/*------------------------------------------------------------------------*/
/* iterators */
/*------------------------------------------------------------------------*/

typedef struct BzlaNodeMapIterator
{
  BzlaPtrHashTableIterator it;
} BzlaNodeMapIterator;

void bzla_iter_nodemap_init(BzlaNodeMapIterator *it, const BzlaNodeMap *map);
void bzla_iter_nodemap_init_reversed(BzlaNodeMapIterator *it,
                                     const BzlaNodeMap *map);
void bzla_iter_nodemap_queue(BzlaNodeMapIterator *it, const BzlaNodeMap *map);
bool bzla_iter_nodemap_has_next(const BzlaNodeMapIterator *it);
BzlaNode *bzla_iter_nodemap_next(BzlaNodeMapIterator *it);
BzlaHashTableData *bzla_iter_nodemap_next_data(BzlaNodeMapIterator *it);

/*------------------------------------------------------------------------*/

#endif
