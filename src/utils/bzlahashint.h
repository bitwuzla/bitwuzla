/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLA_INT_HASH_H_INCLUDED
#define BZLA_INT_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "utils/bzlahash.h"
#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

struct BzlaIntHashTable
{
  BzlaMemMgr *mm;
  size_t count;
  size_t size;
  int32_t *keys;
  uint8_t *hop_info; /* displacement information */
  BzlaHashTableData *data;
};

typedef struct BzlaIntHashTable BzlaIntHashTable;

/*------------------------------------------------------------------------*/
/* hash table                                                             */
/*------------------------------------------------------------------------*/

/* Create new int32_t hash table. */
BzlaIntHashTable *bzla_hashint_table_new(BzlaMemMgr *);

/* Free int32_t hash table. */
void bzla_hashint_table_delete(BzlaIntHashTable *);

/* Returns the size of the BzlaIntHashTable in Byte. */
size_t bzla_hashint_table_size(BzlaIntHashTable *);

/* Add 'key' to the hash table and return the position at which 'key' is
 * stored in the keys array. */
size_t bzla_hashint_table_add(BzlaIntHashTable *, int32_t key);

/* Check whether 'key' is in the hash table. */
bool bzla_hashint_table_contains(BzlaIntHashTable *, int32_t key);

/* Remove 'key' from the hash table and return the position at which 'key'
 * was stored in the keys array. */
size_t bzla_hashint_table_remove(BzlaIntHashTable *, int32_t key);

/* Returns the position at which 'key' is stored in the keys array. It returns
 * 'size' of the hash table if 'key' could not be found. */
// TODO (ma): remove
size_t bzla_hashint_table_get_pos(BzlaIntHashTable *, int32_t key);

BzlaIntHashTable *bzla_hashint_table_clone(BzlaMemMgr *mm,
                                           BzlaIntHashTable *table);

/*------------------------------------------------------------------------*/
/* hash map                                                               */
/*------------------------------------------------------------------------*/

BzlaIntHashTable *bzla_hashint_map_new(BzlaMemMgr *);

bool bzla_hashint_map_contains(BzlaIntHashTable *, int32_t key);

void bzla_hashint_map_remove(BzlaIntHashTable *,
                             int32_t key,
                             BzlaHashTableData *stored_data);

BzlaHashTableData *bzla_hashint_map_add(BzlaIntHashTable *, int32_t key);
BzlaHashTableData *bzla_hashint_map_get(BzlaIntHashTable *, int32_t key);

void bzla_hashint_map_delete(BzlaIntHashTable *);

BzlaIntHashTable *bzla_hashint_map_clone(BzlaMemMgr *mm,
                                         BzlaIntHashTable *table,
                                         BzlaCloneHashTableData cdata,
                                         const void *data_map);

/*------------------------------------------------------------------------*/
/* iterators                                                              */
/*------------------------------------------------------------------------*/

typedef struct BzlaIntHashTableIterator
{
  size_t cur_pos;
  const BzlaIntHashTable *t;
} BzlaIntHashTableIterator;

void bzla_iter_hashint_init(BzlaIntHashTableIterator *it,
                            const BzlaIntHashTable *t);

bool bzla_iter_hashint_has_next(const BzlaIntHashTableIterator *it);

int32_t bzla_iter_hashint_next(BzlaIntHashTableIterator *it);

BzlaHashTableData *bzla_iter_hashint_next_data(BzlaIntHashTableIterator *it);

/*------------------------------------------------------------------------*/

#endif
