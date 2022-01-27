/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLA_INT_HASH_H_INCLUDED
#define BZLA_INT_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "utils/bzlahash.h"
#include "utils/bzlamem.h"

/*----------------------------------------------------------------------------*/

struct BzlaIntHashTable
{
  BzlaMemMgr *mm;
  size_t count;
  size_t size;
  int32_t *keys;
  uint8_t *hop_info; /** displacement information */
  BzlaHashTableData *data;
};

typedef struct BzlaIntHashTable BzlaIntHashTable;

/*----------------------------------------------------------------------------*/
/* hash table                                                                 */
/*----------------------------------------------------------------------------*/

/** Create new int hash table. */
BzlaIntHashTable *bzla_hashint_table_new(BzlaMemMgr *mm);

/** Free int hash table. */
void bzla_hashint_table_delete(BzlaIntHashTable *t);

/** Returns the size of the BzlaIntHashTable in Byte. */
size_t bzla_hashint_table_size(BzlaIntHashTable *t);

/**
 * Add 'key' to the hash table and return the position at which 'key' is
 * stored in the keys array.
 */
size_t bzla_hashint_table_add(BzlaIntHashTable *t, int32_t key);

/** Check whether 'key' is in the hash table. */
bool bzla_hashint_table_contains(BzlaIntHashTable *t, int32_t key);

/**
 * Remove all entries of the hash table.
 *
 * The hash table retains its size, no (re)allocation of memory is performed,
 * keys and hop_info are cleared (set to 0).
 */
void bzla_hashint_table_clear(BzlaIntHashTable *t);

/**
 * Remove 'key' from the hash table and return the position at which 'key'
 * was stored in the keys array.
 */
size_t bzla_hashint_table_remove(BzlaIntHashTable *t, int32_t key);

/**
 * Returns the position at which 'key' is stored in the keys array. It returns
 * 'size' of the hash table if 'key' could not be found.
 */
size_t bzla_hashint_table_get_pos(BzlaIntHashTable *t, int32_t key);

/** Clone int hash table. */
BzlaIntHashTable *bzla_hashint_table_clone(BzlaMemMgr *mm,
                                           BzlaIntHashTable *table);

/*----------------------------------------------------------------------------*/
/* hash map                                                                   */
/*----------------------------------------------------------------------------*/

/** Create new int32_t hash map. */
BzlaIntHashTable *bzla_hashint_map_new(BzlaMemMgr *t);

/** Free int32_t hash map. */
void bzla_hashint_map_delete(BzlaIntHashTable *t);

/** Check whether 'key' is in the hash map. */
bool bzla_hashint_map_contains(BzlaIntHashTable *t, int32_t key);

/**
 * Remove 'key' from the hash map and store mapped data in 'stored_data' if
 * 'stored_data' is not null.
 */
void bzla_hashint_map_remove(BzlaIntHashTable *t,
                             int32_t key,
                             BzlaHashTableData *stored_data);

/** Add 'key' to the hash map and return mapped data.  */
BzlaHashTableData *bzla_hashint_map_add(BzlaIntHashTable *t, int32_t key);
/** Get mapped data at 'key'.  */
BzlaHashTableData *bzla_hashint_map_get(BzlaIntHashTable *t, int32_t key);

/**
 * Remove all entries of the hash map.
 *
 * The hash map retains its size, no (re)allocation of memory is performed,
 * keys, hop_info and mapped data are cleared (set to 0).
 */
void bzla_hashint_map_clear(BzlaIntHashTable *t);

/**
 * Clone int hash map.
 *
 * mm      : The memory manager of the clone.
 * table   : The int hash map to clone.
 * cdata   : The function for cloning the mapped data.
 * data_map: The (optional) map for cloning the mapped data (maps data items
 *           to be cloned to cloned data items, e.g., expressions).
 *
 * Returns the cloned int hash map.
 */
BzlaIntHashTable *bzla_hashint_map_clone(BzlaMemMgr *mm,
                                         BzlaIntHashTable *table,
                                         BzlaCloneHashTableData cdata,
                                         const void *data_map);

/*----------------------------------------------------------------------------*/
/* iterators                                                                  */
/*----------------------------------------------------------------------------*/

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

/*----------------------------------------------------------------------------*/

#endif
